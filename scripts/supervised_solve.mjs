#!/usr/bin/env node
/**
 * External two-process resource supervisor for LDProver (`tprover`).
 *
 * Enforces end-to-end monotonic wall-clock deadline (`--total-time-ms`),
 * cooperative search soft deadline (`--search-soft-ms`), and memory budget
 * (`--memory-limit-bytes`, `--solver-memory-bytes`) serially across:
 *   Stage 1: `tprover solve` -> isolated temp staging directory
 *   Stage 2: `tprover check --original-root` -> independent verification
 *   Stage 3: atomic publish to `--out-proof` ONLY on verified PASS within
 *            deadline, memory limit, and complete metering
 *
 * On Linux with `--cgroup-dir <path>`, validates that the supervisor itself
 * is already running inside a dedicated memory-limited, zero-swap cgroup v2
 * (so all child workers inherit membership at spawn) and checks `memory.max`,
 * `memory.swap.max`, `memory.current`, `memory.peak`, and `memory.events`.
 * On macOS/other POSIX without Linux cgroup v2, uses `/usr/bin/time -l`
 * (kernel ru_maxrss) plus process-group `ps` polling (advisory only;
 * `budgetCertified` remains false).
 */

import crypto from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { execFileSync, spawn } from "node:child_process";
import { pathToFileURL } from "node:url";

function parsePositiveInt(raw, flagName) {
  const n = Number(raw);
  if (!Number.isInteger(n) || n <= 0) {
    throw new Error(`Invalid positive integer for ${flagName}: ${raw}`);
  }
  return n;
}

function parseNonNegativeInt(raw, flagName) {
  const n = Number(raw);
  if (!Number.isInteger(n) || n < 0) {
    throw new Error(`Invalid non-negative integer for ${flagName}: ${raw}`);
  }
  return n;
}

function parseCliArgs(argv) {
  const opts = {
    tproverBin: "",
    problemPath: "",
    outProofPath: "",
    outReceiptPath: "",
    totalTimeMs: 600000,
    searchSoftMs: 480000,
    memoryLimitBytes: 2000000000,
    solverMemoryBytes: 0,
    nodeLimit: 100000000,
    maxDepth: 64,
    cgroupDir: "",
    faultCheckDelayMs: 0,
    faultPublishDelayMs: 0,
    faultPostPublishDelayMs: 0,
    faultTamperStaging: false,
  };
  for (let i = 0; i < argv.length; ++i) {
    const a = argv[i];
    if (a === "--tprover" && i + 1 < argv.length) {
      opts.tproverBin = argv[++i];
    } else if (a === "--problem" && i + 1 < argv.length) {
      opts.problemPath = argv[++i];
    } else if (a === "--out-proof" && i + 1 < argv.length) {
      opts.outProofPath = argv[++i];
    } else if (a === "--out-receipt" && i + 1 < argv.length) {
      opts.outReceiptPath = argv[++i];
    } else if (a === "--total-time-ms" && i + 1 < argv.length) {
      opts.totalTimeMs = parsePositiveInt(argv[++i], "--total-time-ms");
    } else if (a === "--search-soft-ms" && i + 1 < argv.length) {
      opts.searchSoftMs = parsePositiveInt(argv[++i], "--search-soft-ms");
    } else if (a === "--memory-limit-bytes" && i + 1 < argv.length) {
      opts.memoryLimitBytes = parsePositiveInt(
        argv[++i],
        "--memory-limit-bytes"
      );
    } else if (a === "--solver-memory-bytes" && i + 1 < argv.length) {
      opts.solverMemoryBytes = parsePositiveInt(
        argv[++i],
        "--solver-memory-bytes"
      );
    } else if (a === "--node-limit" && i + 1 < argv.length) {
      opts.nodeLimit = parsePositiveInt(argv[++i], "--node-limit");
    } else if (a === "--max-depth" && i + 1 < argv.length) {
      opts.maxDepth = parsePositiveInt(argv[++i], "--max-depth");
    } else if (a === "--cgroup-dir" && i + 1 < argv.length) {
      opts.cgroupDir = argv[++i];
    } else if (a === "--fault-check-delay-ms" && i + 1 < argv.length) {
      opts.faultCheckDelayMs = parseNonNegativeInt(
        argv[++i],
        "--fault-check-delay-ms"
      );
    } else if (a === "--fault-publish-delay-ms" && i + 1 < argv.length) {
      opts.faultPublishDelayMs = parseNonNegativeInt(
        argv[++i],
        "--fault-publish-delay-ms"
      );
    } else if (a === "--fault-post-publish-delay-ms" && i + 1 < argv.length) {
      opts.faultPostPublishDelayMs = parseNonNegativeInt(
        argv[++i],
        "--fault-post-publish-delay-ms"
      );
    } else if (a === "--fault-tamper-staging") {
      opts.faultTamperStaging = true;
    } else {
      throw new Error(`Unknown or incomplete option: ${a}`);
    }
  }
  if (!opts.tproverBin || !opts.problemPath) {
    throw new Error(
      "Usage: supervised_solve.mjs --tprover <bin> --problem <file.json> [options]"
    );
  }
  if (opts.solverMemoryBytes === 0) {
    opts.solverMemoryBytes = Math.max(
      1,
      Math.floor(opts.memoryLimitBytes * 0.85)
    );
  }
  return opts;
}

function sha256FileHex(filePath) {
  const hash = crypto.createHash("sha256");
  const buf = Buffer.allocUnsafe(65536);
  const fd = fs.openSync(filePath, "r");
  try {
    let bytesRead = 0;
    while ((bytesRead = fs.readSync(fd, buf, 0, buf.length, null)) > 0) {
      hash.update(bytesRead === buf.length ? buf : buf.subarray(0, bytesRead));
    }
  } finally {
    fs.closeSync(fd);
  }
  return hash.digest("hex");
}

function safeStat(filePath) {
  try {
    return fs.statSync(filePath);
  } catch {
    return null;
  }
}

function safeLstat(filePath) {
  try {
    return fs.lstatSync(filePath);
  } catch {
    return null;
  }
}

function canonicalizePathPreservingLeaf(inputPath, seen = new Set()) {
  let abs = path.resolve(inputPath);
  for (let depth = 0; depth < 40; ++depth) {
    if (seen.has(abs)) {
      throw new Error(`Symlink cycle while resolving path: ${inputPath}`);
    }
    seen.add(abs);
    const tail = [];
    let cur = abs;
    while (cur !== path.dirname(cur) && !safeLstat(cur)) {
      tail.unshift(path.basename(cur));
      cur = path.dirname(cur);
    }
    const realAncestor = safeLstat(cur) ? fs.realpathSync(cur) : cur;
    const combined = tail.length > 0 ? path.join(realAncestor, ...tail) : realAncestor;
    const lst = safeLstat(combined);
    if (lst && lst.isSymbolicLink()) {
      const linkTarget = fs.readlinkSync(combined);
      abs = path.resolve(path.dirname(combined), linkTarget);
      continue;
    }
    return combined;
  }
  throw new Error(`Too many symlink levels while resolving path: ${inputPath}`);
}

function ensureDirWithRollbackTracking(dirPath) {
  const missing = [];
  let cur = path.resolve(dirPath);
  while (cur !== path.dirname(cur) && !fs.existsSync(cur)) {
    missing.unshift(cur);
    cur = path.dirname(cur);
  }
  if (missing.length > 0) {
    fs.mkdirSync(dirPath, { recursive: true });
  }
  return missing;
}

function cleanupCreatedDirs(dirs) {
  for (let i = dirs.length - 1; i >= 0; --i) {
    try {
      fs.rmdirSync(dirs[i]);
    } catch {
      // Stop if non-empty or removed concurrently.
    }
  }
}

function sameFileIdentity(statA, statB) {
  if (!statA || !statB) return false;
  return statA.dev === statB.dev && statA.ino === statB.ino;
}

export function validateOutputPathIdentities({
  problemPath,
  outProofPath,
  outReceiptPath,
}) {
  const probStat = safeStat(problemPath);
  if (!probStat || !probStat.isFile()) {
    throw new Error(`--problem does not exist as a regular file: ${problemPath}`);
  }

  const slots = [{ role: "problem", raw: problemPath }];
  if (outProofPath) slots.push({ role: "out-proof", raw: outProofPath });
  if (outReceiptPath) slots.push({ role: "out-receipt", raw: outReceiptPath });

  for (const s of slots) {
    if (s.role === "problem") continue;
    const st = safeStat(s.raw);
    if (st && st.isDirectory()) {
      throw new Error(`--${s.role} points to an existing directory: ${s.raw}`);
    }
  }

  const resolved = slots.map((s) => ({
    role: s.role,
    raw: s.raw,
    canonical: canonicalizePathPreservingLeaf(s.raw),
    stat: safeStat(s.raw),
    lstat: safeLstat(s.raw),
  }));

  for (let i = 0; i < resolved.length; ++i) {
    for (let j = i + 1; j < resolved.length; ++j) {
      const a = resolved[i];
      const b = resolved[j];
      if (a.canonical === b.canonical) {
        throw new Error(
          `Path alias conflict: --${a.role} and --${b.role} resolve to the same target (${a.canonical})`
        );
      }
      if (sameFileIdentity(a.stat, b.stat)) {
        throw new Error(
          `File identity conflict: --${a.role} and --${b.role} refer to the same inode (${a.stat.dev}:${a.stat.ino})`
        );
      }
    }
  }

  // If both --out-proof and --out-receipt are specified and neither exists yet
  // (nor via existing case/Unicode alias), atomically probe with an exclusive
  // zero-byte file to catch brand-new case-insensitive / NFC-NFD collisions.
  const proofSlot = resolved.find((s) => s.role === "out-proof");
  const receiptSlot = resolved.find((s) => s.role === "out-receipt");
  if (proofSlot && receiptSlot && !proofSlot.lstat && !receiptSlot.lstat) {
    const absProof = path.resolve(proofSlot.raw);
    const parentDir = path.dirname(absProof);
    const createdDirs = ensureDirWithRollbackTracking(parentDir);
    let fd = null;
    try {
      fd = fs.openSync(absProof, "wx", 0o600);
      const probeStat = fs.fstatSync(fd);
      const receiptStat = safeStat(receiptSlot.raw);
      if (sameFileIdentity(probeStat, receiptStat)) {
        throw new Error(
          `Filesystem collision conflict: --out-proof and --out-receipt map to the same directory entry (${absProof})`
        );
      }
    } finally {
      if (fd !== null) {
        try {
          fs.closeSync(fd);
        } catch {
          // Ignore close error.
        }
        try {
          fs.unlinkSync(absProof);
        } catch {
          // Ignore unlink error.
        }
      }
      cleanupCreatedDirs(createdDirs);
    }
  }
}

export function listProcessGroupMembers(pgid) {
  if (!Number.isInteger(pgid) || pgid <= 0) {
    throw new Error(`Invalid pgid for process-group inspection: ${pgid}`);
  }
  const psArgs =
    process.platform === "darwin"
      ? ["-axo", "pid=,pgid=,rss=,comm="]
      : ["-eo", "pid=,pgid=,rss=,comm="];
  const out = execFileSync("ps", psArgs, {
    encoding: "utf8",
    stdio: ["ignore", "pipe", "pipe"],
  });
  const members = [];
  let totalRssBytes = 0;
  for (const line of out.split(/\r?\n/)) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    const m = trimmed.match(/^(\d+)\s+(\d+)\s+(\d+)\s+(.+)$/);
    if (!m) continue;
    const pid = Number(m[1]);
    const pgrp = Number(m[2]);
    const rssKb = Number(m[3]);
    const comm = m[4];
    if (
      (pid === pgid || pgrp === pgid) &&
      Number.isFinite(rssKb) &&
      rssKb >= 0
    ) {
      const rssBytes = rssKb * 1024;
      members.push({ pid, pgid: pgrp, rssBytes, comm });
      totalRssBytes += rssBytes;
    }
  }
  return { members, totalRssBytes };
}

function readCgroupIntFile(filePath, { allowZero = true } = {}) {
  if (!fs.existsSync(filePath)) {
    return { ok: false, reason: "missing", raw: null, value: null };
  }
  const raw = fs.readFileSync(filePath, "utf8").trim();
  if (!/^\d+$/.test(raw)) {
    return { ok: false, reason: "non_integer", raw, value: null };
  }
  const value = Number(raw);
  if (!Number.isSafeInteger(value) || value < 0 || (!allowZero && value === 0)) {
    return { ok: false, reason: "out_of_range", raw, value: null };
  }
  return { ok: true, reason: "ok", raw, value };
}

export function readCgroupV2Snapshot(cgroupDir) {
  if (!cgroupDir) return null;
  try {
    const curRes = readCgroupIntFile(path.join(cgroupDir, "memory.current"));
    if (!curRes.ok) {
      return { ok: false, error: `memory.current_${curRes.reason}` };
    }
    const peakRes = readCgroupIntFile(path.join(cgroupDir, "memory.peak"));
    if (!peakRes.ok) {
      return { ok: false, error: `memory.peak_${peakRes.reason}` };
    }
    const eventsPath = path.join(cgroupDir, "memory.events");
    if (!fs.existsSync(eventsPath)) {
      return { ok: false, error: "memory.events_missing" };
    }
    const txt = fs.readFileSync(eventsPath, "utf8");
    let sawOomCount = 0;
    let sawOomKillCount = 0;
    let oomCount = null;
    let oomKillCount = null;
    for (const line of txt.split(/\r?\n/)) {
      const trimmed = line.trim();
      if (!trimmed) continue;
      const m = trimmed.match(/^(oom|oom_kill)\s+(\S+)$/);
      if (m) {
        if (!/^\d+$/.test(m[2])) {
          return { ok: false, error: `memory.events_${m[1]}_non_integer` };
        }
        const parsed = Number(m[2]);
        if (!Number.isSafeInteger(parsed) || parsed < 0) {
          return { ok: false, error: `memory.events_${m[1]}_out_of_range` };
        }
        if (m[1] === "oom") {
          sawOomCount += 1;
          oomCount = parsed;
        } else {
          sawOomKillCount += 1;
          oomKillCount = parsed;
        }
      }
    }
    if (sawOomCount === 0) {
      return { ok: false, error: "memory.events_oom_missing" };
    }
    if (sawOomKillCount === 0) {
      return { ok: false, error: "memory.events_oom_kill_missing" };
    }
    if (sawOomCount > 1 || sawOomKillCount > 1) {
      return { ok: false, error: "memory.events_duplicate_oom_key" };
    }
    return {
      ok: true,
      currentBytes: curRes.value,
      peakBytes: Math.max(peakRes.value, curRes.value),
      rawPeakBytes: peakRes.value,
      oomCount,
      oomKillCount,
    };
  } catch (err) {
    return {
      ok: false,
      error: `cgroup_read_failed: ${err && err.message ? err.message : String(err)}`,
    };
  }
}

export function evaluateCgroupOomProgress({
  baselineOom,
  baselineOomKill,
  prevOom = baselineOom,
  prevOomKill = baselineOomKill,
  currentOom,
  currentOomKill,
}) {
  if (
    !Number.isSafeInteger(currentOom) ||
    !Number.isSafeInteger(currentOomKill) ||
    currentOom < 0 ||
    currentOomKill < 0
  ) {
    return {
      ok: false,
      regressed: false,
      error: "cgroup_oom_counter_invalid",
      oomDelta: null,
      oomKillDelta: null,
      breachReason: "metering_unavailable",
      breachAttribution: "metering_unavailable",
    };
  }
  if (
    currentOom < baselineOom ||
    currentOomKill < baselineOomKill ||
    currentOom < prevOom ||
    currentOomKill < prevOomKill
  ) {
    return {
      ok: false,
      regressed: true,
      error: `cgroup_oom_counter_regressed (oom=${currentOom}, oom_kill=${currentOomKill})`,
      oomDelta: null,
      oomKillDelta: null,
      breachReason: "metering_unavailable",
      breachAttribution: "metering_unavailable",
    };
  }
  const oomDelta = currentOom - baselineOom;
  const oomKillDelta = currentOomKill - baselineOomKill;
  if (oomKillDelta > 0) {
    return {
      ok: true,
      regressed: false,
      error: null,
      oomDelta,
      oomKillDelta,
      breachReason: "cgroup_oom_kill",
      breachAttribution: "cgroup_oom_kill",
    };
  }
  if (oomDelta > 0) {
    return {
      ok: true,
      regressed: false,
      error: null,
      oomDelta,
      oomKillDelta,
      breachReason: "cgroup_oom",
      breachAttribution: "cgroup_oom_event",
    };
  }
  return {
    ok: true,
    regressed: false,
    error: null,
    oomDelta: 0,
    oomKillDelta: 0,
    breachReason: null,
    breachAttribution: null,
  };
}

export function validateCgroupV2Preflight(cgroupDir, memoryLimitBytes) {
  const result = {
    ok: false,
    errorCode: "cgroup_misconfigured",
    detail: "",
    memoryEnforcementMode:
      process.platform === "linux"
        ? "linux_cgroup_v2"
        : "cgroup_v2_contract_simulation_non_linux",
    cgroupContractValid: false,
    cgroupPath: null,
    initialProcsCount: null,
    memoryMaxBytes: null,
    swapMaxBytes: null,
    initialSnapshot: null,
  };

  let st = null;
  try {
    st = fs.statSync(cgroupDir);
  } catch {
    result.detail = `cgroup directory unreadable: ${cgroupDir}`;
    return result;
  }
  if (!st.isDirectory()) {
    result.detail = `cgroup path is not a directory: ${cgroupDir}`;
    return result;
  }

  // Verify supervisor itself is already attached to this cgroup from startup.
  const procsPath = path.join(cgroupDir, "cgroup.procs");
  if (!fs.existsSync(procsPath)) {
    result.detail = "cgroup.procs missing";
    return result;
  }
  let procsText = "";
  try {
    procsText = fs.readFileSync(procsPath, "utf8");
  } catch {
    result.detail = "cgroup.procs unreadable";
    return result;
  }
  const procsSet = new Set(procsText.trim().split(/\s+/).filter(Boolean));
  if (!procsSet.has(String(process.pid))) {
    result.detail = `supervisor pid ${process.pid} is not pre-attached to ${procsPath}`;
    return result;
  }
  result.initialProcsCount = procsSet.size;
  result.cgroupPath = fs.realpathSync(cgroupDir);

  if (process.platform === "linux") {
    try {
      const realCg = fs.realpathSync(cgroupDir);
      const realRoot = fs.realpathSync("/sys/fs/cgroup");
      if (realCg !== realRoot && !realCg.startsWith(realRoot + path.sep)) {
        result.detail = `cgroupDir is outside /sys/fs/cgroup: ${realCg}`;
        return result;
      }
      const selfCg = fs.readFileSync("/proc/self/cgroup", "utf8");
      const v2Line = selfCg
        .split(/\r?\n/)
        .find((l) => l.startsWith("0::"));
      if (!v2Line) {
        result.detail = "cgroup v2 unified hierarchy (0::) not active in /proc/self/cgroup";
        return result;
      }
      const selfRel = v2Line.slice(3).replace(/^\/+/, "");
      const expectedPath = selfRel ? path.join(realRoot, selfRel) : realRoot;
      if (realCg !== expectedPath) {
        result.detail = `/proc/self/cgroup (${expectedPath}) does not match ${realCg}`;
        return result;
      }
    } catch (err) {
      result.detail = `linux cgroup self-check failed: ${err.message}`;
      return result;
    }
  }

  const maxRes = readCgroupIntFile(path.join(cgroupDir, "memory.max"), {
    allowZero: false,
  });
  if (!maxRes.ok) {
    result.detail = `memory.max invalid (${maxRes.reason})`;
    return result;
  }
  if (maxRes.value > memoryLimitBytes) {
    result.detail = `memory.max (${maxRes.value}) exceeds --memory-limit-bytes (${memoryLimitBytes})`;
    return result;
  }
  result.memoryMaxBytes = maxRes.value;

  const swapRes = readCgroupIntFile(path.join(cgroupDir, "memory.swap.max"), {
    allowZero: true,
  });
  if (!swapRes.ok) {
    result.detail = `memory.swap.max invalid (${swapRes.reason})`;
    return result;
  }
  if (swapRes.value !== 0) {
    result.detail = `memory.swap.max (${swapRes.value}) must be 0`;
    return result;
  }
  result.swapMaxBytes = swapRes.value;

  // Now check live metering availability (`metering_unavailable` on failure).
  const snap = readCgroupV2Snapshot(cgroupDir);
  if (!snap || !snap.ok) {
    result.errorCode = "metering_unavailable";
    result.detail = snap ? snap.error : "metering snapshot failed";
    return result;
  }

  result.ok = true;
  result.errorCode = "none";
  result.cgroupContractValid = true;
  result.initialSnapshot = snap;
  return result;
}

function killProcessGroup(pid) {
  if (!pid || pid <= 0) return;
  try {
    process.kill(-pid, "SIGKILL");
  } catch {
    try {
      process.kill(pid, "SIGKILL");
    } catch {
      // Already exited.
    }
  }
}

function parseDarwinTimeMaxRssBytes(stderrText) {
  if (!stderrText) return null;
  let lastVal = null;
  for (const line of stderrText.split(/\r?\n/)) {
    const m = line.match(/^\s*(\d+)\s+maximum resident set size\b/);
    if (m) {
      const parsed = Number(m[1]);
      if (Number.isFinite(parsed) && parsed > 0) {
        lastVal = parsed;
      }
    }
  }
  return lastVal;
}

function canUseDarwinTimeWrapper() {
  if (process.platform !== "darwin") return false;
  try {
    fs.accessSync("/usr/bin/time", fs.constants.X_OK);
    return true;
  } catch {
    return false;
  }
}

function runIsolatedStage({
  stageName,
  command,
  args,
  hardDeadlineNs,
  memoryLimitBytes,
  cgroupDir,
  cgroupBaselineOom,
  cgroupBaselineOomKill,
  cgroupPrevOom,
  cgroupPrevOomKill,
  timeoutReason,
  timeoutAttribution,
  rssReason,
  rssAttribution,
  pollIntervalMs = 25,
  onStageSpawn = null,
}) {
  return new Promise((resolve) => {
    const stageStartNs = process.hrtime.bigint();
    const useDarwinTime = canUseDarwinTimeWrapper();
    const spawnCmd = useDarwinTime ? "/usr/bin/time" : command;
    const spawnArgs = useDarwinTime ? ["-l", command, ...args] : args;

    let stdout = "";
    let stderr = "";
    let killedReason = "";
    let killedAttribution = "";
    let polledPeakRssBytes = null;
    let cgroupPeakBytes = null;
    let lastCgOomCount = cgroupPrevOom;
    let lastCgOomKillCount = cgroupPrevOomKill;
    let cgroupOomDelta = cgroupDir ? 0 : null;
    let cgroupOomKillDelta = cgroupDir ? 0 : null;
    let cgroupOomRegressed = false;
    let psSampleFailures = 0;
    let cgroupSampleFailure = null;
    let settled = false;

    const remainingMsNow = () =>
      Math.max(0, Number(hardDeadlineNs - process.hrtime.bigint()) / 1e6);

    if (remainingMsNow() <= 0) {
      resolve({
        exitCode: null,
        signal: null,
        stdout: "",
        stderr: "",
        wallMs: 0,
        measuredMaxRssBytes: null,
        darwinTimeRssBytes: null,
        polledMaxRssBytes: null,
        cgroupPeakBytes: null,
        cgroupFinalOomCount: lastCgOomCount,
        cgroupFinalOomKillCount: lastCgOomKillCount,
        cgroupOomDelta,
        cgroupOomKillDelta,
        cgroupOomRegressed: false,
        meteringOk: true,
        meteringIssue: null,
        killedReason: timeoutReason,
        killedAttribution: timeoutAttribution,
      });
      return;
    }

    const child = spawn(spawnCmd, spawnArgs, {
      detached: true,
      stdio: ["ignore", "pipe", "pipe"],
    });

    if (child.pid && typeof onStageSpawn === "function") {
      try {
        onStageSpawn({
          stage: stageName,
          pid: child.pid,
          pgid: child.pid,
        });
      } catch {
        // Ignore diagnostic hook error.
      }
    }

    child.stdout.on("data", (d) => {
      stdout += d.toString("utf8");
    });
    child.stderr.on("data", (d) => {
      stderr += d.toString("utf8");
    });

    const inspectCgroupSnap = (cg, isPostExit) => {
      if (!cg || !cg.ok) {
        cgroupSampleFailure = cg
          ? cg.error
          : isPostExit
            ? "cgroup_post_exit_snapshot_failed"
            : "cgroup_snapshot_failed";
        return { breached: true, reason: "metering_unavailable", attribution: "metering_unavailable" };
      }
      cgroupPeakBytes =
        cgroupPeakBytes === null
          ? cg.peakBytes
          : Math.max(cgroupPeakBytes, cg.peakBytes);
      const oomEval = evaluateCgroupOomProgress({
        baselineOom: cgroupBaselineOom,
        baselineOomKill: cgroupBaselineOomKill,
        prevOom: lastCgOomCount,
        prevOomKill: lastCgOomKillCount,
        currentOom: cg.oomCount,
        currentOomKill: cg.oomKillCount,
      });
      if (!oomEval.ok) {
        cgroupSampleFailure = oomEval.error;
        cgroupOomRegressed = Boolean(oomEval.regressed);
        cgroupOomDelta = null;
        cgroupOomKillDelta = null;
        return {
          breached: true,
          reason: oomEval.breachReason,
          attribution: oomEval.breachAttribution,
        };
      }
      lastCgOomCount = cg.oomCount;
      lastCgOomKillCount = cg.oomKillCount;
      cgroupOomDelta = oomEval.oomDelta;
      cgroupOomKillDelta = oomEval.oomKillDelta;
      if (oomEval.breachReason) {
        return {
          breached: true,
          reason: oomEval.breachReason,
          attribution: oomEval.breachAttribution,
        };
      }
      if (cg.peakBytes > memoryLimitBytes) {
        return { breached: true, reason: rssReason, attribution: rssAttribution };
      }
      return { breached: false, reason: null, attribution: null };
    };

    const enforceBounds = () => {
      if (settled || !child.pid) return;
      if (process.hrtime.bigint() >= hardDeadlineNs) {
        if (!killedReason) {
          killedReason = timeoutReason;
          killedAttribution = timeoutAttribution;
        }
        killProcessGroup(child.pid);
        return;
      }
      if (cgroupDir) {
        const res = inspectCgroupSnap(readCgroupV2Snapshot(cgroupDir), false);
        if (res.breached) {
          if (!killedReason) {
            killedReason = res.reason;
            killedAttribution = res.attribution;
          }
          killProcessGroup(child.pid);
          return;
        }
      } else {
        try {
          const snap = listProcessGroupMembers(child.pid);
          if (snap.members.length > 0) {
            polledPeakRssBytes =
              polledPeakRssBytes === null
                ? snap.totalRssBytes
                : Math.max(polledPeakRssBytes, snap.totalRssBytes);
            if (snap.totalRssBytes > memoryLimitBytes) {
              if (!killedReason) {
                killedReason = rssReason;
                killedAttribution = rssAttribution;
              }
              killProcessGroup(child.pid);
            }
          }
        } catch {
          psSampleFailures += 1;
        }
      }
    };

    const deadlineTimer = setTimeout(
      enforceBounds,
      Math.max(1, Math.ceil(remainingMsNow()))
    );
    const pollTimer = setInterval(enforceBounds, pollIntervalMs);

    const finalize = (exitCode, signal) => {
      if (settled) return;
      settled = true;
      clearTimeout(deadlineTimer);
      clearInterval(pollTimer);
      if (child.pid) killProcessGroup(child.pid);

      if (cgroupDir && !cgroupSampleFailure) {
        const res = inspectCgroupSnap(readCgroupV2Snapshot(cgroupDir), true);
        if (res.breached && !killedReason && (res.reason === "cgroup_oom" || res.reason === "cgroup_oom_kill")) {
          killedReason = res.reason;
          killedAttribution = res.attribution;
        }
      }

      const darwinTimeRssBytes = useDarwinTime
        ? parseDarwinTimeMaxRssBytes(stderr)
        : null;
      const candidates = [polledPeakRssBytes, darwinTimeRssBytes].filter(
        (v) => typeof v === "number" && Number.isFinite(v) && v > 0
      );
      const measuredMaxRssBytes =
        candidates.length > 0 ? Math.max(...candidates) : null;

      let meteringOk = true;
      let meteringIssue = null;
      if (cgroupDir) {
        if (cgroupSampleFailure) {
          meteringOk = false;
          meteringIssue = cgroupSampleFailure;
        }
      } else if (measuredMaxRssBytes === null) {
        meteringOk = false;
        meteringIssue =
          psSampleFailures > 0
            ? `${stageName}_ps_failed_and_no_rusage`
            : `${stageName}_rss_unobserved`;
      }

      const wallMs = Number(process.hrtime.bigint() - stageStartNs) / 1e6;
      resolve({
        exitCode,
        signal,
        stdout,
        stderr,
        wallMs,
        measuredMaxRssBytes,
        darwinTimeRssBytes,
        polledMaxRssBytes: polledPeakRssBytes,
        cgroupPeakBytes,
        cgroupFinalOomCount: lastCgOomCount,
        cgroupFinalOomKillCount: lastCgOomKillCount,
        cgroupOomDelta,
        cgroupOomKillDelta,
        cgroupOomRegressed,
        meteringOk,
        meteringIssue,
        killedReason,
        killedAttribution,
      });
    };

    child.on("error", () => {
      if (!killedReason) {
        killedReason = "worker_failed";
        killedAttribution =
          stageName === "check" ? "checker_failed" : "solver_worker_failed";
      }
      finalize(null, null);
    });
    child.on("close", (code, signal) => {
      finalize(code, signal);
    });
  });
}

function writeReceiptIfRequested(outReceiptPath, receipt) {
  if (!outReceiptPath) return;
  const destDir = path.dirname(path.resolve(outReceiptPath));
  fs.mkdirSync(destDir, { recursive: true });
  const existingStat = safeStat(outReceiptPath);
  const tmpPath = path.join(
    destDir,
    `.tmp.receipt.${process.pid}.${Date.now()}.${Math.random()
      .toString(36)
      .slice(2, 8)}`
  );
  fs.writeFileSync(tmpPath, JSON.stringify(receipt, null, 2) + "\n", {
    encoding: "utf8",
    mode: existingStat ? existingStat.mode & 0o777 : 0o644,
  });
  try {
    if (existingStat) {
      fs.chmodSync(tmpPath, existingStat.mode & 0o777);
    }
    fs.renameSync(tmpPath, outReceiptPath);
  } catch (err) {
    fs.rmSync(tmpPath, { force: true });
    throw err;
  }
}

function mapSolverUnknownAttribution(unknownReason) {
  switch (unknownReason) {
    case "timeout":
      return "solver_soft_timeout";
    case "memory_budget":
      return "solver_soft_memory_budget";
    case "node_limit":
      return "solver_node_limit";
    case "depth_limit":
      return "solver_depth_limit";
    default:
      return "solver_unknown_other";
  }
}

export function evaluateCertificationDecision(input = {}) {
  const {
    isLinux,
    hasCgroupDir,
    cgroupContractValid,
    meteringComplete,
    withinTotalDeadline,
    settlementPassed,
    stagingCleaned,
    cgroupPeakBytes,
    memoryLimitBytes,
    cgroupOomDelta,
    cgroupOomKillDelta,
    verified,
    published,
    hasOutProofPath,
    verdict,
    settlementBreachReason = null,
  } = input && typeof input === "object" ? input : {};
  const validProvenVerdict =
    verdict === "PROVEN_WIN" || verdict === "PROVEN_LOSS";
  const validMemoryLimit =
    typeof memoryLimitBytes === "number" &&
    Number.isSafeInteger(memoryLimitBytes) &&
    memoryLimitBytes > 0;
  const validCgroupPeak =
    typeof cgroupPeakBytes === "number" &&
    Number.isSafeInteger(cgroupPeakBytes) &&
    cgroupPeakBytes >= 0;
  const withinCgroupLimit =
    validMemoryLimit && validCgroupPeak && cgroupPeakBytes <= memoryLimitBytes;
  const noCgroupOom = cgroupOomDelta === 0 && cgroupOomKillDelta === 0;
  const budgetCertified = Boolean(
    isLinux === true &&
      hasCgroupDir === true &&
      cgroupContractValid === true &&
      meteringComplete === true &&
      withinTotalDeadline === true &&
      settlementPassed === true &&
      stagingCleaned === true &&
      withinCgroupLimit &&
      noCgroupOom &&
      verified === true &&
      validProvenVerdict
  );
  const eligibleForFormalCount = Boolean(
    verified === true &&
      published === true &&
      budgetCertified === true &&
      meteringComplete === true &&
      withinTotalDeadline === true &&
      settlementPassed === true
  );
  let formalCountIneligibleReason = null;
  if (!eligibleForFormalCount) {
    if (meteringComplete !== true) {
      formalCountIneligibleReason = "metering_incomplete";
    } else if (settlementBreachReason) {
      formalCountIneligibleReason = settlementBreachReason;
    } else if (withinTotalDeadline === false) {
      formalCountIneligibleReason = "total_deadline_exceeded";
    } else if (verified !== true) {
      formalCountIneligibleReason = "not_verified";
    } else if (published !== true) {
      formalCountIneligibleReason = hasOutProofPath
        ? "not_published"
        : "no_out_proof_path";
    } else if (settlementPassed !== true) {
      formalCountIneligibleReason = "settlement_not_passed";
    } else if (!validProvenVerdict) {
      formalCountIneligibleReason = "invalid_or_unproven_verdict";
    } else if (!validMemoryLimit || !validCgroupPeak) {
      formalCountIneligibleReason = "invalid_memory_metrics";
    } else if (!withinCgroupLimit) {
      formalCountIneligibleReason = "memory_limit_exceeded";
    } else if (!noCgroupOom) {
      formalCountIneligibleReason = "cgroup_oom_detected";
    } else if (!budgetCertified) {
      formalCountIneligibleReason = isLinux
        ? "no_linux_cgroup_certification"
        : "non_linux_advisory_metering_only";
    }
  }
  return { budgetCertified, eligibleForFormalCount, formalCountIneligibleReason };
}

export async function runSupervisedSolve(rawOpts) {
  const taskStartNs = process.hrtime.bigint();
  const opts = {
    totalTimeMs: 600000,
    searchSoftMs: 480000,
    memoryLimitBytes: 2000000000,
    nodeLimit: 100000000,
    maxDepth: 64,
    cgroupDir: "",
    outProofPath: "",
    outReceiptPath: "",
    faultCheckDelayMs: 0,
    faultPublishDelayMs: 0,
    faultPostPublishDelayMs: 0,
    faultTamperStaging: false,
    onStageSpawn: null,
    onBeforeSettlement: null,
    ...rawOpts,
  };
  const hardDeadlineNs =
    taskStartNs + BigInt(opts.totalTimeMs) * 1_000_000n;
  if (!opts.solverMemoryBytes) {
    opts.solverMemoryBytes = Math.max(
      1,
      Math.floor(opts.memoryLimitBytes * 0.85)
    );
  }

  validateOutputPathIdentities({
    problemPath: opts.problemPath,
    outProofPath: opts.outProofPath,
    outReceiptPath: opts.outReceiptPath,
  });

  const isLinux = process.platform === "linux";
  const defaultNonCgroupMode =
    process.platform === "darwin"
      ? "macos_rss_polling_advisory"
      : "posix_rss_polling_advisory";

  let cgPreflight = null;
  if (opts.cgroupDir) {
    cgPreflight = validateCgroupV2Preflight(
      opts.cgroupDir,
      opts.memoryLimitBytes
    );
  }

  const meteringIssues = [];
  let supervisorPeakRssBytes = process.memoryUsage().rss;
  const sampleSupervisorRss = () => {
    const cur = process.memoryUsage().rss;
    if (cur > supervisorPeakRssBytes) supervisorPeakRssBytes = cur;
    return supervisorPeakRssBytes;
  };

  const cgroupBaselineOom =
    cgPreflight && cgPreflight.initialSnapshot
      ? cgPreflight.initialSnapshot.oomCount
      : null;
  const cgroupBaselineOomKill =
    cgPreflight && cgPreflight.initialSnapshot
      ? cgPreflight.initialSnapshot.oomKillCount
      : null;
  let lastCgOomCount = cgroupBaselineOom;
  let lastCgOomKillCount = cgroupBaselineOomKill;

  const receipt = {
    problemPath: opts.problemPath,
    problemId: path.basename(opts.problemPath, path.extname(opts.problemPath)),
    verdict: "UNKNOWN",
    proofRootStatus: null,
    stage: "solve",
    unknownReason: "internal_error",
    stopAttribution: "internal_error",
    verified: false,
    published: false,
    publishedProofPath: null,
    verifiedStagingSha256: null,
    publishedSha256: null,
    proofChecksum: null,
    withinTotalDeadline: null,
    settlementWallMs: null,
    settlementPassed: false,
    settlementBreachReason: null,
    budgetCertified: false,
    eligibleForFormalCount: false,
    formalCountIneligibleReason: null,
    meteringComplete: false,
    meteringIssues,
    memoryEnforcementMode: cgPreflight
      ? cgPreflight.memoryEnforcementMode
      : defaultNonCgroupMode,
    cgroupContractValid: cgPreflight ? cgPreflight.cgroupContractValid : null,
    cgroupPath: cgPreflight ? cgPreflight.cgroupPath : null,
    cgroupInitialProcsCount: cgPreflight ? cgPreflight.initialProcsCount : null,
    cgroupMemoryMaxBytes: cgPreflight ? cgPreflight.memoryMaxBytes : null,
    cgroupSwapMaxBytes: cgPreflight ? cgPreflight.swapMaxBytes : null,
    cgroupInitialPeakBytes:
      cgPreflight && cgPreflight.initialSnapshot
        ? cgPreflight.initialSnapshot.peakBytes
        : null,
    cgroupPeakBytes:
      cgPreflight && cgPreflight.initialSnapshot
        ? cgPreflight.initialSnapshot.peakBytes
        : null,
    cgroupLastObservedPeakBytes:
      cgPreflight && cgPreflight.initialSnapshot
        ? cgPreflight.initialSnapshot.peakBytes
        : null,
    cgroupInitialOomCount: cgroupBaselineOom,
    cgroupInitialOomKillCount: cgroupBaselineOomKill,
    cgroupLastObservedOomCount: cgroupBaselineOom,
    cgroupLastObservedOomKillCount: cgroupBaselineOomKill,
    cgroupFinalOomCount: cgroupBaselineOom,
    cgroupFinalOomKillCount: cgroupBaselineOomKill,
    cgroupOomDelta: cgPreflight && cgPreflight.ok ? 0 : null,
    cgroupOomKillDelta: cgPreflight && cgPreflight.ok ? 0 : null,
    totalTimeMs: opts.totalTimeMs,
    searchSoftMs: opts.searchSoftMs,
    verifyReserveMs: Math.max(0, opts.totalTimeMs - opts.searchSoftMs),
    memoryLimitBytes: opts.memoryLimitBytes,
    solverMemoryBytes: opts.solverMemoryBytes,
    nodeLimit: opts.nodeLimit,
    maxDepth: opts.maxDepth,
    solveMs: null,
    checkMs: null,
    publishMs: null,
    publishCompletedWallMs: null,
    cleanupMs: null,
    totalWallMs: null,
    numNodes: null,
    prunedOutsideRz: null,
    bestMove: null,
    checkerCode: "SKIPPED",
    solveExitCode: null,
    solveSignal: null,
    checkExitCode: null,
    checkSignal: null,
    peakRssBytes: null,
    solveMaxRssBytes: null,
    checkMaxRssBytes: null,
    supervisorPeakRssBytes,
    estimatedMemoryBytes: null,
    stagingCleaned: false,
  };

  if (cgPreflight && !cgPreflight.ok) {
    const endNs = process.hrtime.bigint();
    meteringIssues.push(cgPreflight.detail);
    receipt.verdict = "UNKNOWN";
    receipt.stage = "preflight";
    receipt.unknownReason = cgPreflight.errorCode;
    receipt.stopAttribution = cgPreflight.errorCode;
    receipt.meteringComplete = false;
    receipt.budgetCertified = false;
    receipt.eligibleForFormalCount = false;
    receipt.formalCountIneligibleReason = cgPreflight.errorCode;
    receipt.stagingCleaned = true;
    receipt.cleanupMs = 0;
    receipt.withinTotalDeadline = endNs <= hardDeadlineNs;
    receipt.totalWallMs = Number(
      (Number(endNs - taskStartNs) / 1e6).toFixed(3)
    );
    writeReceiptIfRequested(opts.outReceiptPath, receipt);
    return receipt;
  }

  let stagingParent = os.tmpdir();
  if (opts.outProofPath) {
    stagingParent = path.dirname(path.resolve(opts.outProofPath));
    fs.mkdirSync(stagingParent, { recursive: true });
  }
  const stagingDir = fs.mkdtempSync(
    path.join(stagingParent, ".ldprover-stage-"),
  );
  fs.chmodSync(stagingDir, 0o700);
  const stagingProof = path.join(stagingDir, "staging.proof.json");
  const stagingProfile = path.join(stagingDir, "staging.profile.json");

  const cleanupStagingDir = () => {
    if (fs.existsSync(stagingDir)) {
      const cleanupStartNs = process.hrtime.bigint();
      fs.rmSync(stagingDir, { recursive: true, force: true });
      receipt.stagingCleaned = !fs.existsSync(stagingDir);
      receipt.cleanupMs = Number(
        (Number(process.hrtime.bigint() - cleanupStartNs) / 1e6).toFixed(3)
      );
    } else if (!receipt.stagingCleaned) {
      receipt.stagingCleaned = true;
      if (receipt.cleanupMs === null) receipt.cleanupMs = 0;
    }
  };

  const invalidateTerminalCgroupMetrics = () => {
    receipt.cgroupPeakBytes = null;
    receipt.cgroupFinalOomCount = null;
    receipt.cgroupFinalOomKillCount = null;
    receipt.cgroupOomDelta = null;
    receipt.cgroupOomKillDelta = null;
  };

  const applyCgroupStageRunStats = (stageRun) => {
    if (!opts.cgroupDir) return;
    if (stageRun.cgroupPeakBytes !== null) {
      const mergedPeak =
        receipt.cgroupLastObservedPeakBytes === null
          ? stageRun.cgroupPeakBytes
          : Math.max(receipt.cgroupLastObservedPeakBytes, stageRun.cgroupPeakBytes);
      receipt.cgroupLastObservedPeakBytes = mergedPeak;
      receipt.cgroupPeakBytes = mergedPeak;
      receipt.peakRssBytes =
        receipt.peakRssBytes === null
          ? mergedPeak
          : Math.max(receipt.peakRssBytes, mergedPeak);
    }
    if (stageRun.cgroupFinalOomCount !== null) {
      lastCgOomCount = stageRun.cgroupFinalOomCount;
      receipt.cgroupLastObservedOomCount = stageRun.cgroupFinalOomCount;
      receipt.cgroupFinalOomCount = stageRun.cgroupFinalOomCount;
    }
    if (stageRun.cgroupFinalOomKillCount !== null) {
      lastCgOomKillCount = stageRun.cgroupFinalOomKillCount;
      receipt.cgroupLastObservedOomKillCount = stageRun.cgroupFinalOomKillCount;
      receipt.cgroupFinalOomKillCount = stageRun.cgroupFinalOomKillCount;
    }
    if (!stageRun.meteringOk || stageRun.cgroupOomRegressed) {
      invalidateTerminalCgroupMetrics();
    } else {
      if (stageRun.cgroupOomDelta !== null) {
        receipt.cgroupOomDelta =
          receipt.cgroupOomDelta === null
            ? stageRun.cgroupOomDelta
            : Math.max(receipt.cgroupOomDelta, stageRun.cgroupOomDelta);
      }
      if (stageRun.cgroupOomKillDelta !== null) {
        receipt.cgroupOomKillDelta =
          receipt.cgroupOomKillDelta === null
            ? stageRun.cgroupOomKillDelta
            : Math.max(receipt.cgroupOomKillDelta, stageRun.cgroupOomKillDelta);
      }
    }
  };

  const evaluateCgroupSnapshotPoint = () => {
    if (!opts.cgroupDir) return { breached: false, reason: null, attribution: null };
    const cg = readCgroupV2Snapshot(opts.cgroupDir);
    if (!cg || !cg.ok) {
      const msg = cg ? cg.error : "cgroup_snapshot_failed";
      meteringIssues.push(msg);
      invalidateTerminalCgroupMetrics();
      return {
        breached: true,
        reason: "metering_unavailable",
        attribution: "metering_unavailable",
      };
    }
    const basePeak =
      receipt.cgroupLastObservedPeakBytes !== null
        ? receipt.cgroupLastObservedPeakBytes
        : receipt.cgroupPeakBytes;
    const mergedPeak =
      basePeak === null ? cg.peakBytes : Math.max(basePeak, cg.peakBytes);
    receipt.cgroupLastObservedPeakBytes = mergedPeak;
    receipt.cgroupPeakBytes = mergedPeak;
    receipt.peakRssBytes =
      receipt.peakRssBytes === null
        ? mergedPeak
        : Math.max(receipt.peakRssBytes, mergedPeak);
    const oomEval = evaluateCgroupOomProgress({
      baselineOom: cgroupBaselineOom,
      baselineOomKill: cgroupBaselineOomKill,
      prevOom: lastCgOomCount,
      prevOomKill: lastCgOomKillCount,
      currentOom: cg.oomCount,
      currentOomKill: cg.oomKillCount,
    });
    if (!oomEval.ok) {
      meteringIssues.push(oomEval.error);
      invalidateTerminalCgroupMetrics();
      return {
        breached: true,
        reason: "metering_unavailable",
        attribution: "metering_unavailable",
      };
    }
    lastCgOomCount = cg.oomCount;
    lastCgOomKillCount = cg.oomKillCount;
    receipt.cgroupLastObservedOomCount = cg.oomCount;
    receipt.cgroupLastObservedOomKillCount = cg.oomKillCount;
    receipt.cgroupFinalOomCount = cg.oomCount;
    receipt.cgroupFinalOomKillCount = cg.oomKillCount;
    receipt.cgroupOomDelta = oomEval.oomDelta;
    receipt.cgroupOomKillDelta = oomEval.oomKillDelta;
    if (oomEval.breachReason) {
      return {
        breached: true,
        reason: oomEval.breachReason,
        attribution: oomEval.breachAttribution,
      };
    }
    if (receipt.cgroupPeakBytes > opts.memoryLimitBytes) {
      return {
        breached: true,
        reason: "rss_limit",
        attribution: "memory_limit_exceeded",
      };
    }
    return { breached: false, reason: null, attribution: null };
  };

  const finalizeCertificationFlags = () => {
    sampleSupervisorRss();
    receipt.supervisorPeakRssBytes = supervisorPeakRssBytes;
    receipt.meteringComplete = meteringIssues.length === 0;
    const cert = evaluateCertificationDecision({
      isLinux,
      hasCgroupDir: Boolean(opts.cgroupDir),
      cgroupContractValid: receipt.cgroupContractValid,
      meteringComplete: receipt.meteringComplete,
      withinTotalDeadline: receipt.withinTotalDeadline,
      settlementPassed: receipt.settlementPassed,
      stagingCleaned: receipt.stagingCleaned,
      cgroupPeakBytes: receipt.cgroupPeakBytes,
      memoryLimitBytes: opts.memoryLimitBytes,
      cgroupOomDelta: receipt.cgroupOomDelta,
      cgroupOomKillDelta: receipt.cgroupOomKillDelta,
      verified: receipt.verified,
      published: receipt.published,
      hasOutProofPath: Boolean(opts.outProofPath),
      verdict: receipt.verdict,
      settlementBreachReason: receipt.settlementBreachReason,
    });
    receipt.budgetCertified = cert.budgetCertified;
    receipt.eligibleForFormalCount = cert.eligibleForFormalCount;
    receipt.formalCountIneligibleReason = cert.formalCountIneligibleReason;
  };

  try {
    const remBeforeSolveMs = Math.max(
      1,
      Math.floor(Number(hardDeadlineNs - process.hrtime.bigint()) / 1e6)
    );
    const effectiveSoftMs =
      opts.searchSoftMs > opts.totalTimeMs
        ? opts.searchSoftMs
        : Math.max(1, Math.min(opts.searchSoftMs, remBeforeSolveMs));

    const solveArgs = [
      "solve",
      "--problem",
      opts.problemPath,
      "--out-proof",
      stagingProof,
      "--profile-json",
      stagingProfile,
      "--node-limit",
      String(opts.nodeLimit),
      "--max-depth",
      String(opts.maxDepth),
      "--time-limit-ms",
      String(effectiveSoftMs),
      "--memory-budget-bytes",
      String(opts.solverMemoryBytes),
    ];

    const solveRun = await runIsolatedStage({
      stageName: "solve",
      command: opts.tproverBin,
      args: solveArgs,
      hardDeadlineNs,
      memoryLimitBytes: opts.memoryLimitBytes,
      cgroupDir: opts.cgroupDir,
      cgroupBaselineOom,
      cgroupBaselineOomKill,
      cgroupPrevOom: lastCgOomCount,
      cgroupPrevOomKill: lastCgOomKillCount,
      timeoutReason: "hard_timeout",
      timeoutAttribution: "supervisor_hard_timeout_kill",
      rssReason: "rss_limit",
      rssAttribution: "supervisor_rss_limit_kill",
      onStageSpawn: opts.onStageSpawn,
    });

    receipt.solveMs = Number(solveRun.wallMs.toFixed(3));
    receipt.solveExitCode = solveRun.exitCode;
    receipt.solveSignal = solveRun.signal;

    let profileJson = null;
    if (fs.existsSync(stagingProfile)) {
      try {
        profileJson = JSON.parse(fs.readFileSync(stagingProfile, "utf8"));
      } catch {
        profileJson = null;
      }
    }

    let solveMaxRss = solveRun.measuredMaxRssBytes;
    if (profileJson && profileJson.processRusage) {
      const rusageRss = Number(profileJson.processRusage.maxRssBytes);
      if (Number.isFinite(rusageRss) && rusageRss > 0) {
        solveMaxRss =
          solveMaxRss === null ? rusageRss : Math.max(solveMaxRss, rusageRss);
      }
    }
    receipt.solveMaxRssBytes = solveMaxRss;
    if (solveMaxRss !== null) {
      receipt.peakRssBytes =
        receipt.peakRssBytes === null
          ? solveMaxRss
          : Math.max(receipt.peakRssBytes, solveMaxRss);
    }

    if (profileJson && profileJson.structuresAndMemory) {
      const est = Number(profileJson.structuresAndMemory.estimatedMemoryBytes);
      if (Number.isFinite(est) && est >= 0) {
        receipt.estimatedMemoryBytes = est;
      }
    }

    applyCgroupStageRunStats(solveRun);

    if (!solveRun.meteringOk) {
      meteringIssues.push(solveRun.meteringIssue || "solve_metering_incomplete");
    } else if (solveMaxRss === null && !opts.cgroupDir) {
      meteringIssues.push("solve_rss_unobserved");
    }

    // Always attempt to parse solve stdout JSON so node counts / metadata
    // are never lost on RSS limit breach or signal exit.
    let solveOut = null;
    try {
      const lastLine = solveRun.stdout
        .trim()
        .split(/\r?\n/)
        .filter(Boolean)
        .pop();
      if (lastLine) {
        solveOut = JSON.parse(lastLine);
      }
    } catch {
      solveOut = null;
    }

    if (solveOut && typeof solveOut === "object") {
      if (Number.isFinite(Number(solveOut.numNodes))) {
        receipt.numNodes = Number(solveOut.numNodes);
      }
      if (Number.isFinite(Number(solveOut.prunedOutsideRz))) {
        receipt.prunedOutsideRz = Number(solveOut.prunedOutsideRz);
      }
      if (typeof solveOut.bestMove === "number") {
        receipt.bestMove = solveOut.bestMove;
      }
      if (typeof solveOut.proofChecksum === "string" && solveOut.proofChecksum) {
        receipt.proofChecksum = solveOut.proofChecksum;
      }
    }

    if (!solveRun.meteringOk) {
      receipt.stage = "solve";
      receipt.unknownReason = "metering_unavailable";
      receipt.stopAttribution = "metering_unavailable";
      return receipt;
    }

    if (solveRun.killedReason) {
      receipt.stage = "solve";
      receipt.unknownReason = solveRun.killedReason;
      if (
        solveRun.killedReason === "hard_timeout" &&
        solveRun.signal === null &&
        solveRun.exitCode === 0
      ) {
        receipt.stopAttribution =
          solveOut && solveOut.unknownReason === "timeout"
            ? "solver_soft_timeout_at_hard_deadline"
            : "hard_deadline_expired_on_worker_exit";
      } else {
        receipt.stopAttribution =
          solveRun.killedAttribution || solveRun.killedReason;
      }
      return receipt;
    }

    if (
      (receipt.cgroupOomKillDelta !== null && receipt.cgroupOomKillDelta > 0) ||
      (receipt.cgroupOomDelta !== null && receipt.cgroupOomDelta > 0)
    ) {
      receipt.stage = "solve";
      const killExceeded =
        receipt.cgroupOomKillDelta !== null && receipt.cgroupOomKillDelta > 0;
      receipt.unknownReason = killExceeded ? "cgroup_oom_kill" : "cgroup_oom";
      receipt.stopAttribution = killExceeded
        ? "cgroup_oom_kill"
        : "cgroup_oom_event";
      return receipt;
    }

    if (
      (receipt.peakRssBytes !== null &&
        receipt.peakRssBytes > opts.memoryLimitBytes) ||
      (receipt.cgroupPeakBytes !== null &&
        receipt.cgroupPeakBytes > opts.memoryLimitBytes)
    ) {
      receipt.stage = "solve";
      receipt.unknownReason = "rss_limit";
      receipt.stopAttribution = "supervisor_post_exit_rss_exceeded";
      return receipt;
    }

    if (solveRun.exitCode !== 0 || !solveOut) {
      receipt.stage = "solve";
      receipt.unknownReason = "worker_failed";
      receipt.stopAttribution = "solver_worker_failed";
      return receipt;
    }

    if (
      solveOut.rootStatus !== "PROVEN_WIN" &&
      solveOut.rootStatus !== "PROVEN_LOSS"
    ) {
      receipt.stage = "solve";
      receipt.unknownReason = solveOut.unknownReason || "unknown";
      receipt.stopAttribution = mapSolverUnknownAttribution(
        receipt.unknownReason
      );
      return receipt;
    }

    if (!fs.existsSync(stagingProof)) {
      receipt.stage = "solve";
      receipt.unknownReason = "worker_failed";
      receipt.stopAttribution = "solver_worker_failed";
      return receipt;
    }

    if (opts.faultTamperStaging) {
      const orig = fs.readFileSync(stagingProof, "utf8");
      const tampered = orig.replace(/"bestMove":\s*-?\d+/, '"bestMove": 0');
      if (tampered === orig) {
        throw new Error("faultTamperStaging could not mutate stagingProof");
      }
      fs.writeFileSync(stagingProof, tampered, "utf8");
    }

    receipt.verifiedStagingSha256 = sha256FileHex(stagingProof);

    // Stage 2: Independent process verification strictly bound to original_root.
    if (process.hrtime.bigint() >= hardDeadlineNs) {
      receipt.stage = "check";
      receipt.unknownReason = "checker_timeout";
      receipt.stopAttribution = "checker_hard_timeout_kill";
      return receipt;
    }

    const checkBaseArgs = [
      "check",
      "--problem",
      opts.problemPath,
      "--proof",
      stagingProof,
      "--original-root",
    ];
    let checkCmd = opts.tproverBin;
    let checkArgs = checkBaseArgs;
    if (opts.faultCheckDelayMs > 0) {
      const delaySec = (opts.faultCheckDelayMs / 1000).toFixed(3);
      checkCmd = "/bin/sh";
      checkArgs = [
        "-c",
        'sleep "$1" && shift && exec "$@"',
        "_",
        delaySec,
        opts.tproverBin,
        ...checkBaseArgs,
      ];
    }

    const checkRun = await runIsolatedStage({
      stageName: "check",
      command: checkCmd,
      args: checkArgs,
      hardDeadlineNs,
      memoryLimitBytes: opts.memoryLimitBytes,
      cgroupDir: opts.cgroupDir,
      cgroupBaselineOom,
      cgroupBaselineOomKill,
      cgroupPrevOom: lastCgOomCount,
      cgroupPrevOomKill: lastCgOomKillCount,
      timeoutReason: "checker_timeout",
      timeoutAttribution: "checker_hard_timeout_kill",
      rssReason: "checker_rss_limit",
      rssAttribution: "checker_rss_limit_kill",
      onStageSpawn: opts.onStageSpawn,
    });

    receipt.checkMs = Number(checkRun.wallMs.toFixed(3));
    receipt.checkExitCode = checkRun.exitCode;
    receipt.checkSignal = checkRun.signal;
    receipt.checkMaxRssBytes = checkRun.measuredMaxRssBytes;
    if (checkRun.measuredMaxRssBytes !== null) {
      receipt.peakRssBytes =
        receipt.peakRssBytes === null
          ? checkRun.measuredMaxRssBytes
          : Math.max(receipt.peakRssBytes, checkRun.measuredMaxRssBytes);
    }

    applyCgroupStageRunStats(checkRun);

    if (!checkRun.meteringOk) {
      meteringIssues.push(
        checkRun.meteringIssue || "check_metering_incomplete"
      );
      receipt.stage = "check";
      receipt.unknownReason = "metering_unavailable";
      receipt.stopAttribution = "metering_unavailable";
      return receipt;
    }

    if (checkRun.killedReason) {
      receipt.stage = "check";
      receipt.unknownReason = checkRun.killedReason;
      receipt.stopAttribution =
        checkRun.killedAttribution || checkRun.killedReason;
      return receipt;
    }

    if (
      (receipt.cgroupOomKillDelta !== null && receipt.cgroupOomKillDelta > 0) ||
      (receipt.cgroupOomDelta !== null && receipt.cgroupOomDelta > 0)
    ) {
      receipt.stage = "check";
      const killExceeded =
        receipt.cgroupOomKillDelta !== null && receipt.cgroupOomKillDelta > 0;
      receipt.unknownReason = killExceeded ? "cgroup_oom_kill" : "cgroup_oom";
      receipt.stopAttribution = killExceeded
        ? "cgroup_oom_kill"
        : "cgroup_oom_event";
      return receipt;
    }

    if (
      (receipt.peakRssBytes !== null &&
        receipt.peakRssBytes > opts.memoryLimitBytes) ||
      (receipt.cgroupPeakBytes !== null &&
        receipt.cgroupPeakBytes > opts.memoryLimitBytes)
    ) {
      receipt.stage = "check";
      receipt.unknownReason = "checker_rss_limit";
      receipt.stopAttribution = "checker_post_exit_rss_exceeded";
      return receipt;
    }

    let checkOut = null;
    try {
      const lastLine = checkRun.stdout
        .trim()
        .split(/\r?\n/)
        .filter(Boolean)
        .pop();
      if (lastLine) {
        checkOut = JSON.parse(lastLine);
      }
    } catch {
      checkOut = null;
    }

    receipt.checkerCode = (checkOut && checkOut.errorCode) || "FAILED";
    if (
      checkRun.exitCode !== 0 ||
      !checkOut ||
      !checkOut.passed ||
      checkOut.errorCode !== "PASS"
    ) {
      receipt.stage = "check";
      receipt.unknownReason = "checker_failed";
      receipt.stopAttribution = "checker_failed";
      return receipt;
    }

    if (process.hrtime.bigint() >= hardDeadlineNs) {
      receipt.stage = "check";
      receipt.unknownReason = "checker_timeout";
      receipt.stopAttribution = "checker_hard_timeout_kill";
      return receipt;
    }

    // Independent original_root check has genuinely PASSED within budget.
    receipt.verified = true;
    receipt.proofRootStatus = solveOut.rootStatus;

    if (opts.outProofPath) {
      // Stage 3: Same-filesystem atomic publish with pre-commit deadline,
      // metering, and bounded-buffer published SHA-256 verification.
      const publishStartNs = process.hrtime.bigint();
      if (opts.faultPublishDelayMs > 0) {
        await new Promise((r) => setTimeout(r, opts.faultPublishDelayMs));
      }

      const preCommitCg = evaluateCgroupSnapshotPoint();
      if (preCommitCg.breached) {
        receipt.publishMs = Number(
          (Number(process.hrtime.bigint() - publishStartNs) / 1e6).toFixed(3)
        );
        receipt.stage = "publish";
        receipt.unknownReason = preCommitCg.reason;
        receipt.stopAttribution =
          preCommitCg.reason === "rss_limit"
            ? "publish_memory_exceeded"
            : preCommitCg.attribution;
        return receipt;
      }

      if (process.hrtime.bigint() >= hardDeadlineNs) {
        receipt.publishMs = Number(
          (Number(process.hrtime.bigint() - publishStartNs) / 1e6).toFixed(3)
        );
        receipt.stage = "publish";
        receipt.unknownReason = "publish_timeout";
        receipt.stopAttribution = "publish_timeout";
        return receipt;
      }

      const existingDestStat = safeStat(opts.outProofPath);
      if (existingDestStat) {
        fs.chmodSync(stagingProof, existingDestStat.mode & 0o777);
      }
      fs.renameSync(stagingProof, opts.outProofPath);
      const publishEndNs = process.hrtime.bigint();
      receipt.publishMs = Number(
        (Number(publishEndNs - publishStartNs) / 1e6).toFixed(3)
      );
      receipt.publishCompletedWallMs = Number(
        (Number(publishEndNs - taskStartNs) / 1e6).toFixed(3)
      );

      const publishedSha256 = sha256FileHex(opts.outProofPath);
      if (publishedSha256 !== receipt.verifiedStagingSha256) {
        receipt.stage = "publish";
        receipt.unknownReason = "publish_integrity_failed";
        receipt.stopAttribution = "publish_integrity_failed";
        return receipt;
      }

      receipt.publishedProofPath = path.resolve(opts.outProofPath);
      receipt.publishedSha256 = publishedSha256;
      receipt.published = true;
    } else {
      receipt.published = false;
      receipt.publishedProofPath = null;
      receipt.publishedSha256 = null;
    }

    // Stage 4: Cleanup staging, then execute final settlement checkpoint
    // covering bounded-buffer readback + cleanup + terminal cgroup snapshot +
    // single monotonic total-deadline check before signing certification.
    cleanupStagingDir();

    if (opts.faultPostPublishDelayMs > 0) {
      await new Promise((r) => setTimeout(r, opts.faultPostPublishDelayMs));
    }
    if (typeof opts.onBeforeSettlement === "function") {
      await opts.onBeforeSettlement({
        receipt,
        cgroupDir: opts.cgroupDir,
        hardDeadlineNs,
      });
    }

    const settlementCg = evaluateCgroupSnapshotPoint();
    const settlementNs = process.hrtime.bigint();
    receipt.settlementWallMs = Number(
      (Number(settlementNs - taskStartNs) / 1e6).toFixed(3)
    );
    receipt.totalWallMs = receipt.settlementWallMs;
    receipt.withinTotalDeadline = settlementNs <= hardDeadlineNs;

    let breachReason = null;
    let breachAttribution = null;
    if (settlementCg.breached) {
      breachReason = settlementCg.reason;
      breachAttribution =
        settlementCg.reason === "rss_limit"
          ? "settlement_memory_exceeded"
          : settlementCg.reason === "metering_unavailable"
            ? "settlement_metering_unavailable"
            : settlementCg.reason === "cgroup_oom_kill"
              ? "settlement_cgroup_oom_kill"
              : "settlement_cgroup_oom_event";
    } else if (!receipt.stagingCleaned) {
      meteringIssues.push("staging_cleanup_incomplete");
      breachReason = "settlement_cleanup_failed";
      breachAttribution = "settlement_cleanup_failed";
    } else if (!receipt.withinTotalDeadline) {
      breachReason = "settlement_timeout";
      breachAttribution = receipt.published
        ? "settlement_post_publish_timeout"
        : "settlement_timeout";
    }

    if (breachReason) {
      receipt.settlementPassed = false;
      receipt.settlementBreachReason = breachReason;
      receipt.verdict = "UNKNOWN";
      receipt.stage = "settlement";
      receipt.unknownReason = breachReason;
      receipt.stopAttribution = breachAttribution;
      return receipt;
    }

    receipt.settlementPassed = true;
    receipt.verdict = solveOut.rootStatus;
    receipt.stage = "done";
    receipt.unknownReason = "none";
    receipt.stopAttribution = receipt.published
      ? "proven_verified_published"
      : "proven_verified_unpublished";
    return receipt;
  } finally {
    cleanupStagingDir();
    const endNs = process.hrtime.bigint();
    if (receipt.withinTotalDeadline === null) {
      receipt.withinTotalDeadline = endNs <= hardDeadlineNs;
    }
    if (receipt.totalWallMs === null) {
      receipt.totalWallMs = Number(
        (Number(endNs - taskStartNs) / 1e6).toFixed(3)
      );
    }
    finalizeCertificationFlags();
    writeReceiptIfRequested(opts.outReceiptPath, receipt);
  }
}

const isMain =
  process.argv[1] &&
  import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href;

if (isMain) {
  try {
    const opts = parseCliArgs(process.argv.slice(2));
    const receipt = await runSupervisedSolve(opts);
    process.stdout.write(JSON.stringify(receipt, null, 2) + "\n");
    process.exit(0);
  } catch (err) {
    process.stderr.write(`[supervised_solve] ${err.message}\n`);
    process.exit(2);
  }
}
