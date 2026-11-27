#!/usr/bin/env node
/**
 * Standalone out-of-group two-cell Linux cgroup v2 acceptance runner (R33).
 *
 * Enforces:
 *   - Exclusive non-reused run output namespace (`run_manifest.json` created
 *     via O_EXCL with problem/binary/runner digests)
 *   - Per-cell outer monotonic timeout (`<= 10000 ms`), group drain/kill
 *     confirmation (`cgroup.procs` empty & `populated == 0`) BEFORE post-run
 *     snapshot and cgroup removal
 *   - Always-persisted `<cell>_outer_record.json` across preflight, post-drain
 *     snapshot, receipt parse, bounded out-of-group audit check, and `finally`
 *   - Strict outer kernel-intervention gate on Cell 2 (pure solver soft-stop,
 *     polling RSS cap, missing snapshot, or isolated SIGKILL with 0 outer
 *     kernel deltas NEVER pass)
 *
 * Refuses to run real-cgroup acceptance on non-Linux hosts (exits with code 3).
 */

import crypto from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { execFileSync, spawn } from "node:child_process";
import { fileURLToPath, pathToFileURL } from "node:url";

const THIS_FILE = fileURLToPath(import.meta.url);
const THIS_DIR = path.dirname(THIS_FILE);
const SUPERVISOR_SCRIPT = path.resolve(THIS_DIR, "supervised_solve.mjs");

export function parseCliArgs(argv) {
  const opts = {
    tproverBin: "",
    cgroupParent: "",
    outDir: "",
    tsumegoDir: "public/tsumego",
    cell1MemoryMaxBytes: 268435456, // 256 MiB
    cell2MemoryMaxBytes: 67108864, // 64 MiB
    totalTimeMs: 10000,
    auditTimeoutMs: 5000,
    cell2KernelTarget: "oom_or_oom_kill",
  };
  for (let i = 0; i < argv.length; ++i) {
    const a = argv[i];
    if (a === "--tprover" && i + 1 < argv.length) {
      opts.tproverBin = argv[++i];
    } else if (a === "--cgroup-parent" && i + 1 < argv.length) {
      opts.cgroupParent = argv[++i];
    } else if (a === "--out-dir" && i + 1 < argv.length) {
      opts.outDir = argv[++i];
    } else if (a === "--tsumego-dir" && i + 1 < argv.length) {
      opts.tsumegoDir = argv[++i];
    } else if (a === "--cell1-memory-max-bytes" && i + 1 < argv.length) {
      opts.cell1MemoryMaxBytes = Number(argv[++i]);
    } else if (a === "--cell2-memory-max-bytes" && i + 1 < argv.length) {
      opts.cell2MemoryMaxBytes = Number(argv[++i]);
    } else if (a === "--total-time-ms" && i + 1 < argv.length) {
      opts.totalTimeMs = Number(argv[++i]);
    } else if (a === "--audit-timeout-ms" && i + 1 < argv.length) {
      opts.auditTimeoutMs = Number(argv[++i]);
    } else if (a === "--cell2-kernel-target" && i + 1 < argv.length) {
      opts.cell2KernelTarget = argv[++i];
    } else {
      throw new Error(`Unknown or incomplete option: ${a}`);
    }
  }
  if (!opts.tproverBin || !opts.cgroupParent || !opts.outDir) {
    throw new Error(
      "Usage: verify_linux_cgroup_two_cells.mjs --tprover <bin> --cgroup-parent </sys/fs/cgroup/...> --out-dir <fresh-dir> [options]"
    );
  }
  if (
    !Number.isInteger(opts.totalTimeMs) ||
    opts.totalTimeMs <= 0 ||
    opts.totalTimeMs > 10000
  ) {
    throw new Error(
      `--total-time-ms must be in 1..10000 for small-budget acceptance, got ${opts.totalTimeMs}`
    );
  }
  if (
    !Number.isInteger(opts.auditTimeoutMs) ||
    opts.auditTimeoutMs <= 0 ||
    opts.auditTimeoutMs > 10000
  ) {
    throw new Error(
      `--audit-timeout-ms must be in 1..10000, got ${opts.auditTimeoutMs}`
    );
  }
  if (
    !Number.isSafeInteger(opts.cell1MemoryMaxBytes) ||
    opts.cell1MemoryMaxBytes <= 0 ||
    !Number.isSafeInteger(opts.cell2MemoryMaxBytes) ||
    opts.cell2MemoryMaxBytes <= 0
  ) {
    throw new Error("Cell memory limits must be positive safe integers");
  }
  if (
    opts.cell2KernelTarget !== "oom_or_oom_kill" &&
    opts.cell2KernelTarget !== "memory_max_event"
  ) {
    throw new Error(
      `--cell2-kernel-target must be 'oom_or_oom_kill' or 'memory_max_event', got ${opts.cell2KernelTarget}`
    );
  }
  return opts;
}

export function sha256File(filePath) {
  const hash = crypto.createHash("sha256");
  const buf = Buffer.allocUnsafe(65536);
  const fd = fs.openSync(filePath, "r");
  try {
    let n = 0;
    while ((n = fs.readSync(fd, buf, 0, buf.length, null)) > 0) {
      hash.update(n === buf.length ? buf : buf.subarray(0, n));
    }
  } finally {
    fs.closeSync(fd);
  }
  return hash.digest("hex");
}

function writeJsonAtomic(filePath, payload) {
  const dir = path.dirname(path.resolve(filePath));
  fs.mkdirSync(dir, { recursive: true });
  const tmpPath = path.join(
    dir,
    `.tmp.${path.basename(filePath)}.${process.pid}.${Date.now()}.${Math.random()
      .toString(36)
      .slice(2, 7)}`
  );
  fs.writeFileSync(tmpPath, JSON.stringify(payload, null, 2) + "\n", "utf8");
  try {
    fs.renameSync(tmpPath, filePath);
  } catch (err) {
    fs.rmSync(tmpPath, { force: true });
    throw err;
  }
}

export function prepareExclusiveRunDir(outDir, manifestPayload) {
  const resolvedOut = path.resolve(outDir);
  if (fs.existsSync(resolvedOut)) {
    const st = fs.lstatSync(resolvedOut);
    if (!st.isDirectory() || st.isSymbolicLink()) {
      throw new Error(
        `--out-dir must be an ordinary non-symlink directory: ${resolvedOut}`
      );
    }
    const existingEntries = fs.readdirSync(resolvedOut);
    if (existingEntries.length > 0) {
      throw new Error(
        `--out-dir must be empty for exclusive per-run isolation (found ${existingEntries.length} entries in ${resolvedOut})`
      );
    }
  } else {
    fs.mkdirSync(resolvedOut, { recursive: true });
  }
  const manifestPath = path.join(resolvedOut, "run_manifest.json");
  fs.writeFileSync(
    manifestPath,
    JSON.stringify(manifestPayload, null, 2) + "\n",
    { encoding: "utf8", flag: "wx" }
  );
  return { outDir: resolvedOut, manifestPath };
}

function readIntFileStrict(filePath, { allowZero = true } = {}) {
  if (!fs.existsSync(filePath)) {
    return { ok: false, error: `${path.basename(filePath)}_missing`, value: null };
  }
  const raw = fs.readFileSync(filePath, "utf8").trim();
  if (!/^\d+$/.test(raw)) {
    return {
      ok: false,
      error: `${path.basename(filePath)}_non_integer`,
      value: null,
    };
  }
  const value = Number(raw);
  if (!Number.isSafeInteger(value) || value < 0 || (!allowZero && value === 0)) {
    return {
      ok: false,
      error: `${path.basename(filePath)}_out_of_range`,
      value: null,
    };
  }
  return { ok: true, error: null, value };
}

export function readCgroupDrainState(cgroupDir) {
  if (!cgroupDir) {
    return {
      ok: false,
      error: "cgroup_dir_missing",
      procsPids: null,
      populated: null,
      drainedEmpty: false,
    };
  }
  try {
    const procsPath = path.join(cgroupDir, "cgroup.procs");
    if (!fs.existsSync(procsPath)) {
      return {
        ok: false,
        error: "cgroup.procs_missing",
        procsPids: null,
        populated: null,
        drainedEmpty: false,
      };
    }
    const procsRaw = fs.readFileSync(procsPath, "utf8").trim();
    const procsPids = [];
    if (procsRaw.length > 0) {
      for (const tok of procsRaw.split(/\s+/)) {
        if (!/^\d+$/.test(tok)) {
          return {
            ok: false,
            error: "cgroup.procs_malformed",
            procsPids: null,
            populated: null,
            drainedEmpty: false,
          };
        }
        const pid = Number(tok);
        if (!Number.isSafeInteger(pid) || pid <= 0) {
          return {
            ok: false,
            error: "cgroup.procs_invalid_pid",
            procsPids: null,
            populated: null,
            drainedEmpty: false,
          };
        }
        procsPids.push(pid);
      }
    }

    const cgEventsPath = path.join(cgroupDir, "cgroup.events");
    if (!fs.existsSync(cgEventsPath)) {
      return {
        ok: false,
        error: "cgroup.events_missing",
        procsPids,
        populated: null,
        drainedEmpty: false,
      };
    }
    const cgEventsTxt = fs.readFileSync(cgEventsPath, "utf8");
    let sawPopulated = 0;
    let populated = null;
    for (const line of cgEventsTxt.split(/\r?\n/)) {
      const trimmed = line.trim();
      if (!trimmed) continue;
      const m = trimmed.match(/^populated\s+(\S+)$/);
      if (m) {
        if (m[1] !== "0" && m[1] !== "1") {
          return {
            ok: false,
            error: "cgroup.events_populated_invalid",
            procsPids,
            populated: null,
            drainedEmpty: false,
          };
        }
        sawPopulated += 1;
        populated = Number(m[1]);
      }
    }
    if (sawPopulated === 0) {
      return {
        ok: false,
        error: "cgroup.events_populated_missing",
        procsPids,
        populated: null,
        drainedEmpty: false,
      };
    }
    if (sawPopulated > 1) {
      return {
        ok: false,
        error: "cgroup.events_populated_duplicate",
        procsPids,
        populated: null,
        drainedEmpty: false,
      };
    }

    return {
      ok: true,
      error: null,
      procsPids,
      populated,
      drainedEmpty: procsPids.length === 0 && populated === 0,
    };
  } catch (err) {
    return {
      ok: false,
      error: `cgroup_drain_read_failed: ${err && err.message ? err.message : String(err)}`,
      procsPids: null,
      populated: null,
      drainedEmpty: false,
    };
  }
}

export function readOuterCgroupV2Snapshot(cgroupDir) {
  if (!cgroupDir) {
    return { ok: false, error: "cgroup_dir_missing" };
  }
  try {
    const curRes = readIntFileStrict(path.join(cgroupDir, "memory.current"));
    if (!curRes.ok) return { ok: false, error: curRes.error };

    const peakRes = readIntFileStrict(path.join(cgroupDir, "memory.peak"));
    if (!peakRes.ok) return { ok: false, error: peakRes.error };

    const maxLimitRes = readIntFileStrict(path.join(cgroupDir, "memory.max"), {
      allowZero: false,
    });
    if (!maxLimitRes.ok) return { ok: false, error: maxLimitRes.error };

    const swapRes = readIntFileStrict(path.join(cgroupDir, "memory.swap.max"));
    if (!swapRes.ok) return { ok: false, error: swapRes.error };

    const eventsPath = path.join(cgroupDir, "memory.events");
    if (!fs.existsSync(eventsPath)) {
      return { ok: false, error: "memory.events_missing" };
    }
    const eventsTxt = fs.readFileSync(eventsPath, "utf8");
    const requiredKeys = ["oom", "oom_kill", "max"];
    const counts = Object.create(null);
    const seen = Object.create(null);
    for (const line of eventsTxt.split(/\r?\n/)) {
      const trimmed = line.trim();
      if (!trimmed) continue;
      const m = trimmed.match(/^(oom|oom_kill|max)\s+(\S+)$/);
      if (m) {
        const key = m[1];
        if (!/^\d+$/.test(m[2])) {
          return { ok: false, error: `memory.events_${key}_non_integer` };
        }
        const val = Number(m[2]);
        if (!Number.isSafeInteger(val) || val < 0) {
          return { ok: false, error: `memory.events_${key}_out_of_range` };
        }
        seen[key] = (seen[key] || 0) + 1;
        counts[key] = val;
      }
    }
    for (const k of requiredKeys) {
      if (!seen[k]) {
        return { ok: false, error: `memory.events_${k}_missing` };
      }
      if (seen[k] > 1) {
        return { ok: false, error: `memory.events_${k}_duplicate` };
      }
    }

    const drain = readCgroupDrainState(cgroupDir);
    if (!drain.ok) {
      return { ok: false, error: drain.error };
    }

    return {
      ok: true,
      currentBytes: curRes.value,
      peakBytes: Math.max(peakRes.value, curRes.value),
      rawPeakBytes: peakRes.value,
      memoryMaxBytes: maxLimitRes.value,
      swapMaxBytes: swapRes.value,
      oomCount: counts.oom,
      oomKillCount: counts.oom_kill,
      maxCount: counts.max,
      procsPids: drain.procsPids,
      populated: drain.populated,
    };
  } catch (err) {
    return {
      ok: false,
      error: `outer_cgroup_read_failed: ${err && err.message ? err.message : String(err)}`,
    };
  }
}

function evaluateCommonOuterGates(ctx) {
  const reasons = [];
  const {
    expectedCgroupDir,
    expectedMemoryMaxBytes,
    totalTimeMs,
    outerWallMs,
    outerWallNs,
    outerTimedOut,
    outerKilledByRunner,
    preCgroupSnapshot,
    postCgroupSnapshot,
    cgroupDrainedEmpty,
    cgroupRemoved,
  } = ctx || {};

  if (!preCgroupSnapshot || preCgroupSnapshot.ok !== true) {
    reasons.push("pre_cgroup_snapshot_unavailable");
  }
  if (!postCgroupSnapshot || postCgroupSnapshot.ok !== true) {
    reasons.push("post_cgroup_snapshot_unavailable");
  }
  if (cgroupDrainedEmpty !== true) {
    reasons.push("cgroup_not_drained_empty");
  }
  if (cgroupRemoved !== true) {
    reasons.push("cgroup_not_removed");
  }

  if (outerTimedOut === true) {
    reasons.push("outer_deadline_timed_out");
  }
  if (outerKilledByRunner === true) {
    reasons.push("outer_killed_by_runner");
  }
  const validTotalTime =
    typeof totalTimeMs === "number" &&
    Number.isSafeInteger(totalTimeMs) &&
    totalTimeMs > 0 &&
    totalTimeMs <= 10000;
  if (!validTotalTime) {
    reasons.push("invalid_outer_time_limit");
  } else if (outerWallNs !== undefined && outerWallNs !== null) {
    if (typeof outerWallNs !== "string" && typeof outerWallNs !== "bigint") {
      reasons.push("outer_wall_time_invalid");
    } else {
      try {
        const nsVal = BigInt(outerWallNs);
        if (nsVal < 0n) {
          reasons.push("outer_wall_time_invalid");
        } else if (nsVal > BigInt(totalTimeMs) * 1_000_000n) {
          reasons.push("outer_wall_time_exceeded");
        }
      } catch {
        reasons.push("outer_wall_time_invalid");
      }
    }
  } else if (
    typeof outerWallMs !== "number" ||
    !Number.isFinite(outerWallMs) ||
    outerWallMs < 0
  ) {
    reasons.push("outer_wall_time_missing_or_invalid");
  } else if (outerWallMs > totalTimeMs) {
    reasons.push("outer_wall_time_exceeded");
  }

  let outerOomDelta = null;
  let outerOomKillDelta = null;
  let outerMaxDelta = null;

  if (preCgroupSnapshot && preCgroupSnapshot.ok) {
    if (preCgroupSnapshot.memoryMaxBytes !== expectedMemoryMaxBytes) {
      reasons.push("pre_memory_max_mismatch");
    }
    if (preCgroupSnapshot.swapMaxBytes !== 0) {
      reasons.push("pre_swap_not_zero");
    }
  }
  if (postCgroupSnapshot && postCgroupSnapshot.ok) {
    if (postCgroupSnapshot.memoryMaxBytes !== expectedMemoryMaxBytes) {
      reasons.push("post_memory_max_mismatch");
    }
    if (postCgroupSnapshot.swapMaxBytes !== 0) {
      reasons.push("post_swap_not_zero");
    }
    if (
      !Array.isArray(postCgroupSnapshot.procsPids) ||
      postCgroupSnapshot.procsPids.length > 0
    ) {
      reasons.push("post_cgroup_procs_not_empty_or_missing");
    }
    if (postCgroupSnapshot.populated !== 0) {
      reasons.push("post_cgroup_populated_not_zero");
    }
  }
  if (
    preCgroupSnapshot &&
    preCgroupSnapshot.ok &&
    postCgroupSnapshot &&
    postCgroupSnapshot.ok
  ) {
    if (
      postCgroupSnapshot.oomCount < preCgroupSnapshot.oomCount ||
      postCgroupSnapshot.oomKillCount < preCgroupSnapshot.oomKillCount ||
      postCgroupSnapshot.maxCount < preCgroupSnapshot.maxCount ||
      postCgroupSnapshot.peakBytes < preCgroupSnapshot.peakBytes
    ) {
      reasons.push("outer_cgroup_counter_regressed");
    } else {
      outerOomDelta = postCgroupSnapshot.oomCount - preCgroupSnapshot.oomCount;
      outerOomKillDelta =
        postCgroupSnapshot.oomKillCount - preCgroupSnapshot.oomKillCount;
      outerMaxDelta = postCgroupSnapshot.maxCount - preCgroupSnapshot.maxCount;
    }
  }

  if (!expectedCgroupDir) {
    reasons.push("missing_expected_cgroup_dir");
  }

  return { reasons, outerOomDelta, outerOomKillDelta, outerMaxDelta };
}

export function evaluateCell1PassRecord(ctx) {
  const common = evaluateCommonOuterGates(ctx);
  const reasons = [...common.reasons];
  const { outerOomDelta, outerOomKillDelta, outerMaxDelta } = common;
  const {
    outerExitCode,
    outerSignal,
    expectedCgroupDir,
    expectedMemoryMaxBytes,
    postCgroupSnapshot,
    proofExists,
    proofSha256,
    receiptExists,
    receiptParseError,
    receipt,
    outerAuditCheck,
    unexpectedError,
  } = ctx || {};

  if (unexpectedError) reasons.push("unexpected_error");
  if (outerExitCode !== 0 || outerSignal !== null) {
    reasons.push("cell1_nonzero_exit_or_signal");
  }
  if (outerOomDelta !== 0 || outerOomKillDelta !== 0) {
    reasons.push("cell1_unexpected_oom_event");
  }
  if (
    postCgroupSnapshot &&
    postCgroupSnapshot.ok &&
    postCgroupSnapshot.peakBytes > expectedMemoryMaxBytes
  ) {
    reasons.push("cell1_outer_peak_exceeded_limit");
  }
  if (proofExists !== true || !proofSha256 || !/^[0-9a-f]{64}$/.test(proofSha256)) {
    reasons.push("cell1_missing_or_unhashed_proof");
  }
  if (receiptExists !== true || receiptParseError || !receipt) {
    reasons.push("cell1_missing_or_invalid_receipt");
  } else {
    if (receipt.verdict !== "PROVEN_WIN") reasons.push("receipt_not_proven_win");
    if (receipt.memoryEnforcementMode !== "linux_cgroup_v2") {
      reasons.push("receipt_not_linux_cgroup_v2");
    }
    if (receipt.cgroupPath !== expectedCgroupDir) {
      reasons.push("receipt_cgroup_path_mismatch");
    }
    if (receipt.verified !== true) reasons.push("receipt_not_verified");
    if (receipt.published !== true) reasons.push("receipt_not_published");
    if (receipt.settlementPassed !== true) reasons.push("receipt_settlement_failed");
    if (receipt.withinTotalDeadline !== true) {
      reasons.push("receipt_exceeded_deadline");
    }
    if (receipt.meteringComplete !== true) reasons.push("receipt_metering_incomplete");
    if (receipt.budgetCertified !== true) reasons.push("receipt_not_budget_certified");
    if (receipt.eligibleForFormalCount !== true) {
      reasons.push("receipt_not_eligible_for_formal_count");
    }
    if (receipt.cgroupOomDelta !== 0 || receipt.cgroupOomKillDelta !== 0) {
      reasons.push("receipt_nonzero_oom_delta");
    }
    if (receipt.publishedSha256 !== proofSha256) {
      reasons.push("receipt_proof_sha256_mismatch");
    }
  }

  if (
    !outerAuditCheck ||
    outerAuditCheck.timedOut === true ||
    outerAuditCheck.passed !== true ||
    outerAuditCheck.errorCode !== "PASS"
  ) {
    reasons.push("outer_independent_audit_failed");
  }

  const passed = reasons.length === 0;
  return {
    passed,
    classification: passed ? "PASS_CERTIFIED" : "FAIL_CELL1",
    reasons,
    outerOomDelta,
    outerOomKillDelta,
    outerMaxDelta,
  };
}

export function evaluateCell2MemLimitRecord(ctx) {
  const common = evaluateCommonOuterGates(ctx);
  const reasons = [...common.reasons];
  const { outerOomDelta, outerOomKillDelta, outerMaxDelta } = common;
  const {
    kernelTargetMode = "oom_or_oom_kill",
    outerExitCode,
    outerSignal,
    outerTimedOut,
    expectedCgroupDir,
    proofExists,
    receiptExists,
    receiptParseError,
    receipt,
    unexpectedError,
  } = ctx || {};

  if (unexpectedError) reasons.push("unexpected_error");
  if (proofExists !== false) reasons.push("cell2_unexpectedly_published_proof");

  if (receiptExists) {
    if (receiptParseError || !receipt) {
      reasons.push("cell2_corrupt_receipt");
    } else {
      if (receipt.verdict !== "UNKNOWN") reasons.push("cell2_receipt_not_unknown");
      if (receipt.published !== false) reasons.push("cell2_receipt_marked_published");
      if (receipt.budgetCertified !== false) {
        reasons.push("cell2_receipt_budget_certified");
      }
      if (receipt.eligibleForFormalCount !== false) {
        reasons.push("cell2_receipt_eligible_for_formal_count");
      }
      if (receipt.cgroupPath !== expectedCgroupDir) {
        reasons.push("cell2_receipt_cgroup_path_mismatch");
      }
    }
  }

  let kernelIntervention = "none";
  if (outerOomKillDelta !== null && outerOomKillDelta > 0) {
    kernelIntervention = "cgroup_oom_kill";
  } else if (outerOomDelta !== null && outerOomDelta > 0) {
    kernelIntervention = "cgroup_oom";
  } else if (outerMaxDelta !== null && outerMaxDelta > 0) {
    kernelIntervention = "cgroup_memory_max_reclaim";
  }

  let targetSatisfied = false;
  let noInterventionClass = null;
  if (kernelIntervention === "cgroup_oom_kill") {
    targetSatisfied = true;
  } else if (kernelIntervention === "cgroup_oom") {
    targetSatisfied = true;
  } else if (kernelIntervention === "cgroup_memory_max_reclaim") {
    if (kernelTargetMode === "memory_max_event") {
      targetSatisfied = true;
    } else {
      reasons.push("no_kernel_oom_observed_only_reclaim_events");
      noInterventionClass = "NO_KERNEL_OOM_OBSERVED_RECLAIM_ONLY";
    }
  } else {
    reasons.push("no_kernel_intervention_observed");
    if (receipt && receipt.unknownReason === "memory_budget") {
      noInterventionClass = "SOLVER_SOFT_STOP_ONLY_NO_KERNEL_INTERVENTION";
    } else if (outerTimedOut === true) {
      noInterventionClass = "OUTER_DEADLINE_EXPIRED_NO_KERNEL_INTERVENTION";
    } else if (outerSignal === "SIGKILL" || outerSignal === "SIGTERM") {
      noInterventionClass = "ISOLATED_SIGNAL_UNATTRIBUTED_NO_KERNEL_OOM";
    } else if (outerExitCode === 0) {
      noInterventionClass = "EXITED_CLEANLY_WITHOUT_KERNEL_INTERVENTION";
    } else {
      noInterventionClass = "NO_KERNEL_INTERVENTION_OBSERVED";
    }
  }

  const passed = reasons.length === 0 && targetSatisfied;
  let classification;
  if (passed) {
    classification =
      kernelIntervention === "cgroup_oom_kill"
        ? "PASS_KERNEL_OOM_KILL_OBSERVED"
        : kernelIntervention === "cgroup_oom"
          ? "PASS_KERNEL_OOM_OBSERVED"
          : "PASS_KERNEL_MEMORY_MAX_RECLAIM_OBSERVED";
  } else if (
    reasons.includes("outer_deadline_timed_out") ||
    reasons.includes("outer_killed_by_runner") ||
    reasons.includes("outer_wall_time_exceeded") ||
    reasons.includes("outer_wall_time_missing_or_invalid") ||
    reasons.includes("outer_wall_time_invalid")
  ) {
    classification =
      kernelIntervention !== "none"
        ? "FAIL_OUTER_TIMEOUT_WITH_KERNEL_EVENT"
        : "OUTER_DEADLINE_EXPIRED_NO_KERNEL_INTERVENTION";
  } else if (
    reasons.includes("pre_cgroup_snapshot_unavailable") ||
    reasons.includes("post_cgroup_snapshot_unavailable") ||
    reasons.includes("cgroup_not_drained_empty") ||
    reasons.includes("post_cgroup_populated_not_zero") ||
    reasons.includes("post_cgroup_procs_not_empty_or_missing") ||
    reasons.includes("outer_cgroup_counter_regressed")
  ) {
    classification = "FAIL_INCOMPLETE_OUTER_EVIDENCE_OR_DRAIN";
  } else if (reasons.includes("cgroup_not_removed")) {
    classification = "FAIL_CGROUP_CLEANUP_INCOMPLETE";
  } else if (!targetSatisfied && noInterventionClass) {
    classification = noInterventionClass;
  } else {
    classification = "FAIL_CELL2_GATE_VIOLATION";
  }

  return {
    passed,
    classification,
    kernelIntervention,
    reasons,
    outerOomDelta,
    outerOomKillDelta,
    outerMaxDelta,
  };
}

function defaultSpawnInCgroup({ cgDir, supArgs, outerDeadlineMs }) {
  return new Promise((resolve) => {
    const startNs = process.hrtime.bigint();
    const deadlineNs = BigInt(outerDeadlineMs) * 1_000_000n;
    let stdout = "";
    let stderr = "";
    let timerExpired = false;
    let settled = false;

    const child = spawn(
      "/bin/sh",
      [
        "-c",
        'echo $$ > "$1/cgroup.procs" && shift && exec "$@"',
        "_",
        cgDir,
        ...supArgs,
      ],
      { detached: true, stdio: ["ignore", "pipe", "pipe"] }
    );

    const killChildGroup = () => {
      if (!child.pid) return;
      try {
        process.kill(-child.pid, "SIGKILL");
      } catch {
        try {
          process.kill(child.pid, "SIGKILL");
        } catch {
          // Already exited.
        }
      }
    };

    const timer = setTimeout(() => {
      if (settled) return;
      timerExpired = true;
      killChildGroup();
    }, Math.max(1, outerDeadlineMs));

    child.stdout.on("data", (d) => {
      stdout += d.toString("utf8");
    });
    child.stderr.on("data", (d) => {
      stderr += d.toString("utf8");
    });

    const done = (exitCode, signal) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      killChildGroup();
      const elapsedNs = process.hrtime.bigint() - startNs;
      const wallMs = Number((Number(elapsedNs) / 1e6).toFixed(3));
      const timedOut = timerExpired || elapsedNs > deadlineNs;
      resolve({
        exitCode,
        signal,
        timedOut,
        killedByRunner: timerExpired,
        wallNs: elapsedNs.toString(),
        wallMs,
        stdout,
        stderr,
      });
    };

    child.on("error", (err) => {
      stderr += `\n[spawn error] ${err.message}\n`;
      done(null, null);
    });
    child.on("close", (code, sig) => done(code, sig));
  });
}

export async function defaultDrainAndKillCgroup(
  cgDir,
  { maxWaitMs = 2000 } = {}
) {
  const startMs = Date.now();
  let st = readCgroupDrainState(cgDir);
  let killIssued = false;
  if (!st.ok || !st.drainedEmpty) {
    if (st.ok && !st.drainedEmpty) {
      killIssued = true;
      const cgKillPath = path.join(cgDir, "cgroup.kill");
      if (fs.existsSync(cgKillPath)) {
        try {
          fs.writeFileSync(cgKillPath, "1\n", "utf8");
        } catch {
          // Fallback to per-PID SIGKILL below.
        }
      }
      for (const pid of st.procsPids) {
        try {
          process.kill(pid, "SIGKILL");
        } catch {
          // Process exited concurrently.
        }
      }
    }
    while ((!st.ok || !st.drainedEmpty) && Date.now() - startMs < maxWaitMs) {
      await new Promise((r) => setTimeout(r, 20));
      st = readCgroupDrainState(cgDir);
    }
  }
  return {
    drainedEmpty: st.ok && st.drainedEmpty,
    drainError: st.ok ? null : st.error,
    killIssued,
    remainingPids: st.procsPids,
    populatedAfterDrain: st.populated,
  };
}

function defaultAuditProof({ tproverBin, problemPath, outProof, auditTimeoutMs }) {
  return new Promise((resolve) => {
    const startNs = process.hrtime.bigint();
    let stdout = "";
    let stderr = "";
    let timedOut = false;
    let settled = false;

    const child = spawn(
      tproverBin,
      [
        "check",
        "--problem",
        problemPath,
        "--proof",
        outProof,
        "--original-root",
      ],
      { detached: true, stdio: ["ignore", "pipe", "pipe"] }
    );

    const killAudit = () => {
      if (!child.pid) return;
      try {
        process.kill(-child.pid, "SIGKILL");
      } catch {
        try {
          process.kill(child.pid, "SIGKILL");
        } catch {
          // Exited.
        }
      }
    };

    const timer = setTimeout(() => {
      if (settled) return;
      timedOut = true;
      killAudit();
    }, Math.max(1, auditTimeoutMs));

    child.stdout.on("data", (d) => {
      stdout += d.toString("utf8");
    });
    child.stderr.on("data", (d) => {
      stderr += d.toString("utf8");
    });

    const done = (exitCode, signal) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      killAudit();
      const wallMs = Number(
        (Number(process.hrtime.bigint() - startNs) / 1e6).toFixed(3)
      );
      let parsed = null;
      let parseError = null;
      if (!timedOut) {
        try {
          const line = stdout.trim().split(/\r?\n/).filter(Boolean).pop();
          parsed = line ? JSON.parse(line) : null;
        } catch (err) {
          parseError = err.message;
        }
      }
      resolve({
        wallMs,
        exitCode,
        signal,
        timedOut,
        passed: Boolean(
          !timedOut &&
            exitCode === 0 &&
            parsed &&
            parsed.passed === true &&
            parsed.errorCode === "PASS"
        ),
        errorCode: parsed ? parsed.errorCode || null : null,
        parseError,
        stderrTail: stderr.slice(-500),
      });
    };

    child.on("error", (err) => {
      stderr += `\n[audit spawn error] ${err.message}\n`;
      done(null, null);
    });
    child.on("close", (code, sig) => done(code, sig));
  });
}

export async function executeCellLifecycle(config, hooks = {}) {
  const {
    cellName,
    cgDir,
    tproverBin,
    problemPath,
    problemSha256,
    outDir,
    memoryMaxBytes,
    solverMemoryBytes,
    totalTimeMs,
    searchSoftMs,
    nodeLimit,
    maxDepth,
    expectPass,
    kernelTargetMode = "oom_or_oom_kill",
    auditTimeoutMs = 5000,
    drainTimeoutMs = 2000,
  } = config;

  const spawnCell = hooks.spawnCell || defaultSpawnInCgroup;
  const readSnapshot = hooks.readSnapshot || readOuterCgroupV2Snapshot;
  const drainGroup = hooks.drainGroup || defaultDrainAndKillCgroup;
  const auditProof = hooks.auditProof || defaultAuditProof;
  const createGroup =
    hooks.createGroup ||
    ((dir) => {
      fs.mkdirSync(dir, { recursive: false });
    });
  const configureGroup =
    hooks.configureGroup ||
    ((dir, maxBytes) => {
      fs.writeFileSync(path.join(dir, "memory.max"), `${maxBytes}\n`, "utf8");
      fs.writeFileSync(path.join(dir, "memory.swap.max"), "0\n", "utf8");
    });
  const prepareCgroup = hooks.prepareCgroup || null;
  const removeGroup =
    hooks.removeGroup ||
    ((dir) => {
      fs.rmdirSync(dir);
    });

  const outProof = path.join(outDir, `${cellName}.proof.json`);
  const outReceipt = path.join(outDir, `${cellName}.receipt.json`);
  const outRecord = path.join(outDir, `${cellName}_outer_record.json`);

  const outerRecord = {
    cellName,
    status: "INITIALIZING",
    failureStage: null,
    unexpectedError: null,
    problemPath,
    problemSha256: problemSha256 || null,
    cgroupDir: cgDir,
    cgroupCreated: false,
    configuredMemoryMaxBytes: memoryMaxBytes,
    configuredSwapMaxBytes: 0,
    totalTimeMs,
    searchSoftMs,
    auditTimeoutMs,
    memoryLimitBytes: memoryMaxBytes,
    solverMemoryBytes,
    kernelTargetMode,
    outerExitCode: null,
    outerSignal: null,
    outerTimedOut: false,
    outerKilledByRunner: false,
    outerWallNs: null,
    outerWallMs: null,
    cgroupDrainedEmpty: false,
    cgroupDrainInfo: null,
    cgroupRemoved: false,
    cgroupCleanupError: null,
    preCgroupSnapshot: null,
    postCgroupSnapshot: null,
    outerOomDelta: null,
    outerOomKillDelta: null,
    outerMaxDelta: null,
    proofExists: false,
    proofSha256: null,
    outerAuditCheck: null,
    receiptExists: false,
    receiptPath: null,
    receiptParseError: null,
    receipt: null,
    evaluation: null,
    supervisorStderrTail: "",
  };

  let cgroupCreated = false;
  const markCreated = () => {
    cgroupCreated = true;
    outerRecord.cgroupCreated = true;
  };
  try {
    outerRecord.failureStage = "preflight";
    if (prepareCgroup) {
      prepareCgroup(cgDir, memoryMaxBytes, markCreated);
      markCreated();
    } else {
      createGroup(cgDir);
      markCreated();
      configureGroup(cgDir, memoryMaxBytes);
    }

    const preSnap = readSnapshot(cgDir);
    outerRecord.preCgroupSnapshot = preSnap;
    writeJsonAtomic(outRecord, outerRecord);

    if (!preSnap || !preSnap.ok) {
      throw new Error(
        `Pre-run cgroup snapshot failed: ${preSnap ? preSnap.error : "unknown"}`
      );
    }
    if (preSnap.memoryMaxBytes !== memoryMaxBytes || preSnap.swapMaxBytes !== 0) {
      throw new Error(
        `Effective cgroup config mismatch: memory.max=${preSnap.memoryMaxBytes} (expected ${memoryMaxBytes}), swap=${preSnap.swapMaxBytes}`
      );
    }

    const innerTotalTimeMs =
      totalTimeMs >= 1000 ? totalTimeMs - 250 : Math.max(100, totalTimeMs - 50);
    const innerSoftMs = Math.min(searchSoftMs, Math.max(1, innerTotalTimeMs - 100));
    const supArgs = [
      process.execPath,
      SUPERVISOR_SCRIPT,
      "--tprover",
      tproverBin,
      "--problem",
      problemPath,
      "--out-proof",
      outProof,
      "--out-receipt",
      outReceipt,
      "--cgroup-dir",
      cgDir,
      "--total-time-ms",
      String(innerTotalTimeMs),
      "--search-soft-ms",
      String(innerSoftMs),
      "--memory-limit-bytes",
      String(memoryMaxBytes),
      "--solver-memory-bytes",
      String(solverMemoryBytes),
      "--node-limit",
      String(nodeLimit),
      "--max-depth",
      String(maxDepth),
    ];

    outerRecord.status = "RUNNING";
    outerRecord.failureStage = "spawn";
    writeJsonAtomic(outRecord, outerRecord);

    const runRes = await spawnCell({
      cgDir,
      supArgs,
      outerDeadlineMs: totalTimeMs,
    });
    outerRecord.outerExitCode = runRes.exitCode;
    outerRecord.outerSignal = runRes.signal;
    outerRecord.outerTimedOut = Boolean(runRes.timedOut);
    outerRecord.outerKilledByRunner = Boolean(runRes.killedByRunner);
    outerRecord.outerWallNs = runRes.wallNs ?? null;
    outerRecord.outerWallMs = runRes.wallMs;
    outerRecord.supervisorStderrTail = (runRes.stderr || "").slice(-1000);

    // Confirm cgroup is drained empty BEFORE taking post-run snapshot!
    outerRecord.failureStage = "drain";
    const drainInfo = await drainGroup(cgDir, { maxWaitMs: drainTimeoutMs });
    outerRecord.cgroupDrainInfo = drainInfo;
    outerRecord.cgroupDrainedEmpty = Boolean(drainInfo && drainInfo.drainedEmpty);

    outerRecord.failureStage = "post_snapshot";
    const postSnap = readSnapshot(cgDir);
    outerRecord.postCgroupSnapshot = postSnap;
    writeJsonAtomic(outRecord, outerRecord);

    // Safely inspect proof, receipt, and bounded audit check without letting
    // any parse/audit failure skip outer persistence or group cleanup.
    outerRecord.failureStage = "inspect_artifacts";
    outerRecord.proofExists = fs.existsSync(outProof);
    if (outerRecord.proofExists) {
      outerRecord.proofSha256 = sha256File(outProof);
      outerRecord.outerAuditCheck = await auditProof({
        tproverBin,
        problemPath,
        outProof,
        auditTimeoutMs,
      });
    }

    outerRecord.receiptExists = fs.existsSync(outReceipt);
    if (outerRecord.receiptExists) {
      outerRecord.receiptPath = outReceipt;
      try {
        outerRecord.receipt = JSON.parse(fs.readFileSync(outReceipt, "utf8"));
      } catch (err) {
        outerRecord.receiptParseError = err.message;
      }
    }
    outerRecord.failureStage = null;
  } catch (err) {
    outerRecord.unexpectedError = err && err.message ? err.message : String(err);
  } finally {
    if (cgroupCreated) {
      try {
        if (!outerRecord.cgroupDrainInfo) {
          const drainInfo = await drainGroup(cgDir, { maxWaitMs: drainTimeoutMs });
          outerRecord.cgroupDrainInfo = drainInfo;
          outerRecord.cgroupDrainedEmpty = Boolean(
            drainInfo && drainInfo.drainedEmpty
          );
        }
        if (!outerRecord.postCgroupSnapshot) {
          outerRecord.postCgroupSnapshot = readSnapshot(cgDir);
        }
        removeGroup(cgDir);
        outerRecord.cgroupRemoved = true;
      } catch (err) {
        outerRecord.cgroupRemoved = false;
        outerRecord.cgroupCleanupError = err.message;
      }
    }

    const evalInput = {
      ...outerRecord,
      expectedCgroupDir: cgDir,
      expectedMemoryMaxBytes: memoryMaxBytes,
    };
    const evaluation = expectPass
      ? evaluateCell1PassRecord(evalInput)
      : evaluateCell2MemLimitRecord(evalInput);

    outerRecord.evaluation = evaluation;
    outerRecord.outerOomDelta = evaluation.outerOomDelta;
    outerRecord.outerOomKillDelta = evaluation.outerOomKillDelta;
    outerRecord.outerMaxDelta = evaluation.outerMaxDelta;
    outerRecord.status = evaluation.passed ? "PASS" : "FAIL";
    writeJsonAtomic(outRecord, outerRecord);
  }

  return { outerRecord, outRecordPath: outRecord };
}

async function main() {
  const opts = parseCliArgs(process.argv.slice(2));
  if (process.platform !== "linux") {
    console.log(
      `[NOT RUN] Standalone 2-cell real Linux cgroup v2 verification requires Linux (current platform=${process.platform}).`
    );
    process.exit(3);
  }

  const realRoot = fs.realpathSync("/sys/fs/cgroup");
  const realParent = fs.realpathSync(opts.cgroupParent);
  if (realParent !== realRoot && !realParent.startsWith(realRoot + path.sep)) {
    throw new Error(`--cgroup-parent must be inside /sys/fs/cgroup: ${realParent}`);
  }

  const p042 = path.join(opts.tsumegoDir, "chao_vol1_p042.json");
  const p090 = path.join(opts.tsumegoDir, "chao_vol1_p090.json");
  const p042Sha = sha256File(p042);
  const p090Sha = sha256File(p090);

  const runId = `run_${process.pid}_${Date.now()}_${crypto
    .randomBytes(4)
    .toString("hex")}`;

  const manifest = {
    runId,
    timestampUtc: new Date().toISOString(),
    uname: execFileSync("uname", ["-a"], { encoding: "utf8" }).trim(),
    nodeVersion: process.version,
    runnerScript: THIS_FILE,
    runnerSha256: sha256File(THIS_FILE),
    supervisorScript: SUPERVISOR_SCRIPT,
    supervisorSha256: sha256File(SUPERVISOR_SCRIPT),
    tproverBin: path.resolve(opts.tproverBin),
    tproverSha256: sha256File(opts.tproverBin),
    cgroupParent: realParent,
    totalTimeMs: opts.totalTimeMs,
    auditTimeoutMs: opts.auditTimeoutMs,
    cell2KernelTarget: opts.cell2KernelTarget,
    cell1ProblemPath: p042,
    cell1ProblemSha256: p042Sha,
    cell1MemoryMaxBytes: opts.cell1MemoryMaxBytes,
    cell2ProblemPath: p090,
    cell2ProblemSha256: p090Sha,
    cell2MemoryMaxBytes: opts.cell2MemoryMaxBytes,
  };

  let runDir;
  try {
    ({ outDir: runDir } = prepareExclusiveRunDir(opts.outDir, manifest));
  } catch (err) {
    console.error(`[verify_linux_cgroup_two_cells] ${err.message}`);
    process.exit(2);
  }

  const cell1Cg = path.join(realParent, `ldprover_cell1_${runId}`);
  const cell1Res = await executeCellLifecycle({
    cellName: "cell1_p042_pass",
    cgDir: cell1Cg,
    tproverBin: opts.tproverBin,
    problemPath: p042,
    problemSha256: p042Sha,
    outDir: runDir,
    memoryMaxBytes: opts.cell1MemoryMaxBytes,
    solverMemoryBytes: Math.floor(opts.cell1MemoryMaxBytes * 0.85),
    totalTimeMs: opts.totalTimeMs,
    searchSoftMs: Math.max(1, opts.totalTimeMs - 2000),
    nodeLimit: 3500,
    maxDepth: 48,
    expectPass: true,
    kernelTargetMode: opts.cell2KernelTarget,
    auditTimeoutMs: opts.auditTimeoutMs,
  });

  const cell2Cg = path.join(realParent, `ldprover_cell2_${runId}`);
  const cell2Res = await executeCellLifecycle({
    cellName: "cell2_p090_memlimit",
    cgDir: cell2Cg,
    tproverBin: opts.tproverBin,
    problemPath: p090,
    problemSha256: p090Sha,
    outDir: runDir,
    memoryMaxBytes: opts.cell2MemoryMaxBytes,
    solverMemoryBytes: opts.cell2MemoryMaxBytes,
    totalTimeMs: opts.totalTimeMs,
    searchSoftMs: Math.max(1, opts.totalTimeMs - 500),
    nodeLimit: 1000000,
    maxDepth: 64,
    expectPass: false,
    kernelTargetMode: opts.cell2KernelTarget,
    auditTimeoutMs: opts.auditTimeoutMs,
  });

  const bothPassed =
    cell1Res.outerRecord.evaluation.passed === true &&
    cell2Res.outerRecord.evaluation.passed === true;

  const summary = {
    status: bothPassed
      ? "PASS_2_OF_2_REAL_LINUX_CELLS"
      : "FAIL_REAL_LINUX_TWO_CELLS",
    runId,
    outDir: runDir,
    cell1: {
      status: cell1Res.outerRecord.status,
      classification: cell1Res.outerRecord.evaluation.classification,
      reasons: cell1Res.outerRecord.evaluation.reasons,
      peakBytes: cell1Res.outerRecord.postCgroupSnapshot?.peakBytes ?? null,
      outerOomDelta: cell1Res.outerRecord.outerOomDelta,
      outerOomKillDelta: cell1Res.outerRecord.outerOomKillDelta,
      recordPath: cell1Res.outRecordPath,
    },
    cell2: {
      status: cell2Res.outerRecord.status,
      classification: cell2Res.outerRecord.evaluation.classification,
      kernelIntervention: cell2Res.outerRecord.evaluation.kernelIntervention,
      reasons: cell2Res.outerRecord.evaluation.reasons,
      peakBytes: cell2Res.outerRecord.postCgroupSnapshot?.peakBytes ?? null,
      outerOomDelta: cell2Res.outerRecord.outerOomDelta,
      outerOomKillDelta: cell2Res.outerRecord.outerOomKillDelta,
      outerMaxDelta: cell2Res.outerRecord.outerMaxDelta,
      recordPath: cell2Res.outRecordPath,
    },
  };
  writeJsonAtomic(path.join(runDir, "summary.json"), summary);
  console.log(JSON.stringify(summary, null, 2));

  if (!bothPassed) {
    process.exit(1);
  }
}

const isMain =
  process.argv[1] &&
  import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href;

if (isMain) {
  main().catch((err) => {
    console.error(`[verify_linux_cgroup_two_cells] ${err.stack || err.message}`);
    process.exit(1);
  });
}
