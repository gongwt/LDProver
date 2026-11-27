#!/usr/bin/env node
/**
 * Kernel-independent logic and lifecycle persistence verification suite for
 * `scripts/verify_linux_cgroup_two_cells.mjs` (R33).
 */

import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import {
  defaultDrainAndKillCgroup,
  evaluateCell1PassRecord,
  evaluateCell2MemLimitRecord,
  executeCellLifecycle,
  prepareExclusiveRunDir,
  readCgroupDrainState,
  readOuterCgroupV2Snapshot,
  sha256File,
} from "./verify_linux_cgroup_two_cells.mjs";

const THIS_DIR = path.dirname(fileURLToPath(import.meta.url));
const RUNNER_SCRIPT = path.resolve(
  THIS_DIR,
  "verify_linux_cgroup_two_cells.mjs"
);

function makeSnap(overrides = {}) {
  return {
    ok: true,
    currentBytes: 4096,
    peakBytes: 12000000,
    rawPeakBytes: 12000000,
    memoryMaxBytes: 268435456,
    swapMaxBytes: 0,
    oomCount: 0,
    oomKillCount: 0,
    maxCount: 0,
    procsPids: [],
    populated: 0,
    ...overrides,
  };
}

function makeValidCell1Input(cgDir, proofSha) {
  return {
    expectedCgroupDir: cgDir,
    expectedMemoryMaxBytes: 268435456,
    totalTimeMs: 10000,
    outerWallMs: 40,
    outerWallNs: "40000000",
    preCgroupSnapshot: makeSnap({ peakBytes: 4096, oomCount: 0, oomKillCount: 0 }),
    postCgroupSnapshot: makeSnap({ peakBytes: 28000000, oomCount: 0, oomKillCount: 0 }),
    cgroupDrainedEmpty: true,
    cgroupRemoved: true,
    outerExitCode: 0,
    outerSignal: null,
    outerTimedOut: false,
    outerKilledByRunner: false,
    proofExists: true,
    proofSha256: proofSha,
    receiptExists: true,
    receiptParseError: null,
    receipt: {
      verdict: "PROVEN_WIN",
      memoryEnforcementMode: "linux_cgroup_v2",
      cgroupPath: cgDir,
      verified: true,
      published: true,
      settlementPassed: true,
      withinTotalDeadline: true,
      meteringComplete: true,
      budgetCertified: true,
      eligibleForFormalCount: true,
      cgroupOomDelta: 0,
      cgroupOomKillDelta: 0,
      publishedSha256: proofSha,
    },
    outerAuditCheck: {
      timedOut: false,
      passed: true,
      errorCode: "PASS",
    },
    unexpectedError: null,
  };
}

function makeBaseCell2Input(cgDir) {
  return {
    kernelTargetMode: "oom_or_oom_kill",
    expectedCgroupDir: cgDir,
    expectedMemoryMaxBytes: 67108864,
    totalTimeMs: 10000,
    outerWallMs: 20,
    outerWallNs: "20000000",
    preCgroupSnapshot: makeSnap({
      memoryMaxBytes: 67108864,
      peakBytes: 4096,
      oomCount: 0,
      oomKillCount: 0,
      maxCount: 0,
    }),
    postCgroupSnapshot: makeSnap({
      memoryMaxBytes: 67108864,
      peakBytes: 67108864,
      oomCount: 0,
      oomKillCount: 0,
      maxCount: 0,
    }),
    cgroupDrainedEmpty: true,
    cgroupRemoved: true,
    outerExitCode: 0,
    outerSignal: null,
    outerTimedOut: false,
    outerKilledByRunner: false,
    proofExists: false,
    receiptExists: false,
    receiptParseError: null,
    receipt: null,
    unexpectedError: null,
  };
}

function writeMockCgroupFiles(dir, files = {}) {
  fs.mkdirSync(dir, { recursive: true });
  const defaults = {
    "memory.current": "4096\n",
    "memory.peak": "12000000\n",
    "memory.max": "268435456\n",
    "memory.swap.max": "0\n",
    "memory.events": "low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\n",
    "cgroup.procs": "",
    "cgroup.events": "populated 0\nfrozen 0\n",
  };
  for (const [k, v] of Object.entries({ ...defaults, ...files })) {
    if (v === null) continue;
    fs.writeFileSync(path.join(dir, k), v, "utf8");
  }
}

async function main() {
  const tmpRoot = fs.mkdtempSync(path.join(os.tmpdir(), "ldprover-r33-logic-"));
  let passed = 0;
  let total = 0;

  async function runCase(name, fn) {
    ++total;
    await fn();
    ++passed;
    console.log(`  [PASS] ${name}`);
  }

  try {
    // 1. All 6 R33 matrix rows + extended OOM / memory.events:max / binding / regression cases
    await runCase(
      "1. R33 decision matrix rejects soft-stop-only, isolated SIGKILL, and missing post-snapshot",
      async () => {
        const proofSha = "a".repeat(64);
        const cg1 = "/sys/fs/cgroup/ldprover_cell1_test";
        const cg2 = "/sys/fs/cgroup/ldprover_cell2_test";

        // Row 1: Cell 1 positive pass
        const r1 = evaluateCell1PassRecord(makeValidCell1Input(cg1, proofSha));
        assert.equal(r1.passed, true);
        assert.equal(r1.classification, "PASS_CERTIFIED");

        // Row 2: Cell 1 missing/failed outer postSnapshot -> REJECTED
        const r2 = evaluateCell1PassRecord({
          ...makeValidCell1Input(cg1, proofSha),
          postCgroupSnapshot: { ok: false, error: "memory.peak_missing" },
        });
        assert.equal(r2.passed, false);
        assert.ok(r2.reasons.includes("post_cgroup_snapshot_unavailable"));

        // Row 3: Cell 2 OOM=1 & OOM_KILL=1, no receipt, killed, drained+removed -> PASS
        const r3 = evaluateCell2MemLimitRecord({
          ...makeBaseCell2Input(cg2),
          outerExitCode: null,
          outerSignal: "SIGKILL",
          postCgroupSnapshot: makeSnap({
            memoryMaxBytes: 67108864,
            peakBytes: 67108864,
            oomCount: 1,
            oomKillCount: 1,
            maxCount: 3,
          }),
        });
        assert.equal(r3.passed, true);
        assert.equal(r3.classification, "PASS_KERNEL_OOM_KILL_OBSERVED");
        assert.equal(r3.outerOomDelta, 1);
        assert.equal(r3.outerOomKillDelta, 1);

        // Row 4: Cell 2 pure solver soft stop (memory_budget), 0 outer OOM deltas -> REJECTED
        const r4 = evaluateCell2MemLimitRecord({
          ...makeBaseCell2Input(cg2),
          receiptExists: true,
          receipt: {
            verdict: "UNKNOWN",
            unknownReason: "memory_budget",
            published: false,
            budgetCertified: false,
            eligibleForFormalCount: false,
            cgroupPath: cg2,
          },
        });
        assert.equal(r4.passed, false);
        assert.equal(
          r4.classification,
          "SOLVER_SOFT_STOP_ONLY_NO_KERNEL_INTERVENTION"
        );
        assert.ok(r4.reasons.includes("no_kernel_intervention_observed"));

        // Row 5: Cell 2 isolated SIGKILL, no receipt, 0 outer OOM deltas -> REJECTED
        const r5 = evaluateCell2MemLimitRecord({
          ...makeBaseCell2Input(cg2),
          outerExitCode: null,
          outerSignal: "SIGKILL",
        });
        assert.equal(r5.passed, false);
        assert.equal(
          r5.classification,
          "ISOLATED_SIGNAL_UNATTRIBUTED_NO_KERNEL_OOM"
        );

        // Row 6: Cell 2 no receipt, no signal, 0 outer OOM deltas -> REJECTED
        const r6a = evaluateCell2MemLimitRecord(makeBaseCell2Input(cg2));
        assert.equal(r6a.passed, false);
        assert.equal(
          r6a.classification,
          "EXITED_CLEANLY_WITHOUT_KERNEL_INTERVENTION"
        );
        const r6b = evaluateCell2MemLimitRecord({
          ...makeBaseCell2Input(cg2),
          outerExitCode: 1,
        });
        assert.equal(r6b.passed, false);
        assert.equal(r6b.classification, "NO_KERNEL_INTERVENTION_OBSERVED");

        // Solo oom (1,0) -> PASS; solo oom_kill (0,1) -> PASS
        assert.equal(
          evaluateCell2MemLimitRecord({
            ...makeBaseCell2Input(cg2),
            postCgroupSnapshot: makeSnap({
              memoryMaxBytes: 67108864,
              oomCount: 1,
              oomKillCount: 0,
            }),
          }).classification,
          "PASS_KERNEL_OOM_OBSERVED"
        );
        assert.equal(
          evaluateCell2MemLimitRecord({
            ...makeBaseCell2Input(cg2),
            postCgroupSnapshot: makeSnap({
              memoryMaxBytes: 67108864,
              oomCount: 0,
              oomKillCount: 1,
            }),
          }).classification,
          "PASS_KERNEL_OOM_KILL_OBSERVED"
        );

        // memory.events:max reclaim-only rejected by default, accepted when explicitly targeted
        const reclaimOnlyBase = {
          ...makeBaseCell2Input(cg2),
          postCgroupSnapshot: makeSnap({
            memoryMaxBytes: 67108864,
            oomCount: 0,
            oomKillCount: 0,
            maxCount: 4,
          }),
        };
        assert.equal(evaluateCell2MemLimitRecord(reclaimOnlyBase).passed, false);
        assert.equal(
          evaluateCell2MemLimitRecord(reclaimOnlyBase).classification,
          "NO_KERNEL_OOM_OBSERVED_RECLAIM_ONLY"
        );
        const reclaimOptIn = evaluateCell2MemLimitRecord({
          ...reclaimOnlyBase,
          kernelTargetMode: "memory_max_event",
        });
        assert.equal(reclaimOptIn.passed, true);
        assert.equal(
          reclaimOptIn.classification,
          "PASS_KERNEL_MEMORY_MAX_RECLAIM_OBSERVED"
        );

        // Group not drained / not removed / regressed / receipt mismatch / audit timeout
        assert.equal(
          evaluateCell1PassRecord({
            ...makeValidCell1Input(cg1, proofSha),
            cgroupDrainedEmpty: false,
          }).passed,
          false
        );
        assert.equal(
          evaluateCell1PassRecord({
            ...makeValidCell1Input(cg1, proofSha),
            cgroupRemoved: false,
          }).passed,
          false
        );
        assert.equal(
          evaluateCell1PassRecord({
            ...makeValidCell1Input(cg1, proofSha),
            outerAuditCheck: { timedOut: true, passed: false, errorCode: null },
          }).passed,
          false
        );
        assert.equal(
          evaluateCell1PassRecord({
            ...makeValidCell1Input(cg1, proofSha),
            receipt: {
              ...makeValidCell1Input(cg1, proofSha).receipt,
              publishedSha256: "b".repeat(64),
            },
          }).passed,
          false
        );
        assert.equal(
          evaluateCell2MemLimitRecord({
            ...makeBaseCell2Input(cg2),
            preCgroupSnapshot: makeSnap({ memoryMaxBytes: 67108864, oomCount: 3 }),
            postCgroupSnapshot: makeSnap({
              memoryMaxBytes: 67108864,
              oomCount: 2,
              oomKillCount: 1,
            }),
          }).passed,
          false
        );
      }
    );

    // 2. Strict readOuterCgroupV2Snapshot parser tests
    await runCase(
      "2. readOuterCgroupV2Snapshot validates oom, oom_kill, max, limit, swap and procs strictly",
      async () => {
        const snapDir = path.join(tmpRoot, "snaps");
        const dOk = path.join(snapDir, "ok");
        writeMockCgroupFiles(dOk, {
          "memory.events": "low 0\nhigh 1\nmax 2\noom 3\noom_kill 1\n",
          "cgroup.procs": "101\n102\n",
          "cgroup.events": "populated 1\nfrozen 0\n",
        });
        const sOk = readOuterCgroupV2Snapshot(dOk);
        assert.equal(sOk.ok, true);
        assert.equal(sOk.oomCount, 3);
        assert.equal(sOk.oomKillCount, 1);
        assert.equal(sOk.maxCount, 2);
        assert.equal(sOk.memoryMaxBytes, 268435456);
        assert.equal(sOk.swapMaxBytes, 0);
        assert.deepEqual(sOk.procsPids, [101, 102]);
        assert.equal(sOk.populated, 1);

        for (const [sub, ov] of [
          ["missing_max_ev", { "memory.events": "low 0\nhigh 0\noom 0\noom_kill 0\n" }],
          ["missing_oom_kill", { "memory.events": "max 0\noom 0\n" }],
          ["missing_oom", { "memory.events": "max 0\noom_kill 0\n" }],
          ["unlimited_max", { "memory.max": "max\n" }],
        ]) {
          const d = path.join(snapDir, sub);
          writeMockCgroupFiles(d, ov);
          assert.equal(readOuterCgroupV2Snapshot(d).ok, false);
        }
      }
    );

    // 3. Always-persist lifecycle, drain-before-post-snapshot ordering, and failure persistence
    await runCase(
      "3. executeCellLifecycle drains before post-snapshot and persists outer_record.json on every failure path",
      async () => {
        const lcBase = path.join(tmpRoot, "lifecycle");
        const dummyBin = "/usr/bin/true";
        const dummyProb = path.join(lcBase, "prob.json");
        fs.mkdirSync(lcBase, { recursive: true });
        fs.writeFileSync(dummyProb, '{"id":"p042"}\n', "utf8");
        const probSha = sha256File(dummyProb);

        // 3a. Valid Cell 1 pass persists PASS record & order pre->spawn->drain->post->remove
        const run3a = path.join(lcBase, "r3a");
        fs.mkdirSync(run3a, { recursive: true });
        const proof3a = path.join(run3a, "cell1_p042_pass.proof.json");
        const receipt3a = path.join(run3a, "cell1_p042_pass.receipt.json");
        const cg3a = "/sys/fs/cgroup/cg3a";
        const events3a = [];
        const res3a = await executeCellLifecycle(
          {
            cellName: "cell1_p042_pass",
            cgDir: cg3a,
            tproverBin: dummyBin,
            problemPath: dummyProb,
            problemSha256: probSha,
            outDir: run3a,
            memoryMaxBytes: 268435456,
            solverMemoryBytes: 220000000,
            totalTimeMs: 5000,
            searchSoftMs: 4000,
            nodeLimit: 3500,
            maxDepth: 48,
            expectPass: true,
          },
          {
            prepareCgroup: () => events3a.push("prepare"),
            spawnCell: async () => {
              events3a.push("spawn");
              fs.writeFileSync(proof3a, '{"proof":1}\n', "utf8");
              const pSha = sha256File(proof3a);
              fs.writeFileSync(
                receipt3a,
                JSON.stringify({
                  verdict: "PROVEN_WIN",
                  memoryEnforcementMode: "linux_cgroup_v2",
                  cgroupPath: cg3a,
                  verified: true,
                  published: true,
                  settlementPassed: true,
                  withinTotalDeadline: true,
                  meteringComplete: true,
                  budgetCertified: true,
                  eligibleForFormalCount: true,
                  cgroupOomDelta: 0,
                  cgroupOomKillDelta: 0,
                  publishedSha256: pSha,
                }),
                "utf8"
              );
              return { exitCode: 0, signal: null, timedOut: false, killedByRunner: false, wallMs: 50, stderr: "" };
            },
            drainGroup: async () => {
              events3a.push("drain");
              return { drainedEmpty: true, killIssued: false, remainingPids: [], populatedAfterDrain: 0 };
            },
            readSnapshot: () => {
              events3a.push("snapshot");
              return makeSnap({ peakBytes: 20000000 });
            },
            auditProof: async () => ({
              wallMs: 10,
              exitCode: 0,
              signal: null,
              timedOut: false,
              passed: true,
              errorCode: "PASS",
            }),
            removeGroup: () => events3a.push("remove"),
          }
        );
        assert.deepEqual(events3a, ["prepare", "snapshot", "spawn", "drain", "snapshot", "remove"]);
        assert.equal(res3a.outerRecord.status, "PASS");
        assert.equal(fs.existsSync(res3a.outRecordPath), true);
        const persisted3a = JSON.parse(fs.readFileSync(res3a.outRecordPath, "utf8"));
        assert.equal(persisted3a.evaluation.passed, true);

        // 3b. Corrupt receipt JSON does NOT lose outer_record.json and rejects Cell 1
        const run3b = path.join(lcBase, "r3b");
        fs.mkdirSync(run3b, { recursive: true });
        const proof3b = path.join(run3b, "cell1_p042_pass.proof.json");
        const receipt3b = path.join(run3b, "cell1_p042_pass.receipt.json");
        const res3b = await executeCellLifecycle(
          {
            cellName: "cell1_p042_pass",
            cgDir: "/sys/fs/cgroup/cg3b",
            tproverBin: dummyBin,
            problemPath: dummyProb,
            problemSha256: probSha,
            outDir: run3b,
            memoryMaxBytes: 268435456,
            solverMemoryBytes: 220000000,
            totalTimeMs: 5000,
            searchSoftMs: 4000,
            nodeLimit: 3500,
            maxDepth: 48,
            expectPass: true,
          },
          {
            prepareCgroup: () => {},
            spawnCell: async () => {
              fs.writeFileSync(proof3b, '{"proof":1}\n', "utf8");
              fs.writeFileSync(receipt3b, "{not valid json", "utf8");
              return { exitCode: 0, signal: null, timedOut: false, killedByRunner: false, wallMs: 50, stderr: "" };
            },
            drainGroup: async () => ({ drainedEmpty: true, killIssued: false, remainingPids: [], populatedAfterDrain: 0 }),
            readSnapshot: () => makeSnap({ peakBytes: 20000000 }),
            auditProof: async () => ({ wallMs: 10, exitCode: 0, signal: null, timedOut: false, passed: true, errorCode: "PASS" }),
            removeGroup: () => {},
          }
        );
        assert.equal(res3b.outerRecord.status, "FAIL");
        assert.ok(res3b.outerRecord.receiptParseError);
        const persisted3b = JSON.parse(fs.readFileSync(res3b.outRecordPath, "utf8"));
        assert.equal(persisted3b.status, "FAIL");
        assert.ok(persisted3b.postCgroupSnapshot.ok);

        // 3c. Audit timeout + unremovable cgroup both fail and still write outer_record.json
        const run3c = path.join(lcBase, "r3c");
        fs.mkdirSync(run3c, { recursive: true });
        const proof3c = path.join(run3c, "cell1_p042_pass.proof.json");
        const res3c = await executeCellLifecycle(
          {
            cellName: "cell1_p042_pass",
            cgDir: "/sys/fs/cgroup/cg3c",
            tproverBin: dummyBin,
            problemPath: dummyProb,
            problemSha256: probSha,
            outDir: run3c,
            memoryMaxBytes: 268435456,
            solverMemoryBytes: 220000000,
            totalTimeMs: 5000,
            searchSoftMs: 4000,
            nodeLimit: 3500,
            maxDepth: 48,
            expectPass: true,
          },
          {
            prepareCgroup: () => {},
            spawnCell: async () => {
              fs.writeFileSync(proof3c, '{"proof":1}\n', "utf8");
              return { exitCode: 0, signal: null, timedOut: true, killedByRunner: true, wallMs: 5000, stderr: "" };
            },
            drainGroup: async () => ({ drainedEmpty: true, killIssued: true, remainingPids: [], populatedAfterDrain: 0 }),
            readSnapshot: () => makeSnap({ peakBytes: 20000000 }),
            auditProof: async () => ({ wallMs: 5000, exitCode: null, signal: "SIGKILL", timedOut: true, passed: false, errorCode: null }),
            removeGroup: () => {
              throw new Error("EBUSY");
            },
          }
        );
        const persisted3c = JSON.parse(fs.readFileSync(res3c.outRecordPath, "utf8"));
        assert.equal(persisted3c.status, "FAIL");
        assert.equal(persisted3c.outerAuditCheck.timedOut, true);
        assert.equal(persisted3c.cgroupRemoved, false);
        assert.equal(persisted3c.cgroupCleanupError, "EBUSY");
        assert.equal(persisted3c.evaluation.passed, false);

        // 3d. No-receipt OOM kill negative cell persists PASS outer_record.json
        const run3d = path.join(lcBase, "r3d");
        fs.mkdirSync(run3d, { recursive: true });
        let snapIdx = 0;
        const res3d = await executeCellLifecycle(
          {
            cellName: "cell2_p090_memlimit",
            cgDir: "/sys/fs/cgroup/cg3d",
            tproverBin: dummyBin,
            problemPath: dummyProb,
            problemSha256: probSha,
            outDir: run3d,
            memoryMaxBytes: 67108864,
            solverMemoryBytes: 67108864,
            totalTimeMs: 5000,
            searchSoftMs: 4500,
            nodeLimit: 1000000,
            maxDepth: 64,
            expectPass: false,
          },
          {
            prepareCgroup: () => {},
            spawnCell: async () => ({
              exitCode: null,
              signal: "SIGKILL",
              timedOut: false,
              killedByRunner: false,
              wallMs: 420,
              stderr: "",
            }),
            drainGroup: async () => ({ drainedEmpty: true, killIssued: false, remainingPids: [], populatedAfterDrain: 0 }),
            readSnapshot: () =>
              snapIdx++ === 0
                ? makeSnap({ memoryMaxBytes: 67108864, peakBytes: 4096, oomCount: 0, oomKillCount: 0 })
                : makeSnap({ memoryMaxBytes: 67108864, peakBytes: 67108864, oomCount: 1, oomKillCount: 1, maxCount: 2 }),
            removeGroup: () => {},
          }
        );
        assert.equal(res3d.outerRecord.status, "PASS");
        assert.equal(
          res3d.outerRecord.evaluation.classification,
          "PASS_KERNEL_OOM_KILL_OBSERVED"
        );
        assert.equal(res3d.outerRecord.receiptExists, false);
        assert.equal(fs.existsSync(res3d.outRecordPath), true);
      }
    );

    // 4. Exclusive per-run output directory isolation (R33 P2)
    await runCase(
      "4. prepareExclusiveRunDir rejects reused or pre-populated directories without touching existing files",
      async () => {
        const dirA = path.join(tmpRoot, "run_dir_a");
        const { manifestPath } = prepareExclusiveRunDir(dirA, { runId: "a1" });
        assert.equal(fs.existsSync(manifestPath), true);

        const staleReceipt = path.join(dirA, "cell1_p042_pass.receipt.json");
        fs.writeFileSync(staleReceipt, '{"stale":true}\n', "utf8");
        const staleSha = sha256File(staleReceipt);

        assert.throws(() => prepareExclusiveRunDir(dirA, { runId: "a2" }), /empty/);
        assert.equal(sha256File(staleReceipt), staleSha);
      }
    );

    // 5. Non-Linux CLI guard exits cleanly with code 3 without creating outDir
    await runCase(
      "5. CLI guard exits with code 3 on non-Linux without creating --out-dir",
      async () => {
        if (process.platform === "linux") return;
        const untouchedDir = path.join(tmpRoot, "must_not_exist");
        const res = spawnSync(
          process.execPath,
          [
            RUNNER_SCRIPT,
            "--tprover",
            "/usr/bin/true",
            "--cgroup-parent",
            "/sys/fs/cgroup",
            "--out-dir",
            untouchedDir,
          ],
          { encoding: "utf8" }
        );
        assert.equal(res.status, 3);
        assert.ok(res.stdout.includes("[NOT RUN]"));
        assert.equal(fs.existsSync(untouchedDir), false);
      }
    );

    // 6. R34 paired controls (timeout+OOM, missing cgroup.events/populated=null, wall-time overrun, partial-create ownership, non-PASS failure class)
    await runCase(
      "6. R34 paired controls reject timeout+OOM, missing drain populated, wall-time overrun, and fix partial-create cleanup & failure class",
      async () => {
        const proofSha = "a".repeat(64);
        const cg1 = "/sys/fs/cgroup/ldprover_cell1_r34";
        const cg2 = "/sys/fs/cgroup/ldprover_cell2_r34";

        // 6a. Negative normal control -> PASS
        const ctrlNeg = evaluateCell2MemLimitRecord({
          ...makeBaseCell2Input(cg2),
          outerExitCode: null,
          outerSignal: "SIGKILL",
          postCgroupSnapshot: makeSnap({
            memoryMaxBytes: 67108864,
            peakBytes: 67108864,
            oomCount: 1,
            oomKillCount: 1,
            populated: 0,
          }),
        });
        assert.equal(ctrlNeg.passed, true);
        assert.equal(ctrlNeg.classification, "PASS_KERNEL_OOM_KILL_OBSERVED");

        // 6b. Negative OOM kill + outerTimedOut + outerWallMs=10025 at 10000ms limit -> FAIL while preserving kernelIntervention
        const timeoutWithOom = evaluateCell2MemLimitRecord({
          ...makeBaseCell2Input(cg2),
          outerExitCode: null,
          outerSignal: "SIGKILL",
          outerTimedOut: true,
          outerKilledByRunner: true,
          outerWallMs: 10025,
          outerWallNs: "10025000000",
          postCgroupSnapshot: makeSnap({
            memoryMaxBytes: 67108864,
            peakBytes: 67108864,
            oomCount: 1,
            oomKillCount: 1,
            populated: 0,
          }),
        });
        assert.equal(timeoutWithOom.passed, false);
        assert.equal(timeoutWithOom.kernelIntervention, "cgroup_oom_kill");
        assert.equal(timeoutWithOom.classification.startsWith("PASS_"), false);
        assert.ok(timeoutWithOom.reasons.includes("outer_deadline_timed_out"));
        assert.ok(timeoutWithOom.reasons.includes("outer_killed_by_runner"));
        assert.ok(timeoutWithOom.reasons.includes("outer_wall_time_exceeded"));

        // 6c. Positive wall-time overrun (outerWallMs=10025 even with outerTimedOut=false) -> FAIL
        const cell1OverWall = evaluateCell1PassRecord({
          ...makeValidCell1Input(cg1, proofSha),
          outerWallMs: 10025,
          outerWallNs: "10025000000",
          outerTimedOut: false,
        });
        assert.equal(cell1OverWall.passed, false);
        assert.ok(cell1OverWall.reasons.includes("outer_wall_time_exceeded"));
        assert.equal(cell1OverWall.classification, "FAIL_CELL1");

        // 6d. Positive direct call with populated=null -> FAIL
        const cell1NullPop = evaluateCell1PassRecord({
          ...makeValidCell1Input(cg1, proofSha),
          postCgroupSnapshot: makeSnap({ peakBytes: 28000000, populated: null }),
        });
        assert.equal(cell1NullPop.passed, false);
        assert.ok(cell1NullPop.reasons.includes("post_cgroup_populated_not_zero"));

        // 6e. Negative OOM kill + cgroupDrainedEmpty=false -> FAIL with non-PASS_ classification
        const negUndrained = evaluateCell2MemLimitRecord({
          ...makeBaseCell2Input(cg2),
          cgroupDrainedEmpty: false,
          postCgroupSnapshot: makeSnap({
            memoryMaxBytes: 67108864,
            oomCount: 1,
            oomKillCount: 1,
            populated: 1,
          }),
        });
        assert.equal(negUndrained.passed, false);
        assert.equal(negUndrained.kernelIntervention, "cgroup_oom_kill");
        assert.equal(negUndrained.classification.startsWith("PASS_"), false);

        // 6f. End-to-end lifecycle with REAL default readOuterCgroupV2Snapshot + defaultDrainAndKillCgroup:
        // deleting `cgroup.events` mid-run must fail drain and snapshot -> FAIL + non-PASS_ classification
        const r34Root = path.join(tmpRoot, "r34_e2e");
        const dummyProb = path.join(r34Root, "prob.json");
        fs.mkdirSync(r34Root, { recursive: true });
        fs.writeFileSync(dummyProb, '{"id":"p090"}\n', "utf8");
        const probSha = sha256File(dummyProb);

        const outNoEvents = path.join(r34Root, "out_no_events");
        const cgNoEvents = path.join(r34Root, "cg_no_events");
        fs.mkdirSync(outNoEvents, { recursive: true });
        const resNoEvents = await executeCellLifecycle(
          {
            cellName: "cell2_p090_memlimit",
            cgDir: cgNoEvents,
            tproverBin: "/usr/bin/true",
            problemPath: dummyProb,
            problemSha256: probSha,
            outDir: outNoEvents,
            memoryMaxBytes: 67108864,
            solverMemoryBytes: 67108864,
            totalTimeMs: 10000,
            searchSoftMs: 9500,
            nodeLimit: 1000000,
            maxDepth: 64,
            expectPass: false,
            drainTimeoutMs: 60,
          },
          {
            createGroup: (dir) => {
              writeMockCgroupFiles(dir, {
                "memory.max": "67108864\n",
                "memory.peak": "4096\n",
              });
            },
            spawnCell: async ({ cgDir }) => {
              writeMockCgroupFiles(cgDir, {
                "memory.max": "67108864\n",
                "memory.peak": "67108864\n",
                "memory.events": "low 0\nhigh 0\nmax 1\noom 1\noom_kill 1\n",
              });
              fs.rmSync(path.join(cgDir, "cgroup.events"), { force: true });
              return {
                exitCode: null,
                signal: "SIGKILL",
                timedOut: false,
                killedByRunner: false,
                wallNs: "20000000",
                wallMs: 20,
                stderr: "",
              };
            },
            drainGroup: defaultDrainAndKillCgroup,
            readSnapshot: readOuterCgroupV2Snapshot,
            removeGroup: (dir) => fs.rmSync(dir, { recursive: true, force: true }),
          }
        );
        assert.equal(resNoEvents.outerRecord.status, "FAIL");
        assert.equal(resNoEvents.outerRecord.cgroupDrainedEmpty, false);
        assert.equal(
          resNoEvents.outerRecord.cgroupDrainInfo.drainError,
          "cgroup.events_missing"
        );
        assert.equal(resNoEvents.outerRecord.postCgroupSnapshot.ok, false);
        assert.equal(resNoEvents.outerRecord.evaluation.passed, false);
        assert.equal(
          resNoEvents.outerRecord.evaluation.classification.startsWith("PASS_"),
          false
        );
        assert.equal(
          readCgroupDrainState(path.join(r34Root, "nonexistent")).ok,
          false
        );

        // 6g. Partial cgroup creation: directory created, configureGroup throws -> newly created dir MUST be removed
        const outPartial = path.join(r34Root, "out_partial");
        const cgPartial = path.join(r34Root, "cg_partial");
        fs.mkdirSync(outPartial, { recursive: true });
        const resPartial = await executeCellLifecycle(
          {
            cellName: "cell2_p090_memlimit",
            cgDir: cgPartial,
            tproverBin: "/usr/bin/true",
            problemPath: dummyProb,
            problemSha256: probSha,
            outDir: outPartial,
            memoryMaxBytes: 67108864,
            solverMemoryBytes: 67108864,
            totalTimeMs: 10000,
            searchSoftMs: 9500,
            nodeLimit: 1000000,
            maxDepth: 64,
            expectPass: false,
          },
          {
            createGroup: (dir) => fs.mkdirSync(dir, { recursive: false }),
            configureGroup: () => {
              throw new Error("EACCES writing memory.max");
            },
            removeGroup: (dir) => fs.rmdirSync(dir),
          }
        );
        assert.equal(fs.existsSync(cgPartial), false);
        assert.equal(resPartial.outerRecord.status, "FAIL");
        assert.equal(resPartial.outerRecord.failureStage, "preflight");
        assert.equal(resPartial.outerRecord.cgroupCreated, true);
        assert.equal(resPartial.outerRecord.cgroupRemoved, true);

        // 6h. Pre-existing cgroup directory: createGroup EEXIST -> pre-existing dir & sentinel MUST NOT be removed
        const outPreexist = path.join(r34Root, "out_preexist");
        const cgPreexist = path.join(r34Root, "cg_preexist");
        fs.mkdirSync(outPreexist, { recursive: true });
        fs.mkdirSync(cgPreexist, { recursive: true });
        const cgSentinel = path.join(cgPreexist, "keep_me.txt");
        fs.writeFileSync(cgSentinel, "preexisting\n", "utf8");
        const resPreexist = await executeCellLifecycle(
          {
            cellName: "cell2_p090_memlimit",
            cgDir: cgPreexist,
            tproverBin: "/usr/bin/true",
            problemPath: dummyProb,
            problemSha256: probSha,
            outDir: outPreexist,
            memoryMaxBytes: 67108864,
            solverMemoryBytes: 67108864,
            totalTimeMs: 10000,
            searchSoftMs: 9500,
            nodeLimit: 1000000,
            maxDepth: 64,
            expectPass: false,
          },
          {}
        );
        assert.equal(resPreexist.outerRecord.status, "FAIL");
        assert.equal(resPreexist.outerRecord.cgroupCreated, false);
        assert.equal(resPreexist.outerRecord.cgroupRemoved, false);
        assert.equal(fs.existsSync(cgSentinel), true);
        assert.equal(fs.readFileSync(cgSentinel, "utf8"), "preexisting\n");
      }
    );

    console.log(
      `\n========================================\nLinux Two-Cell Logic Verification: ${passed}/${total} passed, 0 failed.\n========================================`
    );
  } finally {
    fs.rmSync(tmpRoot, { recursive: true, force: true });
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
