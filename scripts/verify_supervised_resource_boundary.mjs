#!/usr/bin/env node
/**
 * Fault-injection, resource-boundary, publish-contract, and path-identity
 * verification harness for `scripts/supervised_solve.mjs` (Task Card 1a).
 */

import assert from "node:assert/strict";
import crypto from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { execFileSync, spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import {
  evaluateCertificationDecision,
  evaluateCgroupOomProgress,
  listProcessGroupMembers,
  readCgroupV2Snapshot,
  runSupervisedSolve,
} from "./supervised_solve.mjs";

const SUPERVISOR_SCRIPT = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  "supervised_solve.mjs"
);

function parseArgs(argv) {
  let tproverBin = "";
  let tsumegoDir = "public/tsumego";
  for (let i = 0; i < argv.length; ++i) {
    if (argv[i] === "--tprover" && i + 1 < argv.length) {
      tproverBin = argv[++i];
    } else if (argv[i] === "--tsumego-dir" && i + 1 < argv.length) {
      tsumegoDir = argv[++i];
    }
  }
  if (!tproverBin) {
    throw new Error(
      "Usage: verify_supervised_resource_boundary.mjs --tprover <bin> [--tsumego-dir public/tsumego]"
    );
  }
  return { tproverBin, tsumegoDir };
}

function sha256File(filePath) {
  return crypto.createHash("sha256").update(fs.readFileSync(filePath)).digest("hex");
}

function runSupervisorCli(args) {
  return spawnSync(process.execPath, [SUPERVISOR_SCRIPT, ...args], {
    encoding: "utf8",
  });
}

function createMockCgroupDir(baseDir, name, overrides = {}) {
  const dir = path.join(baseDir, name);
  fs.mkdirSync(dir, { recursive: true });
  const defaults = {
    "memory.max": "2000000000\n",
    "memory.swap.max": "0\n",
    "memory.current": "10000000\n",
    "memory.peak": "12000000\n",
    "memory.events": "low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\n",
    "cgroup.procs": `${process.pid}\n`,
  };
  const merged = { ...defaults, ...overrides };
  for (const [k, v] of Object.entries(merged)) {
    if (v === null) continue;
    fs.writeFileSync(path.join(dir, k), v, "utf8");
  }
  return dir;
}

async function main() {
  const { tproverBin, tsumegoDir } = parseArgs(process.argv.slice(2));
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "ldprover-tc1a-ver-"));
  let passed = 0;
  let total = 0;

  async function runCase(name, fn) {
    ++total;
    await fn();
    ++passed;
    console.log(`  [PASS] ${name}`);
  }

  try {
    const p042 = path.join(tsumegoDir, "chao_vol1_p042.json");
    const p031 = path.join(tsumegoDir, "chao_vol1_p031.json");
    const p060 = path.join(tsumegoDir, "chao_vol1_p060.json");
    const p090 = path.join(tsumegoDir, "chao_vol1_p090.json");

    // 1. Valid end-to-end solve + independent check + atomic publish (with non-null checkMaxRssBytes)
    await runCase(
      "1. valid end-to-end p042 & p031 solve + independent check + publish + non-null RSS",
      async () => {
        for (const [label, prob, expNodes] of [
          ["p042", p042, 329],
          ["p031", p031, 1908],
        ]) {
          const outProof = path.join(tmpDir, `${label}.proof.json`);
          const outReceipt = path.join(tmpDir, `${label}.receipt.json`);
          const r = await runSupervisedSolve({
            tproverBin,
            problemPath: prob,
            outProofPath: outProof,
            outReceiptPath: outReceipt,
            totalTimeMs: 15000,
            searchSoftMs: 12000,
            memoryLimitBytes: 2000000000,
            solverMemoryBytes: 1700000000,
            nodeLimit: 1000000,
            maxDepth: 48,
          });
          assert.equal(r.verdict, "PROVEN_WIN");
          assert.equal(r.proofRootStatus, "PROVEN_WIN");
          assert.equal(r.stage, "done");
          assert.equal(r.unknownReason, "none");
          assert.equal(r.stopAttribution, "proven_verified_published");
          assert.equal(r.verified, true);
          assert.equal(r.published, true);
          assert.equal(r.settlementPassed, true);
          assert.equal(r.withinTotalDeadline, true);
          assert.equal(r.publishedProofPath, path.resolve(outProof));
          assert.equal(r.checkerCode, "PASS");
          assert.equal(r.numNodes, expNodes);
          assert.equal(r.meteringComplete, true);
          assert.equal(r.stagingCleaned, true);
          assert.ok(typeof r.solveMaxRssBytes === "number" && r.solveMaxRssBytes > 0);
          assert.ok(
            typeof r.checkMaxRssBytes === "number" && r.checkMaxRssBytes > 0,
            `Expected positive checkMaxRssBytes, got ${r.checkMaxRssBytes}`
          );
          assert.ok(typeof r.peakRssBytes === "number" && r.peakRssBytes >= r.checkMaxRssBytes);
          assert.ok(typeof r.publishMs === "number" && r.publishMs >= 0);
          assert.ok(typeof r.cleanupMs === "number" && r.cleanupMs >= 0);
          assert.equal(r.publishedSha256, r.verifiedStagingSha256);
          assert.equal(r.publishedSha256, sha256File(outProof));
          if (process.platform !== "linux") {
            assert.equal(r.budgetCertified, false);
            assert.equal(r.eligibleForFormalCount, false);
            assert.equal(r.memoryEnforcementMode, "macos_rss_polling_advisory");
          }
          const chk = JSON.parse(
            execFileSync(
              tproverBin,
              ["check", "--problem", prob, "--proof", outProof, "--original-root"],
              { encoding: "utf8" }
            )
          );
          assert.equal(chk.passed, true);
          assert.equal(chk.errorCode, "PASS");
        }
      }
    );

    // 2. Valid p042 omitting --out-proof must set verified=true, published=false
    await runCase(
      "2. valid p042 omitting --out-proof marks verified=true, published=false, ineligible",
      async () => {
        const outReceipt = path.join(tmpDir, "no_out_proof.receipt.json");
        const r = await runSupervisedSolve({
          tproverBin,
          problemPath: p042,
          outReceiptPath: outReceipt,
          totalTimeMs: 15000,
          searchSoftMs: 12000,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 3500,
          maxDepth: 48,
        });
        assert.equal(r.verdict, "PROVEN_WIN");
        assert.equal(r.proofRootStatus, "PROVEN_WIN");
        assert.equal(r.verified, true);
        assert.equal(r.published, false);
        assert.equal(r.settlementPassed, true);
        assert.equal(r.withinTotalDeadline, true);
        assert.equal(r.publishedProofPath, null);
        assert.equal(r.publishedSha256, null);
        assert.equal(r.checkerCode, "PASS");
        assert.equal(r.stopAttribution, "proven_verified_unpublished");
        assert.equal(r.eligibleForFormalCount, false);
        assert.equal(r.formalCountIneligibleReason, "no_out_proof_path");
        assert.ok(typeof r.checkMaxRssBytes === "number" && r.checkMaxRssBytes > 0);
        assert.equal(r.stagingCleaned, true);
      }
    );

    // 3. Cooperative search soft-timeout expiry
    await runCase(
      "3. cooperative search soft timeout stops p060 cleanly with explicit attribution and nulls",
      async () => {
        const outProof = path.join(tmpDir, "soft_timeout.proof.json");
        const r = await runSupervisedSolve({
          tproverBin,
          problemPath: p060,
          outProofPath: outProof,
          totalTimeMs: 5000,
          searchSoftMs: 50,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 10000000,
          maxDepth: 64,
        });
        assert.equal(r.verdict, "UNKNOWN");
        assert.equal(r.stage, "solve");
        assert.equal(r.unknownReason, "timeout");
        assert.equal(r.stopAttribution, "solver_soft_timeout");
        assert.equal(r.verified, false);
        assert.equal(r.published, false);
        assert.ok(typeof r.numNodes === "number" && r.numNodes > 0);
        assert.equal(r.checkMaxRssBytes, null);
        assert.equal(r.checkMs, null);
        assert.equal(r.publishMs, null);
        assert.equal(r.stagingCleaned, true);
        assert.equal(fs.existsSync(outProof), false);
      }
    );

    // 4. Hard wall-clock kill during search + POSITIVE CONTROL PGID PROBE
    await runCase(
      "4. hard deadline SIGKILLs solve process group with verified positive-control PGID probe",
      async () => {
        const outProof = path.join(tmpDir, "hard_timeout.proof.json");
        let probedPgid = null;
        let positiveControlMembers = 0;
        const r = await runSupervisedSolve({
          tproverBin,
          problemPath: p060,
          outProofPath: outProof,
          totalTimeMs: 180,
          searchSoftMs: 30000,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 10000000,
          maxDepth: 64,
          onStageSpawn: ({ stage, pgid }) => {
            if (stage === "solve") {
              probedPgid = pgid;
              const snap = listProcessGroupMembers(pgid);
              positiveControlMembers = snap.members.length;
            }
          },
        });
        assert.ok(probedPgid && probedPgid > 0);
        assert.ok(
          positiveControlMembers >= 1,
          `Positive control failed: expected >=1 live process in pgid ${probedPgid}, got ${positiveControlMembers}`
        );
        assert.equal(r.verdict, "UNKNOWN");
        assert.equal(r.stage, "solve");
        assert.equal(r.unknownReason, "hard_timeout");
        assert.equal(r.stopAttribution, "supervisor_hard_timeout_kill");
        assert.equal(r.solveSignal, "SIGKILL");
        assert.equal(r.verified, false);
        assert.equal(r.published, false);
        assert.equal(r.stagingCleaned, true);
        assert.equal(fs.existsSync(outProof), false);
        const postSnap = listProcessGroupMembers(probedPgid);
        assert.equal(
          postSnap.members.length,
          0,
          `Expected 0 remaining members in pgid ${probedPgid}, found ${postSnap.members.length}`
        );
      }
    );

    // 5. Hard deadline during independent check stage + POSITIVE CONTROL PGID PROBE
    await runCase(
      "5. hard deadline during independent check SIGKILLs check PGID and withholds publish",
      async () => {
        const outProof = path.join(tmpDir, "checker_timeout.proof.json");
        let checkPgid = null;
        let checkLiveSeen = 0;
        const r = await runSupervisedSolve({
          tproverBin,
          problemPath: p042,
          outProofPath: outProof,
          totalTimeMs: 700,
          searchSoftMs: 600,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 3500,
          maxDepth: 48,
          faultCheckDelayMs: 1500,
          onStageSpawn: ({ stage, pgid }) => {
            if (stage === "check") {
              checkPgid = pgid;
              const snap = listProcessGroupMembers(pgid);
              checkLiveSeen = snap.members.length;
            }
          },
        });
        assert.ok(checkPgid && checkPgid > 0);
        assert.ok(
          checkLiveSeen >= 1,
          `Positive control failed for check pgid ${checkPgid}`
        );
        assert.equal(r.verdict, "UNKNOWN");
        assert.equal(r.stage, "check");
        assert.equal(r.unknownReason, "checker_timeout");
        assert.equal(r.stopAttribution, "checker_hard_timeout_kill");
        assert.equal(r.verified, false);
        assert.equal(r.published, false);
        assert.equal(r.stagingCleaned, true);
        assert.equal(fs.existsSync(outProof), false);
        assert.equal(listProcessGroupMembers(checkPgid).members.length, 0);
      }
    );

    // 6. Publish-stage deadline expiry preserves pre-existing destination file bytes
    await runCase(
      "6. publish-stage deadline expiry returns publish_timeout and preserves pre-existing proof",
      async () => {
        const outProof = path.join(tmpDir, "publish_sentinel.proof.json");
        const sentinel = JSON.stringify({ sentinel: "DO_NOT_OVERWRITE" }) + "\n";
        fs.writeFileSync(outProof, sentinel, { mode: 0o600 });
        const sentinelSha = sha256File(outProof);

        const r = await runSupervisedSolve({
          tproverBin,
          problemPath: p042,
          outProofPath: outProof,
          totalTimeMs: 1500,
          searchSoftMs: 1200,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 3500,
          maxDepth: 48,
          faultPublishDelayMs: 1600,
        });
        assert.equal(r.verdict, "UNKNOWN");
        assert.equal(r.stage, "publish");
        assert.equal(r.unknownReason, "publish_timeout");
        assert.equal(r.stopAttribution, "publish_timeout");
        assert.equal(r.verified, true);
        assert.equal(r.published, false);
        assert.equal(r.publishedSha256, null);
        assert.equal(r.stagingCleaned, true);
        assert.equal(sha256File(outProof), sentinelSha);
        assert.equal(fs.readFileSync(outProof, "utf8"), sentinel);
      }
    );

    // 7. Tight memory budget stops cleanly (both soft memory budget & hard RSS cap)
    await runCase(
      "7. low memory budgets trigger solver_soft_memory_budget and rss_limit with preserved metadata",
      async () => {
        // 7a: Cooperative solver soft budget stop
        const softOut = path.join(tmpDir, "mem_soft.proof.json");
        const rSoft = await runSupervisedSolve({
          tproverBin,
          problemPath: p090,
          outProofPath: softOut,
          totalTimeMs: 10000,
          searchSoftMs: 8000,
          memoryLimitBytes: 500000000,
          solverMemoryBytes: 4000000,
          nodeLimit: 1000000,
          maxDepth: 64,
        });
        assert.equal(rSoft.verdict, "UNKNOWN");
        assert.equal(rSoft.stage, "solve");
        assert.equal(rSoft.unknownReason, "memory_budget");
        assert.equal(rSoft.stopAttribution, "solver_soft_memory_budget");
        assert.ok(typeof rSoft.numNodes === "number" && rSoft.numNodes > 0);
        assert.equal(rSoft.published, false);
        assert.equal(fs.existsSync(softOut), false);

        // 7b: Hard supervisor RSS cap stop on p090
        const rssOut = path.join(tmpDir, "mem_rss.proof.json");
        const rRss = await runSupervisedSolve({
          tproverBin,
          problemPath: p090,
          outProofPath: rssOut,
          totalTimeMs: 10000,
          searchSoftMs: 8000,
          memoryLimitBytes: 15000000,
          solverMemoryBytes: 12000000,
          nodeLimit: 1000000,
          maxDepth: 64,
        });
        assert.equal(rRss.verdict, "UNKNOWN");
        assert.equal(rRss.stage, "solve");
        assert.ok(
          rRss.unknownReason === "rss_limit" ||
            rRss.unknownReason === "memory_budget",
          `Unexpected reason=${rRss.unknownReason}`
        );
        assert.ok(typeof rRss.peakRssBytes === "number" && rRss.peakRssBytes > 0);
        assert.equal(rRss.published, false);
        assert.equal(fs.existsSync(rssOut), false);
      }
    );

    // 8. Tampered staging proof rejected by independent check
    await runCase(
      "8. tampered staging proof rejected at independent check with checker_failed",
      async () => {
        const outProof = path.join(tmpDir, "tampered.proof.json");
        const r = await runSupervisedSolve({
          tproverBin,
          problemPath: p042,
          outProofPath: outProof,
          totalTimeMs: 10000,
          searchSoftMs: 8000,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 3500,
          maxDepth: 48,
          faultTamperStaging: true,
        });
        assert.equal(r.verdict, "UNKNOWN");
        assert.equal(r.stage, "check");
        assert.equal(r.unknownReason, "checker_failed");
        assert.equal(r.stopAttribution, "checker_failed");
        assert.equal(r.verified, false);
        assert.equal(r.published, false);
        assert.ok(typeof r.checkMaxRssBytes === "number" && r.checkMaxRssBytes > 0);
        assert.equal(r.stagingCleaned, true);
        assert.equal(fs.existsSync(outProof), false);
      }
    );

    // 9. Unified file-identity & alias conflict matrix via CLI (exit 2 + preserved bytes)
    await runCase(
      "9. unified file-identity & alias conflict matrix rejects all collisions with exit 2",
      async () => {
        const idDir = path.join(tmpDir, "identity_matrix");
        fs.mkdirSync(idDir, { recursive: true });
        const probCopy = path.join(idDir, "prob.json");
        fs.copyFileSync(p042, probCopy);
        const probSha = sha256File(probCopy);

        const existingProof = path.join(idDir, "existing.proof.json");
        fs.writeFileSync(existingProof, '{"sentinel":"proof"}\n', "utf8");
        const existingProofSha = sha256File(existingProof);

        const probSymlink = path.join(idDir, "prob.link.json");
        fs.symlinkSync(probCopy, probSymlink);

        const probHardlink = path.join(idDir, "prob.hard.json");
        fs.linkSync(probCopy, probHardlink);

        const realOutDir = path.join(idDir, "real_out");
        const aliasOutDir = path.join(idDir, "alias_out");
        fs.mkdirSync(realOutDir, { recursive: true });
        fs.symlinkSync(realOutDir, aliasOutDir);

        const conflictCases = [
          [
            "receipt==problem",
            ["--out-receipt", probCopy, "--out-proof", path.join(idDir, "ok1.proof.json")],
          ],
          ["proof==problem", ["--out-proof", probCopy]],
          [
            "receipt==existing-proof",
            ["--out-proof", existingProof, "--out-receipt", existingProof],
          ],
          [
            "receipt==brand-new-proof",
            [
              "--out-proof",
              path.join(idDir, "same_new.json"),
              "--out-receipt",
              path.join(idDir, "same_new.json"),
            ],
          ],
          [
            "receipt==symlink(problem)",
            ["--out-receipt", probSymlink],
          ],
          [
            "receipt==hardlink(problem)",
            ["--out-receipt", probHardlink],
          ],
          [
            "parent-dir-symlink-alias",
            [
              "--out-proof",
              path.join(realOutDir, "nested.json"),
              "--out-receipt",
              path.join(aliasOutDir, "nested.json"),
            ],
          ],
        ];

        // Add case-insensitive / Unicode NFC-NFD brand-new tests on APFS/darwin
        if (process.platform === "darwin") {
          conflictCases.push(
            [
              "brand-new-case-collision",
              [
                "--out-proof",
                path.join(idDir, "CaseCollide.json"),
                "--out-receipt",
                path.join(idDir, "casecollide.json"),
              ],
            ],
            [
              "brand-new-unicode-nfc-nfd-collision",
              [
                "--out-proof",
                path.join(idDir, "caf\u00e9.json"),
                "--out-receipt",
                path.join(idDir, "cafe\u0301.json"),
              ],
            ]
          );
        }

        for (const [label, extraArgs] of conflictCases) {
          const res = runSupervisorCli([
            "--tprover",
            tproverBin,
            "--problem",
            probCopy,
            ...extraArgs,
          ]);
          assert.equal(
            res.status,
            2,
            `Expected exit code 2 for ${label}, got ${res.status} (stderr=${res.stderr})`
          );
          assert.equal(sha256File(probCopy), probSha, `Problem modified on ${label}`);
          assert.equal(
            sha256File(existingProof),
            existingProofSha,
            `Existing proof modified on ${label}`
          );
        }
        assert.equal(fs.existsSync(path.join(idDir, "same_new.json")), false);
        assert.equal(fs.existsSync(path.join(realOutDir, "nested.json")), false);
      }
    );

    // 10. Platform-independent cgroup snapshot, OOM counter split, regression & certification logic fixtures
    await runCase(
      "10. cgroup snapshot parser, independent OOM/oom_kill deltas, regression & certification unit fixtures",
      async () => {
        const fxBase = path.join(tmpDir, "cg_unit_fixtures");
        const fxValid = createMockCgroupDir(fxBase, "fx_valid", {
          "memory.events": "low 0\nhigh 0\nmax 0\noom 5\noom_kill 1\n",
        });
        const snapBase = readCgroupV2Snapshot(fxValid);
        assert.equal(snapBase.ok, true);
        assert.equal(snapBase.oomCount, 5);
        assert.equal(snapBase.oomKillCount, 1);

        // Positive zero-delta control
        const evalZero = evaluateCgroupOomProgress({
          baselineOom: 5,
          baselineOomKill: 1,
          currentOom: 5,
          currentOomKill: 1,
        });
        assert.equal(evalZero.ok, true);
        assert.equal(evalZero.oomDelta, 0);
        assert.equal(evalZero.oomKillDelta, 0);
        assert.equal(evalZero.breachReason, null);

        // Exact R31 counterexample: oom unchanged (5->5), oom_kill 1->2 must detect kill delta = 1
        fs.writeFileSync(
          path.join(fxValid, "memory.events"),
          "low 0\nhigh 0\nmax 0\noom 5\noom_kill 2\n",
          "utf8"
        );
        const snapKillOnly = readCgroupV2Snapshot(fxValid);
        assert.equal(snapKillOnly.ok, true);
        assert.equal(snapKillOnly.oomCount, 5);
        assert.equal(snapKillOnly.oomKillCount, 2);
        const evalKillOnly = evaluateCgroupOomProgress({
          baselineOom: snapBase.oomCount,
          baselineOomKill: snapBase.oomKillCount,
          currentOom: snapKillOnly.oomCount,
          currentOomKill: snapKillOnly.oomKillCount,
        });
        assert.equal(evalKillOnly.ok, true);
        assert.equal(evalKillOnly.oomDelta, 0);
        assert.equal(evalKillOnly.oomKillDelta, 1);
        assert.equal(evalKillOnly.breachReason, "cgroup_oom_kill");

        // Solo oom increment (oom 5->6, oom_kill unchanged 1->1)
        const evalOomOnly = evaluateCgroupOomProgress({
          baselineOom: 5,
          baselineOomKill: 1,
          currentOom: 6,
          currentOomKill: 1,
        });
        assert.equal(evalOomOnly.ok, true);
        assert.equal(evalOomOnly.oomDelta, 1);
        assert.equal(evalOomOnly.oomKillDelta, 0);
        assert.equal(evalOomOnly.breachReason, "cgroup_oom");

        // Counter regression must fail closed as metering_unavailable
        const evalRegress = evaluateCgroupOomProgress({
          baselineOom: 5,
          baselineOomKill: 1,
          prevOom: 5,
          prevOomKill: 2,
          currentOom: 5,
          currentOomKill: 1,
        });
        assert.equal(evalRegress.ok, false);
        assert.equal(evalRegress.regressed, true);
        assert.equal(evalRegress.breachReason, "metering_unavailable");

        // Missing oom_kill OR missing oom individually rejected
        const fxMissingKill = createMockCgroupDir(fxBase, "fx_missing_kill", {
          "memory.events": "low 0\nhigh 0\nmax 0\noom 5\n",
        });
        assert.equal(readCgroupV2Snapshot(fxMissingKill).ok, false);
        assert.equal(
          readCgroupV2Snapshot(fxMissingKill).error,
          "memory.events_oom_kill_missing"
        );

        const fxMissingOom = createMockCgroupDir(fxBase, "fx_missing_oom", {
          "memory.events": "low 0\nhigh 0\nmax 0\noom_kill 1\n",
        });
        assert.equal(readCgroupV2Snapshot(fxMissingOom).ok, false);
        assert.equal(
          readCgroupV2Snapshot(fxMissingOom).error,
          "memory.events_oom_missing"
        );

        // Certification decision gate (Linux positive + all R31 failure reasons)
        const baseLinuxOk = {
          isLinux: true,
          hasCgroupDir: true,
          cgroupContractValid: true,
          meteringComplete: true,
          withinTotalDeadline: true,
          settlementPassed: true,
          stagingCleaned: true,
          cgroupPeakBytes: 12000000,
          memoryLimitBytes: 2000000000,
          cgroupOomDelta: 0,
          cgroupOomKillDelta: 0,
          verified: true,
          published: true,
          hasOutProofPath: true,
          verdict: "PROVEN_WIN",
          settlementBreachReason: null,
        };
        assert.equal(evaluateCertificationDecision(baseLinuxOk).budgetCertified, true);
        assert.equal(
          evaluateCertificationDecision(baseLinuxOk).eligibleForFormalCount,
          true
        );
        assert.equal(
          evaluateCertificationDecision({
            ...baseLinuxOk,
            withinTotalDeadline: false,
            settlementPassed: false,
            verdict: "UNKNOWN",
            settlementBreachReason: "settlement_timeout",
          }).eligibleForFormalCount,
          false
        );
        assert.equal(
          evaluateCertificationDecision({ ...baseLinuxOk, cgroupOomKillDelta: 1 })
            .budgetCertified,
          false
        );
        assert.equal(
          evaluateCertificationDecision({ ...baseLinuxOk, cgroupOomDelta: 1 })
            .budgetCertified,
          false
        );
        assert.equal(
          evaluateCertificationDecision({
            ...baseLinuxOk,
            cgroupPeakBytes: 2000000001,
          }).budgetCertified,
          false
        );
        assert.equal(
          evaluateCertificationDecision({ ...baseLinuxOk, meteringComplete: false })
            .eligibleForFormalCount,
          false
        );

        // R32 P2 strict validation: PROVEN_LOSS valid; missing/non-proven verdict, negative/non-int peak, bad budget rejected
        assert.equal(
          evaluateCertificationDecision({ ...baseLinuxOk, verdict: "PROVEN_LOSS" })
            .eligibleForFormalCount,
          true
        );
        const { verdict: _omittedVerdict, ...missingVerdict } = baseLinuxOk;
        assert.equal(
          evaluateCertificationDecision(missingVerdict).budgetCertified,
          false
        );
        assert.equal(
          evaluateCertificationDecision(missingVerdict).eligibleForFormalCount,
          false
        );
        for (const badVerdict of [undefined, null, "", "PASS", "PROVEN"]) {
          const d = evaluateCertificationDecision({
            ...baseLinuxOk,
            verdict: badVerdict,
          });
          assert.equal(d.budgetCertified, false);
          assert.equal(d.eligibleForFormalCount, false);
        }
        for (const badPeak of [-1, NaN, Infinity, 12.5, "12000000", null]) {
          const d = evaluateCertificationDecision({
            ...baseLinuxOk,
            cgroupPeakBytes: badPeak,
          });
          assert.equal(d.budgetCertified, false);
          assert.equal(d.eligibleForFormalCount, false);
        }
        for (const badBudget of [0, -100, NaN, null]) {
          const d = evaluateCertificationDecision({
            ...baseLinuxOk,
            memoryLimitBytes: badBudget,
          });
          assert.equal(d.budgetCertified, false);
          assert.equal(d.eligibleForFormalCount, false);
        }
        assert.equal(evaluateCertificationDecision().budgetCertified, false);
        assert.equal(evaluateCertificationDecision().eligibleForFormalCount, false);
      }
    );

    // 11. Platform-aware synthetic cgroup v2 end-to-end receipt tests (or Linux tmpdir rejection)
    await runCase(
      "11. end-to-end cgroup contract receipts (synthetic on non-Linux / strict /sys/fs/cgroup check on Linux)",
      async () => {
        const cgBase = path.join(tmpDir, "mock_cgroups");
        fs.mkdirSync(cgBase, { recursive: true });

        if (process.platform === "linux") {
          // On Linux, ordinary temp dirs MUST be rejected by production preflight
          const cgTmp = createMockCgroupDir(cgBase, "linux_tmp_must_reject");
          const rTmp = await runSupervisedSolve({
            tproverBin,
            problemPath: p042,
            outProofPath: path.join(tmpDir, "linux_tmp_reject.proof.json"),
            cgroupDir: cgTmp,
            totalTimeMs: 5000,
            searchSoftMs: 4000,
            memoryLimitBytes: 2000000000,
          });
          assert.equal(rTmp.unknownReason, "cgroup_misconfigured");
          assert.equal(rTmp.cgroupContractValid, false);
          assert.equal(rTmp.budgetCertified, false);
          assert.equal(rTmp.published, false);
          return;
        }

        // 11a. Non-Linux valid mock cgroup positive control with non-zero baseline (oom=5, oom_kill=1)
        const cgValid = createMockCgroupDir(cgBase, "valid", {
          "memory.events": "low 0\nhigh 0\nmax 0\noom 5\noom_kill 1\n",
        });
        const out11a = path.join(tmpDir, "cg_valid.proof.json");
        const r11a = await runSupervisedSolve({
          tproverBin,
          problemPath: p042,
          outProofPath: out11a,
          cgroupDir: cgValid,
          totalTimeMs: 10000,
          searchSoftMs: 8000,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 3500,
          maxDepth: 48,
        });
        assert.equal(r11a.verdict, "PROVEN_WIN");
        assert.equal(r11a.verified, true);
        assert.equal(r11a.published, true);
        assert.equal(r11a.settlementPassed, true);
        assert.equal(r11a.withinTotalDeadline, true);
        assert.equal(r11a.cgroupContractValid, true);
        assert.equal(r11a.meteringComplete, true);
        assert.equal(r11a.cgroupInitialOomCount, 5);
        assert.equal(r11a.cgroupInitialOomKillCount, 1);
        assert.equal(r11a.cgroupFinalOomCount, 5);
        assert.equal(r11a.cgroupFinalOomKillCount, 1);
        assert.equal(r11a.cgroupOomDelta, 0);
        assert.equal(r11a.cgroupOomKillDelta, 0);
        assert.equal(
          r11a.memoryEnforcementMode,
          "cgroup_v2_contract_simulation_non_linux"
        );
        assert.equal(r11a.budgetCertified, false);

        // 11b. Misconfigured memory.max, swap != 0, missing PID in cgroup.procs
        for (const [sub, ov] of [
          ["max_unlimited", { "memory.max": "max\n" }],
          ["max_too_high", { "memory.max": "2000000001\n" }],
          ["swap_nonzero", { "memory.swap.max": "1048576\n" }],
          ["missing_pid", { "cgroup.procs": "999999\n" }],
        ]) {
          const cg = createMockCgroupDir(cgBase, sub, ov);
          const r = await runSupervisedSolve({
            tproverBin,
            problemPath: p042,
            cgroupDir: cg,
            totalTimeMs: 5000,
            searchSoftMs: 4000,
            memoryLimitBytes: 2000000000,
          });
          assert.equal(r.unknownReason, "cgroup_misconfigured");
          assert.equal(r.stopAttribution, "cgroup_misconfigured");
          assert.equal(r.budgetCertified, false);
          assert.equal(r.published, false);
        }

        // 11c. Missing memory.peak OR missing oom_kill -> metering_unavailable
        for (const [sub, ov] of [
          ["missing_peak", { "memory.peak": null }],
          ["missing_oom_kill", { "memory.events": "low 0\nhigh 0\noom 5\n" }],
        ]) {
          const cg = createMockCgroupDir(cgBase, sub, ov);
          const r = await runSupervisedSolve({
            tproverBin,
            problemPath: p042,
            outProofPath: path.join(tmpDir, `${sub}.proof.json`),
            cgroupDir: cg,
            totalTimeMs: 5000,
            searchSoftMs: 4000,
            memoryLimitBytes: 2000000000,
          });
          assert.equal(r.unknownReason, "metering_unavailable");
          assert.equal(r.stopAttribution, "metering_unavailable");
          assert.equal(r.meteringComplete, false);
          assert.equal(r.budgetCertified, false);
          assert.equal(r.published, false);
        }

        // 11d. Mid-run solo oom_kill increment (5,1 -> 5,2) detects delta=1
        const cgKillOnly = createMockCgroupDir(cgBase, "oom_kill_only", {
          "memory.events": "low 0\nhigh 0\nmax 0\noom 5\noom_kill 1\n",
        });
        const rKillOnly = await runSupervisedSolve({
          tproverBin,
          problemPath: p042,
          outProofPath: path.join(tmpDir, "cg_kill_only.proof.json"),
          cgroupDir: cgKillOnly,
          totalTimeMs: 10000,
          searchSoftMs: 8000,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 3500,
          maxDepth: 48,
          onStageSpawn: ({ stage }) => {
            if (stage === "solve") {
              fs.writeFileSync(
                path.join(cgKillOnly, "memory.events"),
                "low 0\nhigh 0\nmax 0\noom 5\noom_kill 2\n",
                "utf8"
              );
            }
          },
        });
        assert.equal(rKillOnly.verdict, "UNKNOWN");
        assert.equal(rKillOnly.unknownReason, "cgroup_oom_kill");
        assert.equal(rKillOnly.stopAttribution, "cgroup_oom_kill");
        assert.equal(rKillOnly.cgroupOomDelta, 0);
        assert.equal(rKillOnly.cgroupOomKillDelta, 1);
        assert.equal(rKillOnly.published, false);

        // 11e. Mid-run solo oom increment (5,1 -> 6,1) detects oomDelta=1, killDelta=0
        const cgOomOnly = createMockCgroupDir(cgBase, "oom_only", {
          "memory.events": "low 0\nhigh 0\nmax 0\noom 5\noom_kill 1\n",
        });
        const rOomOnly = await runSupervisedSolve({
          tproverBin,
          problemPath: p042,
          outProofPath: path.join(tmpDir, "cg_oom_only.proof.json"),
          cgroupDir: cgOomOnly,
          totalTimeMs: 10000,
          searchSoftMs: 8000,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 3500,
          maxDepth: 48,
          onStageSpawn: ({ stage }) => {
            if (stage === "solve") {
              fs.writeFileSync(
                path.join(cgOomOnly, "memory.events"),
                "low 0\nhigh 0\nmax 1\noom 6\noom_kill 1\n",
                "utf8"
              );
            }
          },
        });
        assert.equal(rOomOnly.verdict, "UNKNOWN");
        assert.equal(rOomOnly.unknownReason, "cgroup_oom");
        assert.equal(rOomOnly.stopAttribution, "cgroup_oom_event");
        assert.equal(rOomOnly.cgroupOomDelta, 1);
        assert.equal(rOomOnly.cgroupOomKillDelta, 0);
        assert.equal(rOomOnly.published, false);

        // 11f. Mid-run counter regression disqualifies metering
        const cgRegress = createMockCgroupDir(cgBase, "oom_regress", {
          "memory.events": "low 0\nhigh 0\nmax 0\noom 5\noom_kill 2\n",
        });
        const rRegress = await runSupervisedSolve({
          tproverBin,
          problemPath: p042,
          outProofPath: path.join(tmpDir, "cg_regress.proof.json"),
          cgroupDir: cgRegress,
          totalTimeMs: 10000,
          searchSoftMs: 8000,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 3500,
          maxDepth: 48,
          onStageSpawn: ({ stage }) => {
            if (stage === "solve") {
              fs.writeFileSync(
                path.join(cgRegress, "memory.events"),
                "low 0\nhigh 0\nmax 0\noom 5\noom_kill 1\n",
                "utf8"
              );
            }
          },
        });
        assert.equal(rRegress.verdict, "UNKNOWN");
        assert.equal(rRegress.unknownReason, "metering_unavailable");
        assert.equal(rRegress.meteringComplete, false);
        assert.equal(rRegress.published, false);
        assert.equal(rRegress.cgroupFinalOomCount, null);
        assert.equal(rRegress.cgroupFinalOomKillCount, null);
        assert.equal(rRegress.cgroupOomDelta, null);
        assert.equal(rRegress.cgroupOomKillDelta, null);
        assert.equal(rRegress.cgroupPeakBytes, null);
        assert.equal(rRegress.cgroupLastObservedOomCount, 5);
        assert.equal(rRegress.cgroupLastObservedOomKillCount, 2);

        // 11g. Peak > memoryLimitBytes
        const cgPeakOver = createMockCgroupDir(cgBase, "peak_over", {
          "memory.max": "50000000\n",
          "memory.current": "10000000\n",
          "memory.peak": "60000000\n",
        });
        const rPeakOver = await runSupervisedSolve({
          tproverBin,
          problemPath: p042,
          outProofPath: path.join(tmpDir, "peak_over.proof.json"),
          cgroupDir: cgPeakOver,
          totalTimeMs: 10000,
          searchSoftMs: 8000,
          memoryLimitBytes: 50000000,
          solverMemoryBytes: 40000000,
          nodeLimit: 3500,
          maxDepth: 48,
        });
        assert.equal(rPeakOver.verdict, "UNKNOWN");
        assert.equal(rPeakOver.unknownReason, "rss_limit");
        assert.equal(rPeakOver.published, false);
      }
    );

    // 12. Post-publish & post-cleanup settlement gate tests
    await runCase(
      "12. post-publish settlement gate rejects late deadline, missing metering, peak breach & OOM while preserving publication facts",
      async () => {
        // 12a. Post-publish-only deadline breach preserves published=true + verified=true, marks UNKNOWN settlement_timeout
        const outLate = path.join(tmpDir, "post_pub_late.proof.json");
        const rLate = await runSupervisedSolve({
          tproverBin,
          problemPath: p042,
          outProofPath: outLate,
          totalTimeMs: 1800,
          searchSoftMs: 1500,
          memoryLimitBytes: 2000000000,
          solverMemoryBytes: 1700000000,
          nodeLimit: 3500,
          maxDepth: 48,
          faultPostPublishDelayMs: 1600,
        });
        assert.equal(fs.existsSync(outLate), true);
        assert.equal(rLate.published, true);
        assert.equal(rLate.verified, true);
        assert.equal(rLate.proofRootStatus, "PROVEN_WIN");
        assert.equal(rLate.publishedSha256, sha256File(outLate));
        assert.equal(rLate.withinTotalDeadline, false);
        assert.equal(rLate.settlementPassed, false);
        assert.equal(rLate.stage, "settlement");
        assert.equal(rLate.verdict, "UNKNOWN");
        assert.equal(rLate.unknownReason, "settlement_timeout");
        assert.equal(rLate.stopAttribution, "settlement_post_publish_timeout");
        assert.equal(rLate.budgetCertified, false);
        assert.equal(rLate.eligibleForFormalCount, false);
        assert.equal(rLate.stagingCleaned, true);

        if (process.platform !== "linux") {
          const cgSettleBase = path.join(tmpDir, "cg_settle");

          // 12b. Post-publish missing memory.peak
          const cgMissing = createMockCgroupDir(cgSettleBase, "missing_at_settle");
          const outMiss = path.join(tmpDir, "post_pub_missing.proof.json");
          const rMiss = await runSupervisedSolve({
            tproverBin,
            problemPath: p042,
            outProofPath: outMiss,
            cgroupDir: cgMissing,
            totalTimeMs: 10000,
            searchSoftMs: 8000,
            memoryLimitBytes: 2000000000,
            solverMemoryBytes: 1700000000,
            nodeLimit: 3500,
            maxDepth: 48,
            onBeforeSettlement: ({ cgroupDir }) => {
              fs.rmSync(path.join(cgroupDir, "memory.peak"), { force: true });
            },
          });
          assert.equal(rMiss.published, true);
          assert.equal(rMiss.verified, true);
          assert.equal(rMiss.settlementPassed, false);
          assert.equal(rMiss.meteringComplete, false);
          assert.equal(rMiss.stage, "settlement");
          assert.equal(rMiss.verdict, "UNKNOWN");
          assert.equal(rMiss.unknownReason, "metering_unavailable");
          assert.equal(rMiss.cgroupPeakBytes, null);
          assert.equal(rMiss.cgroupFinalOomCount, null);
          assert.equal(rMiss.cgroupFinalOomKillCount, null);
          assert.equal(rMiss.cgroupOomDelta, null);
          assert.equal(rMiss.cgroupOomKillDelta, null);
          assert.equal(rMiss.cgroupLastObservedPeakBytes, 12000000);
          assert.equal(rMiss.budgetCertified, false);
          assert.equal(rMiss.eligibleForFormalCount, false);

          // 12c. Post-publish terminal peak breach (during readback/hash)
          const cgPeak = createMockCgroupDir(cgSettleBase, "peak_at_settle", {
            "memory.max": "50000000\n",
            "memory.current": "10000000\n",
            "memory.peak": "12000000\n",
          });
          const outPeak = path.join(tmpDir, "post_pub_peak.proof.json");
          const rPeak = await runSupervisedSolve({
            tproverBin,
            problemPath: p042,
            outProofPath: outPeak,
            cgroupDir: cgPeak,
            totalTimeMs: 10000,
            searchSoftMs: 8000,
            memoryLimitBytes: 50000000,
            solverMemoryBytes: 40000000,
            nodeLimit: 3500,
            maxDepth: 48,
            onBeforeSettlement: ({ cgroupDir }) => {
              fs.writeFileSync(
                path.join(cgroupDir, "memory.peak"),
                "60000000\n",
                "utf8"
              );
            },
          });
          assert.equal(rPeak.published, true);
          assert.equal(rPeak.settlementPassed, false);
          assert.equal(rPeak.stage, "settlement");
          assert.equal(rPeak.verdict, "UNKNOWN");
          assert.equal(rPeak.unknownReason, "rss_limit");
          assert.equal(rPeak.stopAttribution, "settlement_memory_exceeded");
          assert.equal(rPeak.budgetCertified, false);
          assert.equal(rPeak.eligibleForFormalCount, false);

          // 12d. Post-publish solo oom_kill increment (5,1 -> 5,2)
          const cgKill = createMockCgroupDir(cgSettleBase, "kill_at_settle", {
            "memory.events": "low 0\nhigh 0\nmax 0\noom 5\noom_kill 1\n",
          });
          const outKill = path.join(tmpDir, "post_pub_kill.proof.json");
          const rKill = await runSupervisedSolve({
            tproverBin,
            problemPath: p042,
            outProofPath: outKill,
            cgroupDir: cgKill,
            totalTimeMs: 10000,
            searchSoftMs: 8000,
            memoryLimitBytes: 2000000000,
            solverMemoryBytes: 1700000000,
            nodeLimit: 3500,
            maxDepth: 48,
            onBeforeSettlement: ({ cgroupDir }) => {
              fs.writeFileSync(
                path.join(cgroupDir, "memory.events"),
                "low 0\nhigh 0\nmax 0\noom 5\noom_kill 2\n",
                "utf8"
              );
            },
          });
          assert.equal(rKill.published, true);
          assert.equal(rKill.settlementPassed, false);
          assert.equal(rKill.stage, "settlement");
          assert.equal(rKill.verdict, "UNKNOWN");
          assert.equal(rKill.unknownReason, "cgroup_oom_kill");
          assert.equal(rKill.cgroupOomDelta, 0);
          assert.equal(rKill.cgroupOomKillDelta, 1);
          assert.equal(rKill.budgetCertified, false);
          assert.equal(rKill.eligibleForFormalCount, false);

          // 12e. Exact R32 s3 reproducer: terminal memory.events drops oom_kill -> final/deltas MUST be null (not stale 0)
          const cgDropKill = createMockCgroupDir(cgSettleBase, "drop_kill_at_settle", {
            "memory.events": "low 0\nhigh 0\nmax 0\noom 5\noom_kill 1\n",
          });
          const outDropKill = path.join(tmpDir, "post_pub_drop_kill.proof.json");
          const rDropKill = await runSupervisedSolve({
            tproverBin,
            problemPath: p042,
            outProofPath: outDropKill,
            cgroupDir: cgDropKill,
            totalTimeMs: 10000,
            searchSoftMs: 8000,
            memoryLimitBytes: 2000000000,
            solverMemoryBytes: 1700000000,
            nodeLimit: 3500,
            maxDepth: 48,
            onBeforeSettlement: ({ cgroupDir }) => {
              fs.writeFileSync(
                path.join(cgroupDir, "memory.events"),
                "low 0\nhigh 0\nmax 0\noom 5\n",
                "utf8"
              );
            },
          });
          assert.equal(rDropKill.published, true);
          assert.equal(rDropKill.verified, true);
          assert.equal(rDropKill.proofRootStatus, "PROVEN_WIN");
          assert.equal(rDropKill.stage, "settlement");
          assert.equal(rDropKill.verdict, "UNKNOWN");
          assert.equal(rDropKill.unknownReason, "metering_unavailable");
          assert.equal(rDropKill.meteringComplete, false);
          assert.ok(rDropKill.meteringIssues.includes("memory.events_oom_kill_missing"));
          assert.equal(rDropKill.cgroupInitialOomCount, 5);
          assert.equal(rDropKill.cgroupInitialOomKillCount, 1);
          assert.equal(rDropKill.cgroupLastObservedOomCount, 5);
          assert.equal(rDropKill.cgroupLastObservedOomKillCount, 1);
          assert.equal(rDropKill.cgroupLastObservedPeakBytes, 12000000);
          assert.equal(rDropKill.cgroupFinalOomCount, null);
          assert.equal(rDropKill.cgroupFinalOomKillCount, null);
          assert.equal(rDropKill.cgroupOomDelta, null);
          assert.equal(rDropKill.cgroupOomKillDelta, null);
          assert.equal(rDropKill.cgroupPeakBytes, null);
          assert.equal(rDropKill.budgetCertified, false);
          assert.equal(rDropKill.eligibleForFormalCount, false);
        }
      }
    );

    console.log(
      `  [NOT RUN] real Linux 2-cell dedicated cgroup v2 acceptance requires standalone out-of-group launcher scripts/verify_linux_cgroup_two_cells.mjs (current platform=${process.platform}).`
    );

    console.log(
      `\n========================================\nTask Card 1a Supervisor Verification: ${passed}/${total} passed, 0 failed.\n========================================`
    );
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
