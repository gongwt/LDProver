// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Versioned R4 + R5 Regression & Cross-Verification Test Suite (TypeScript)
// Run via: npx tsx scripts/verify_r5_regression.ts

import { DfpnSolver } from '../src/engine/dfpnSolver';
import {
  coordFromRowCol,
  GoPosition,
  PASS_MOVE,
  sgfToCoord,
} from '../src/engine/position';
import {
  SRS_BENCHMARK_PROBLEMS_CATALOG,
  TSUMEGO_PROBLEMS_CATALOG,
} from '../src/engine/problemsCatalog';
import {
  canonicalizeJsonJcs,
  ProofArtifactManager,
  sha256Hex,
} from '../src/engine/proofChecker';
import {
  parseStudyLdRzJsonToProblemSpec,
  RawStudyLdRzProblemJson,
  validateStudyLdRzContract,
} from '../src/engine/studyLdRzCatalog';
import {
  KoRule,
  ProofContext,
  ProofOutcome,
  SearchGoal,
  SolverConfig,
  TsumegoProblemSpec,
} from '../src/engine/types';

let totalAssertions = 0;
let passedAssertions = 0;
const failures: string[] = [];

function check(condition: boolean, label: string, detail = ''): void {
  totalAssertions++;
  if (condition) {
    passedAssertions++;
  } else {
    const msg = detail ? `${label} — ${detail}` : label;
    failures.push(msg);
    console.error(`  [FAIL] ${msg}`);
  }
}

function getSpec(idPrefix: string): TsumegoProblemSpec {
  const found = TSUMEGO_PROBLEMS_CATALOG.find(
    (p) => p.id === idPrefix || p.id.startsWith(idPrefix)
  );
  if (!found) {
    throw new Error(`Problem spec not found for prefix: ${idPrefix}`);
  }
  return found;
}

function resignLProof(obj: Record<string, unknown>): {
  json: string;
  checksum: string;
} {
  const copy: Record<string, unknown> = { ...obj };
  delete copy.checksum;
  const checksum = `sha256-jcs:${sha256Hex(canonicalizeJsonJcs(copy))}`;
  copy.checksum = checksum;
  return {
    json: JSON.stringify(copy, null, 2),
    checksum,
  };
}

function defaultConfig(maxNodes = 3500): SolverConfig {
  return {
    maxNodes,
    maxDepth: 64,
    memoryBudgetMb: 256,
    ttMode: 'pattern-tt',
    enableRzPruning: true,
    enableFastCaptureOrdering: true,
    enableProgressiveWidening: true,
    wideningBaseK: 8,
    deterministicMode: true,
    koRule: KoRule.SituationalSuperko,
    attackerAllowKo: false,
    defenderAllowKo: true,
  };
}

function runSection(title: string, fn: () => void): void {
  console.log(`\n=== ${title} ===`);
  fn();
}

const checker = new ProofArtifactManager();

// ============================================================================
// Section 1: Core Benchmarks (p001..p007) + p042 Performance & Soundness
// ============================================================================
runSection('1. Core Benchmarks (p001..p007) & p042', () => {
  for (const spec of SRS_BENCHMARK_PROBLEMS_CATALOG) {
    const cfg = defaultConfig(3500);
    const ctx = DfpnSolver.buildProofContext(spec, cfg);
    const pos = DfpnSolver.buildInitialPosition(spec, ctx);
    const solver = new DfpnSolver(cfg);
    const report = solver.solveFromPosition(spec, pos, ctx);

    check(
      report.rootStatus === spec.expectedOutcome,
      `${spec.id} outcome`,
      `expected=${spec.expectedOutcome}, got=${report.rootStatus} (nodes=${report.numNodes})`
    );

    if (spec.id === 'p003_false_eye_poke_kill') {
      check(
        report.numNodes <= 50,
        'p003 RZ-on node budget',
        `nodes=${report.numNodes}`
      );
    }

    if (spec.id === 'p004_outside_rz_pruning') {
      check(
        report.numNodes <= 50 && report.prunedOutsideRzCount > 0,
        'p004 RZ-on solved with OutsideRZRevalidated pruning',
        `nodes=${report.numNodes}, pruned=${report.prunedOutsideRzCount}`
      );
    }

    if (spec.id === 'p005_ko_dependent_barrier') {
      check(
        report.unknownReason === 'ko_dependent',
        'p005 default allow_ko=false returns UNKNOWN(ko_dependent)',
        `reason=${String(report.unknownReason)}`
      );
      // Verify allow_ko=true solves p005
      const koCfg: SolverConfig = { ...cfg, attackerAllowKo: true };
      const koCtx = DfpnSolver.buildProofContext(spec, koCfg);
      const koPos = DfpnSolver.buildInitialPosition(spec, koCtx);
      const koRep = new DfpnSolver(koCfg).solveFromPosition(spec, koPos, koCtx);
      check(
        koRep.rootStatus === ProofOutcome.ProvenWin,
        'p005 allow_ko=true returns PROVEN_WIN',
        `got=${koRep.rootStatus}`
      );
      const koMem = checker.verifyProofDag(koPos, koCtx, koRep, {
        verifiedScope: 'original_root',
      });
      const koFile = checker.verifySerializedLProofJson(koRep.lproofJson, {
        problem: spec,
        context: koCtx,
        scope: 'original_root',
      });
      const koFileMismatch = checker.verifySerializedLProofJson(koRep.lproofJson, {
        problem: spec,
        scope: 'original_root',
      });
      check(
        koMem.passed && koFile.passed,
        'p005 allow_ko=true memory & file verification PASS (with matching koCtx)',
        `mem=${koMem.errorCode}, file=${koFile.errorCode}`
      );
      check(
        !koFileMismatch.passed && koFileMismatch.errorCode === 'LP-P01',
        'p005 allow_ko=true rejected with LP-P01 when bound to default allow_ko=false spec',
        `got=${koFileMismatch.errorCode}`
      );
      continue;
    }

    const memVer = checker.verifyProofDag(pos, ctx, report, {
      verifiedScope: 'original_root',
    });
    const fileVer = checker.verifySerializedLProofJson(report.lproofJson, {
      problem: spec,
      scope: 'original_root',
    });
    check(
      memVer.passed && memVer.errorCode === 'PASS',
      `${spec.id} memory verification PASS`,
      `code=${memVer.errorCode}, msg=${memVer.message}`
    );
    check(
      fileVer.passed && fileVer.errorCode === 'PASS',
      `${spec.id} file verification PASS`,
      `code=${fileVer.errorCode}, msg=${fileVer.message}`
    );
  }

  // p042 benchmark from study-LD-RZ
  const p042 = getSpec('chao_vol1_p042');
  const cfg42 = defaultConfig(3500);
  const ctx42 = DfpnSolver.buildProofContext(p042, cfg42);
  const pos42 = DfpnSolver.buildInitialPosition(p042, ctx42);
  const rep42 = new DfpnSolver(cfg42).solveFromPosition(p042, pos42, ctx42);
  check(
    rep42.rootStatus === ProofOutcome.ProvenWin,
    'p042 solved as PROVEN_WIN',
    `got=${rep42.rootStatus}, nodes=${rep42.numNodes}`
  );
  check(
    rep42.numNodes <= 600 && rep42.prunedOutsideRzCount > 0,
    'p042 search nodes stay optimized (<= 600) with RZ pruning',
    `nodes=${rep42.numNodes}, pruned=${rep42.prunedOutsideRzCount}`
  );
  const mem42 = checker.verifyProofDag(pos42, ctx42, rep42, {
    verifiedScope: 'original_root',
  });
  const ver42 = checker.verifySerializedLProofJson(rep42.lproofJson, {
    problem: p042,
    scope: 'original_root',
  });
  check(
    mem42.passed &&
      ver42.passed &&
      mem42.canonicalDagChecksum === ver42.canonicalDagChecksum,
    'p042 memory & standalone file verification PASS with matching canonicalDagChecksum',
    `mem=${mem42.errorCode}, file=${ver42.errorCode}`
  );
  console.log(
    `  [INFO] p042: outcome=${rep42.rootStatus}, nodes=${rep42.numNodes}, dag=${rep42.proofDagNodes.length}, pruned=${rep42.prunedOutsideRzCount}, timeMs=${rep42.timeMs.toFixed(1)}`
  );
});

// ============================================================================
// Section 2: R5 §2 Workbench Verification Scope & Memory/File Parity
// ============================================================================
runSection('2. R5 §2 Verification Scope & Memory/File Parity', () => {
  const p001 = getSpec('p001_straight_three_live');
  const p005 = getSpec('p005_ko_dependent_barrier');

  const verifyTracedCase = (
    label: string,
    spec: TsumegoProblemSpec,
    traceMoves: number[],
    expectedOriginalCode: string,
    expectedTracedCode: string,
    expectedFreeCode: string,
    expectedOutsideRegion: boolean,
    expectedRestrictedKo: boolean
  ) => {
    const cfg = defaultConfig(3500);
    const ctx = DfpnSolver.buildProofContext(spec, cfg);
    const pos: GoPosition = DfpnSolver.buildInitialPosition(spec, ctx);
    for (const mv of traceMoves) {
      const res = pos.playMove(mv);
      check(res.legal, `${label} manual move ${mv} is legal`);
    }
    const rep = new DfpnSolver(cfg).solveFromPosition(spec, pos, ctx);
    check(
      rep.rootStatus === ProofOutcome.ProvenWin ||
        rep.rootStatus === ProofOutcome.ProvenLoss,
      `${label} subposition reached decisive outcome`,
      `got=${rep.rootStatus}`
    );

    const scopes: Array<{
      scope: 'original_root' | 'traced_within_rules' | 'free_exploration';
      expectedCode: string;
    }> = [
      { scope: 'original_root', expectedCode: expectedOriginalCode },
      { scope: 'traced_within_rules', expectedCode: expectedTracedCode },
      { scope: 'free_exploration', expectedCode: expectedFreeCode },
    ];

    for (const { scope, expectedCode } of scopes) {
      const mem = checker.verifyProofDag(pos, ctx, rep, {
        verifiedScope: scope,
      });
      const file = checker.verifySerializedLProofJson(rep.lproofJson, {
        problem: spec,
        scope,
      });
      check(
        mem.errorCode === expectedCode && file.errorCode === expectedCode,
        `${label} [${scope}] mem & file errorCode == ${expectedCode}`,
        `mem=${mem.errorCode}, file=${file.errorCode}`
      );
      check(
        mem.passed === (expectedCode === 'PASS') &&
          file.passed === (expectedCode === 'PASS'),
        `${label} [${scope}] mem & file passed parity`,
        `mem=${mem.passed}, file=${file.passed}`
      );
      check(
        mem.verifiedScope === scope && file.verifiedScope === scope,
        `${label} [${scope}] verifiedScope echoed`,
        `mem=${mem.verifiedScope}, file=${file.verifiedScope}`
      );
      check(
        mem.verifiedRootKind === 'traced_subposition' &&
          file.verifiedRootKind === 'traced_subposition',
        `${label} [${scope}] verifiedRootKind == traced_subposition`,
        `mem=${mem.verifiedRootKind}, file=${file.verifiedRootKind}`
      );
      if (scope !== 'original_root') {
        check(
          mem.traceOutsideRegion === expectedOutsideRegion &&
            file.traceOutsideRegion === expectedOutsideRegion,
          `${label} [${scope}] traceOutsideRegion == ${expectedOutsideRegion}`,
          `mem=${mem.traceOutsideRegion}, file=${file.traceOutsideRegion}`
        );
        check(
          mem.traceHasRestrictedKoCapture === expectedRestrictedKo &&
            file.traceHasRestrictedKoCapture === expectedRestrictedKo,
          `${label} [${scope}] traceHasRestrictedKoCapture == ${expectedRestrictedKo}`,
          `mem=${mem.traceHasRestrictedKoCapture}, file=${file.traceHasRestrictedKoCapture}`
        );
      }
    }
  };

  // Case A: p001 legal in-region move aa (0,0) -> coord 0
  verifyTracedCase(
    'p001 in-region trace [aa]',
    p001,
    [coordFromRowCol(0, 0, 19)],
    'LP-P02',
    'PASS',
    'PASS',
    false,
    false
  );

  // Case B: p001 out-of-region move fa (0,5) -> coord 5
  verifyTracedCase(
    'p001 out-of-region trace [fa]',
    p001,
    [coordFromRowCol(0, 5, 19)],
    'LP-P02',
    'LP-S11',
    'PASS',
    true,
    false
  );

  // Case C: p005 restricted-side ko capture ca (0,2) -> coord 2
  verifyTracedCase(
    'p005 restricted-ko trace [ca]',
    p005,
    [coordFromRowCol(0, 2, 19)],
    'LP-P02',
    'LP-S12',
    'PASS',
    false,
    true
  );

  // Contradictory rootKind="initial" + non-empty initialTraceMoves -> LP-P02
  const cfg1 = defaultConfig(3500);
  const ctx1 = DfpnSolver.buildProofContext(p001, cfg1);
  const pos1 = DfpnSolver.buildInitialPosition(p001, ctx1);
  const rep1 = new DfpnSolver(cfg1).solveFromPosition(p001, pos1, ctx1);
  const parsedContradict = JSON.parse(rep1.lproofJson) as Record<string, unknown>;
  (parsedContradict.problemSetup as Record<string, unknown>).rootKind = 'initial';
  (parsedContradict.problemSetup as Record<string, unknown>).initialTraceMoves = [1];
  const { json: contradictJson } = resignLProof(parsedContradict);
  const contradictDefault = checker.verifySerializedLProofJson(contradictJson);
  const contradictFree = checker.verifySerializedLProofJson(contradictJson, {
    scope: 'free_exploration',
  });
  check(
    !contradictDefault.passed && contradictDefault.errorCode === 'LP-P02',
    'Contradictory initial + non-empty initialTraceMoves rejected (default scope) -> LP-P02',
    `got=${contradictDefault.errorCode}`
  );
  check(
    !contradictFree.passed && contradictFree.errorCode === 'LP-P02',
    'Contradictory initial + non-empty initialTraceMoves rejected (free_exploration) -> LP-P02',
    `got=${contradictFree.errorCode}`
  );

  // R6 §2 P1: Pre-root history snapshot integrity in memory & file entrypoints
  // covering BOTH SituationalSuperko (SSK) and PositionalSuperko (PSK).
  for (const koRule of [KoRule.SituationalSuperko, KoRule.PositionalSuperko]) {
    const koLabel = koRule === KoRule.SituationalSuperko ? 'SSK' : 'PSK';
    const r6Cfg: SolverConfig = { ...defaultConfig(3500), koRule };
    const r6Ctx = DfpnSolver.buildProofContext(p001, r6Cfg);
    const fullHistPos = DfpnSolver.buildInitialPosition(p001, r6Ctx);
    const baPlay = fullHistPos.playMove(coordFromRowCol(0, 1, 19)); // B[ba]
    check(baPlay.legal, `R6 §2 [${koLabel}] p001 B[ba] legal`);
    check(
      fullHistPos.historySnapshots.length === 2,
      `R6 §2 [${koLabel}] full history has 2 snapshots`
    );

    const fullRep = new DfpnSolver(r6Cfg).solveFromPosition(
      p001,
      fullHistPos,
      r6Ctx
    );
    const fullMem = checker.verifyProofDag(fullHistPos, r6Ctx, fullRep, {
      verifiedScope: 'traced_within_rules',
    });
    const fullFile = checker.verifySerializedLProofJson(fullRep.lproofJson, {
      problem: p001,
      context: r6Ctx,
      scope: 'traced_within_rules',
    });
    check(
      fullMem.passed && fullFile.passed,
      `R6 §2 [${koLabel}] p001 B[ba] full history (2 snapshots) mem & file PASS`,
      `mem=${fullMem.errorCode}, file=${fullFile.errorCode}`
    );

    // Strip the origin-root snapshot while keeping board, turn, tokens, ko, origin & playedMoveTrace=[ba]
    const strippedPos = fullHistPos.clone();
    strippedPos.historySnapshots = fullHistPos.historySnapshots.slice(1);
    check(
      strippedPos.historySnapshots.length === 1,
      `R6 §2 [${koLabel}] stripped history has 1 snapshot`
    );
    const strippedRep = new DfpnSolver(r6Cfg).solveFromPosition(
      p001,
      strippedPos,
      r6Ctx
    );
    const strippedMem = checker.verifyProofDag(strippedPos, r6Ctx, strippedRep, {
      verifiedScope: 'traced_within_rules',
    });
    const strippedFile = checker.verifySerializedLProofJson(
      strippedRep.lproofJson,
      {
        problem: p001,
        context: r6Ctx,
        scope: 'traced_within_rules',
      }
    );
    check(
      !strippedMem.passed && strippedMem.errorCode === 'LP-S02',
      `R6 §2 [${koLabel}] stripped pre-root history rejected by memory checker -> LP-S02`,
      `mem=${strippedMem.errorCode}`
    );
    check(
      !strippedFile.passed && strippedFile.errorCode === 'LP-S02',
      `R6 §2 [${koLabel}] stripped pre-root history rejected by file checker -> LP-S02`,
      `file=${strippedFile.errorCode}`
    );

    // Also reject un-traced initial root whose historySnapshots was emptied in memory
    const emptyRootHistPos = DfpnSolver.buildInitialPosition(p001, r6Ctx);
    const rootRep = new DfpnSolver(r6Cfg).solveFromPosition(
      p001,
      emptyRootHistPos,
      r6Ctx
    );
    emptyRootHistPos.historySnapshots = [];
    const emptyRootMem = checker.verifyProofDag(
      emptyRootHistPos,
      r6Ctx,
      rootRep,
      { verifiedScope: 'original_root' }
    );
    check(
      !emptyRootMem.passed && emptyRootMem.errorCode === 'LP-S02',
      `R6 §2 [${koLabel}] un-traced root with emptied historySnapshots rejected -> LP-S02`,
      `mem=${emptyRootMem.errorCode}`
    );
  }
});

// ============================================================================
// Section 3: R5/R6 §3 Full-State Node Binding & §4 Cross-Engine canonicalDagChecksum
// ============================================================================
runSection('3. R5/R6 §3 Full-State Node Binding & §4 canonicalDagChecksum', () => {
  const p001 = getSpec('p001_straight_three_live');
  const cfg = defaultConfig(3500);
  const ctx = DfpnSolver.buildProofContext(p001, cfg);
  const pos = DfpnSolver.buildInitialPosition(p001, ctx);
  const rep = new DfpnSolver(cfg).solveFromPosition(p001, pos, ctx);

  // Cross-engine canonical compact_dag digest shared verbatim with C++ r5_regression_test.cc
  const expectedCrossEngineCanonicalDigest =
    'sha256-jcs:a002fe4896c1c728d06c9700518bf86bdb9e5a0b8c8dc58a8e3ecf7ef9d669d6';

  const baselineMem = checker.verifyProofDag(pos, ctx, rep, {
    verifiedScope: 'original_root',
  });
  const baselineVer = checker.verifySerializedLProofJson(rep.lproofJson, {
    problem: p001,
    scope: 'original_root',
  });
  check(
    baselineVer.passed &&
      baselineVer.canonicalDagChecksum === expectedCrossEngineCanonicalDigest &&
      baselineMem.canonicalDagChecksum === expectedCrossEngineCanonicalDigest,
    'R6 §4 p001 baseline memory & file canonicalDagChecksum match cross-engine canonical compact_dag digest',
    `file=${baselineVer.canonicalDagChecksum}, mem=${baselineMem.canonicalDagChecksum}`
  );

  // R5 §3 / R6 §3 Table: 4 independent single-field mutations on ba leaf (re-signed)
  const mutateBaLeaf = (
    mutator: (leaf: Record<string, unknown>) => void
  ): string => {
    const parsed = JSON.parse(rep.lproofJson) as Record<string, unknown>;
    const nodes = parsed.nodes as Array<Record<string, unknown>>;
    const leaf = nodes.find(
      (n) =>
        n.incomingMove === coordFromRowCol(0, 1, 19) &&
        (n.childNodeIds as number[]).length === 0
    );
    check(Boolean(leaf), 'Located ba leaf node in p001 full_state_table');
    if (leaf) mutator(leaf);
    return resignLProof(parsed).json;
  };

  // 1) stateId: 1 -> 0 => LP-N10
  const verBadState = checker.verifySerializedLProofJson(
    mutateBaLeaf((leaf) => {
      leaf.stateId = 0;
    }),
    { problem: p001, scope: 'original_root' }
  );
  check(
    !verBadState.passed && verBadState.errorCode === 'LP-N10',
    'R5/R6 §3 ba leaf stateId=0 rejected with LP-N10',
    `passed=${verBadState.passed}, code=${verBadState.errorCode}`
  );

  // 2) historyId: 1 -> 0 => LP-S10
  const verBadHistory = checker.verifySerializedLProofJson(
    mutateBaLeaf((leaf) => {
      leaf.historyId = 0;
    }),
    { problem: p001, scope: 'original_root' }
  );
  check(
    !verBadHistory.passed && verBadHistory.errorCode === 'LP-S10',
    'R6 §3 ba leaf historyId=0 rejected with LP-S10',
    `passed=${verBadHistory.passed}, code=${verBadHistory.errorCode}`
  );

  // 3) parentStateId: 0 -> -1 => LP-S10
  const verBadParent = checker.verifySerializedLProofJson(
    mutateBaLeaf((leaf) => {
      leaf.parentStateId = -1;
    }),
    { problem: p001, scope: 'original_root' }
  );
  check(
    !verBadParent.passed && verBadParent.errorCode === 'LP-S10',
    'R6 §3 ba leaf parentStateId=-1 rejected with LP-S10',
    `passed=${verBadParent.passed}, code=${verBadParent.errorCode}`
  );

  // 4) deleted historyId => LP-J02
  const verMissingHistory = checker.verifySerializedLProofJson(
    mutateBaLeaf((leaf) => {
      delete leaf.historyId;
    }),
    { problem: p001, scope: 'original_root' }
  );
  check(
    !verMissingHistory.passed && verMissingHistory.errorCode === 'LP-J02',
    'R6 §3 ba leaf missing historyId rejected with LP-J02',
    `passed=${verMissingHistory.passed}, code=${verMissingHistory.errorCode}`
  );

  // R5 §3 P2 / R6 §4 P2: Extra non-semantic top-level JSON field -> re-signed -> PASS,
  // jcsSha256Checksum reflects file bytes while canonicalDagChecksum stays identical across engines!
  const parsedExtra = JSON.parse(rep.lproofJson) as Record<string, unknown>;
  parsedExtra.extraNonSemanticTag = 'r6-audit-metadata';
  const { json: extraJson, checksum: extraFileChecksum } = resignLProof(parsedExtra);
  const extraVer = checker.verifySerializedLProofJson(extraJson, {
    problem: p001,
    scope: 'original_root',
  });
  check(
    extraVer.passed,
    'Extra non-semantic JSON field re-signed certificate PASS',
    `code=${extraVer.errorCode}`
  );
  check(
    extraVer.jcsSha256Checksum === extraFileChecksum,
    'jcsSha256Checksum matches re-signed file checksum',
    `got=${extraVer.jcsSha256Checksum}`
  );
  check(
    extraVer.canonicalDagChecksum !== extraVer.jcsSha256Checksum,
    'canonicalDagChecksum differs from jcsSha256Checksum when extra field is present',
    `canonical=${extraVer.canonicalDagChecksum}, file=${extraVer.jcsSha256Checksum}`
  );
  check(
    extraVer.canonicalDagChecksum === expectedCrossEngineCanonicalDigest,
    'canonicalDagChecksum equals cross-engine canonical compact_dag digest',
    `extra=${extraVer.canonicalDagChecksum}, expected=${expectedCrossEngineCanonicalDigest}`
  );
});

// ============================================================================
// Section 4: R4 & Core Tampering Defenses (LP-C01, LP-P01, LP-N22, LP-R01)
// ============================================================================
runSection('4. R4 & Core Tampering Defenses', () => {
  const p001 = getSpec('p001_straight_three_live');
  const p003 = getSpec('p003_false_eye_poke_kill');
  const p004 = getSpec('p004_outside_rz_pruning');
  const p007 = getSpec('p007_cramped_corner_proven_loss');

  const cfg = defaultConfig(3500);
  const ctx1 = DfpnSolver.buildProofContext(p001, cfg);
  const pos1 = DfpnSolver.buildInitialPosition(p001, ctx1);
  const rep1 = new DfpnSolver(cfg).solveFromPosition(p001, pos1, ctx1);

  // LP-C01: Tampered payload without re-signing
  const tamperedC01 = rep1.lproofJson.replace('"PROVEN_WIN"', '"PROVEN_LOSS"');
  const verC01 = checker.verifySerializedLProofJson(tamperedC01);
  check(
    !verC01.passed && verC01.errorCode === 'LP-C01',
    'Unsigned tampering triggers LP-C01',
    `code=${verC01.errorCode}`
  );

  // LP-P01: Binding p001 certificate against p003 expectedProblem
  const verP01 = checker.verifySerializedLProofJson(rep1.lproofJson, {
    problem: p003,
    scope: 'original_root',
  });
  check(
    !verP01.passed && verP01.errorCode === 'LP-P01',
    'Mismatched expectedProblem triggers LP-P01',
    `code=${verP01.errorCode}`
  );

  // LP-N22: Drop one legal move from universal root of p007 (OR PROVEN_LOSS)
  const ctx7 = DfpnSolver.buildProofContext(p007, cfg);
  const pos7 = DfpnSolver.buildInitialPosition(p007, ctx7);
  const rep7 = new DfpnSolver(cfg).solveFromPosition(p007, pos7, ctx7);
  const parsed7 = JSON.parse(rep7.lproofJson) as Record<string, unknown>;
  const root7 = (parsed7.nodes as Array<Record<string, unknown>>)[
    parsed7.rootNode as number
  ];
  (root7.childMoves as number[]).pop();
  (root7.childNodeIds as number[]).pop();
  const { json: dropMoveJson } = resignLProof(parsed7);
  const verN22 = checker.verifySerializedLProofJson(dropMoveJson, {
    problem: p007,
    scope: 'original_root',
  });
  check(
    !verN22.passed && verN22.errorCode === 'LP-N22',
    'Dropping legal move at universal node triggers LP-N22',
    `code=${verN22.errorCode}`
  );

  // LP-R01: Self-referencing pruned node on p004
  const ctx4 = DfpnSolver.buildProofContext(p004, cfg);
  const pos4 = DfpnSolver.buildInitialPosition(p004, ctx4);
  const rep4 = new DfpnSolver(cfg).solveFromPosition(p004, pos4, ctx4);
  const parsed4 = JSON.parse(rep4.lproofJson) as Record<string, unknown>;
  const prunedNode = (parsed4.nodes as Array<Record<string, unknown>>).find(
    (n) => Boolean(n.isPrunedOutsideRz)
  );
  check(Boolean(prunedNode), 'Found OutsideRZRevalidated node in p004');
  if (prunedNode) {
    prunedNode.sourceProofNodeId = prunedNode.nodeId;
    const { json: selfRefJson } = resignLProof(parsed4);
    const verR01 = checker.verifySerializedLProofJson(selfRefJson, {
      problem: p004,
      scope: 'original_root',
    });
    check(
      !verR01.passed && verR01.errorCode === 'LP-R01',
      'Self-referencing pruned node triggers LP-R01',
      `code=${verR01.errorCode}`
    );
  }
});

// ============================================================================
// Section 5: R7 Protocol Edge Cases (§2 Empty Region, §3 NULL_MOVE, §4 Unicode)
// ============================================================================
runSection('5. R7 Protocol Edge Cases (§2 Empty Region, §3 NULL_MOVE, §4 Unicode)', () => {
  const p001 = getSpec('p001_straight_three_live');
  const p007 = getSpec('p007_cramped_corner_proven_loss');
  const cfg = defaultConfig(3500);

  const toCompactDagJson = (fullObj: Record<string, unknown>): Record<string, unknown> => {
    const compact: Record<string, unknown> = {
      ...fullObj,
      encodingMode: 'compact_dag',
    };
    delete compact.stateTable;
    delete compact.snapshotPool;
    delete compact.historySnapshotIds;
    delete compact.historyTable;
    delete compact.checksum;
    const rawNodes = (fullObj.nodes as Array<Record<string, unknown>>) ?? [];
    compact.nodes = rawNodes.map((n) => {
      const c = { ...n };
      delete c.stateId;
      delete c.historyId;
      delete c.parentStateId;
      return c;
    });
    return compact;
  };

  // --- R7 §2 P1: Explicit empty region (PASS-only) tri-state round-trip ---
  const p001EmptyRegion: TsumegoProblemSpec = {
    ...p001,
    hasRegionHint: true,
    regionCoords: [],
    rawRegionCoords: [],
    attentionCoords: [],
  };
  const ctxEmpty = DfpnSolver.buildProofContext(p001EmptyRegion, cfg);
  const posEmpty = DfpnSolver.buildInitialPosition(p001EmptyRegion, ctxEmpty);
  const repEmpty = new DfpnSolver(cfg).solveFromPosition(
    p001EmptyRegion,
    posEmpty,
    ctxEmpty
  );
  check(
    repEmpty.rootStatus === ProofOutcome.ProvenLoss && repEmpty.numNodes <= 5,
    'R7 §2 p001 explicit empty region (PASS-only) solves to PROVEN_LOSS in <= 5 nodes',
    `status=${repEmpty.rootStatus}, nodes=${repEmpty.numNodes}`
  );
  const emptyMemVer = checker.verifyProofDag(posEmpty, ctxEmpty, repEmpty, {
    verifiedScope: 'original_root',
  });
  check(
    emptyMemVer.passed && emptyMemVer.errorCode === 'PASS',
    'R7 §2 p001 explicit empty region passes memory verification',
    `code=${emptyMemVer.errorCode}`
  );
  const emptyParsed = JSON.parse(repEmpty.lproofJson) as Record<string, unknown>;
  const emptySetup = emptyParsed.problemSetup as Record<string, unknown>;
  check(
    emptySetup.hasRegionHint === true &&
      Array.isArray(emptySetup.regionCoords) &&
      (emptySetup.regionCoords as number[]).length === 0,
    'R7 §2 serialized lproof/1 preserves hasRegionHint=true with empty regionCoords=[]'
  );
  const emptyFileVer = checker.verifySerializedLProofJson(repEmpty.lproofJson);
  const emptyCompact = resignLProof(toCompactDagJson(emptyParsed)).json;
  const emptyCompactVer = checker.verifySerializedLProofJson(emptyCompact);
  check(
    emptyFileVer.passed &&
      emptyCompactVer.passed &&
      emptyFileVer.canonicalDagChecksum === emptyMemVer.canonicalDagChecksum &&
      emptyCompactVer.canonicalDagChecksum === emptyMemVer.canonicalDagChecksum,
    'R7 §2 explicit empty region round-trips PASS in full & compact encodings with identical canonicalDagChecksum',
    `full=${emptyFileVer.errorCode}, compact=${emptyCompactVer.errorCode}`
  );

  // Flipping hasRegionHint=false turns it into unrestricted full-board -> LP-N22!
  const emptyAsUnrestricted = JSON.parse(repEmpty.lproofJson) as Record<
    string,
    unknown
  >;
  (emptyAsUnrestricted.problemSetup as Record<string, unknown>).hasRegionHint =
    false;
  const emptyAsUnrestrictedVer = checker.verifySerializedLProofJson(
    resignLProof(emptyAsUnrestricted).json
  );
  check(
    !emptyAsUnrestrictedVer.passed &&
      emptyAsUnrestrictedVer.errorCode === 'LP-N22',
    'R7 §2 explicit empty region re-labeled hasRegionHint=false fails unrestricted full coverage -> LP-N22',
    `code=${emptyAsUnrestrictedVer.errorCode}`
  );

  // Reverse witness: p001 PROVEN_WIN (ba witness) with hasRegionHint=true, regionCoords=[] -> LP-R02!
  const ctx1 = DfpnSolver.buildProofContext(p001, cfg);
  const pos1 = DfpnSolver.buildInitialPosition(p001, ctx1);
  const rep1 = new DfpnSolver(cfg).solveFromPosition(p001, pos1, ctx1);
  const revFullObj = JSON.parse(rep1.lproofJson) as Record<string, unknown>;
  (revFullObj.problemSetup as Record<string, unknown>).hasRegionHint = true;
  (revFullObj.problemSetup as Record<string, unknown>).regionCoords = [];
  (revFullObj.problemSetup as Record<string, unknown>).rawRegionPointCount = 0;
  const revFullVer = checker.verifySerializedLProofJson(
    resignLProof(revFullObj).json
  );
  const revCompactVer = checker.verifySerializedLProofJson(
    resignLProof(toCompactDagJson(revFullObj)).json
  );
  check(
    !revFullVer.passed &&
      revFullVer.errorCode === 'LP-R02' &&
      !revCompactVer.passed &&
      revCompactVer.errorCode === 'LP-R02',
    'R7 §2 reverse witness (p001 ba with hasRegionHint=true, regionCoords=[]) rejected in both encodings -> LP-R02',
    `full=${revFullVer.errorCode}, compact=${revCompactVer.errorCode}`
  );

  // Contradictory hasRegionHint=false + non-empty regionCoords=[0,1,2] -> LP-J02
  const contraRegObj = JSON.parse(rep1.lproofJson) as Record<string, unknown>;
  (contraRegObj.problemSetup as Record<string, unknown>).hasRegionHint = false;
  const contraRegVer = checker.verifySerializedLProofJson(
    resignLProof(contraRegObj).json
  );
  check(
    !contraRegVer.passed && contraRegVer.errorCode === 'LP-J02',
    'R7 §2 contradictory hasRegionHint=false with non-empty regionCoords rejected -> LP-J02',
    `code=${contraRegVer.errorCode}`
  );

  // --- R7 §3 P2: p007 PROVEN_LOSS with NULL_MOVE (-2) & bestMoveSgf="" vs null ---
  const ctx7 = DfpnSolver.buildProofContext(p007, cfg);
  const pos7 = DfpnSolver.buildInitialPosition(p007, ctx7);
  const rep7 = new DfpnSolver(cfg).solveFromPosition(p007, pos7, ctx7);
  check(
    rep7.rootStatus === ProofOutcome.ProvenLoss,
    'R7 §3 p007 solves to PROVEN_LOSS'
  );
  const makeP007WithBestMove = (
    bestMove: number,
    bestMoveSgf: string | null,
    compact: boolean
  ): string => {
    const obj = JSON.parse(rep7.lproofJson) as Record<string, unknown>;
    obj.bestMove = bestMove;
    obj.bestMoveSgf = bestMoveSgf;
    return resignLProof(compact ? toCompactDagJson(obj) : obj).json;
  };
  const p007EmptyFullVer = checker.verifySerializedLProofJson(
    makeP007WithBestMove(-2, '', false),
    { problem: p007, scope: 'original_root' }
  );
  const p007EmptyCompactVer = checker.verifySerializedLProofJson(
    makeP007WithBestMove(-2, '', true),
    { problem: p007, scope: 'original_root' }
  );
  const p007NullFullVer = checker.verifySerializedLProofJson(
    makeP007WithBestMove(-2, null, false),
    { problem: p007, scope: 'original_root' }
  );
  const p007NullCompactVer = checker.verifySerializedLProofJson(
    makeP007WithBestMove(-2, null, true),
    { problem: p007, scope: 'original_root' }
  );
  check(
    p007EmptyFullVer.passed &&
      p007EmptyCompactVer.passed &&
      p007NullFullVer.passed &&
      p007NullCompactVer.passed,
    'R7 §3 p007 PROVEN_LOSS with bestMove=-2 & bestMoveSgf="" or null PASSES in both full & compact encodings',
    `""full=${p007EmptyFullVer.errorCode}, ""compact=${p007EmptyCompactVer.errorCode}, nullFull=${p007NullFullVer.errorCode}, nullCompact=${p007NullCompactVer.errorCode}`
  );
  check(
    Boolean(p007EmptyFullVer.canonicalDagChecksum) &&
      p007EmptyFullVer.canonicalDagChecksum ===
        p007EmptyCompactVer.canonicalDagChecksum &&
      p007EmptyFullVer.canonicalDagChecksum ===
        p007NullFullVer.canonicalDagChecksum &&
      p007EmptyFullVer.canonicalDagChecksum ===
        p007NullCompactVer.canonicalDagChecksum,
    'R7 §3 p007 bestMove=-2 canonicalDagChecksum is identical across "" / null and full / compact encodings'
  );
  const p007BadSgfFull = checker.verifySerializedLProofJson(
    makeP007WithBestMove(-2, 'pass', false),
    { problem: p007, scope: 'original_root' }
  );
  const p007BadSgfCompact = checker.verifySerializedLProofJson(
    makeP007WithBestMove(-2, 'ba', true),
    { problem: p007, scope: 'original_root' }
  );
  check(
    !p007BadSgfFull.passed &&
      p007BadSgfFull.errorCode === 'LP-R02' &&
      !p007BadSgfCompact.passed &&
      p007BadSgfCompact.errorCode === 'LP-R02',
    'R7 §3 p007 bestMove=-2 with mismatched non-empty bestMoveSgf rejected -> LP-R02',
    `full=${p007BadSgfFull.errorCode}, compact=${p007BadSgfCompact.errorCode}`
  );

  // --- R7 §4 P2: UTF-16 Surrogate Pair Equivalence ("围棋🎯" vs "围棋\ud83c\udfaf") & Lone Surrogate Rejection ---
  const uniObj = JSON.parse(rep1.lproofJson) as Record<string, unknown>;
  (uniObj.context as Record<string, unknown>).contextId = '围棋🎯';
  const { json: uniUtf8Json, checksum: uniChecksum } = resignLProof(uniObj);
  const uniEscapedJson = uniUtf8Json.replace('围棋🎯', '围棋\\ud83c\\udfaf');
  check(
    uniEscapedJson.includes('围棋\\ud83c\\udfaf') &&
      !uniEscapedJson.includes('🎯'),
    'R7 §4 constructed surrogate-pair escaped JSON preserving identical checksum'
  );
  const uniUtf8Ver = checker.verifySerializedLProofJson(uniUtf8Json, {
    problem: p001,
    scope: 'original_root',
  });
  const uniEscapedVer = checker.verifySerializedLProofJson(uniEscapedJson, {
    problem: p001,
    scope: 'original_root',
  });
  check(
    uniUtf8Ver.passed &&
      uniEscapedVer.passed &&
      uniUtf8Ver.jcsSha256Checksum === uniChecksum &&
      uniEscapedVer.jcsSha256Checksum === uniChecksum &&
      uniUtf8Ver.canonicalDagChecksum === uniEscapedVer.canonicalDagChecksum,
    'R7 §4 literal UTF-8 "围棋🎯" and escaped "围棋\\ud83c\\udfaf" both PASS with identical file & canonical digests',
    `utf8=${uniUtf8Ver.errorCode}, esc=${uniEscapedVer.errorCode}`
  );

  const loneHighJson = uniUtf8Json.replace('围棋🎯', '围棋\\ud83c');
  const loneLowJson = uniUtf8Json.replace('围棋🎯', '围棋\\udfaf');
  const loneHighVer = checker.verifySerializedLProofJson(loneHighJson);
  const loneLowVer = checker.verifySerializedLProofJson(loneLowJson);
  check(
    !loneHighVer.passed &&
      loneHighVer.errorCode === 'LP-J01' &&
      !loneLowVer.passed &&
      loneLowVer.errorCode === 'LP-J01',
    'R7 §4 lone UTF-16 high/low surrogates rejected -> LP-J01',
    `high=${loneHighVer.errorCode}, low=${loneLowVer.errorCode}`
  );
});

// =============================================================================
// Section 6: R8 Original Problem Contract Parity, Reverse-Witness & Type Safety
// =============================================================================
runSection('Section 6: R8 Problem Contract, Reverse-Witness & Contradictory Region', () => {
  const checker = new ProofArtifactManager();
  const baseRawJson =
    '{"masked_sgf_str":"(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa])","winning_color":"B","turn_color":"B","black_search_goal":"TOKILL","white_search_goal":"TOLIVE","black_crucial_stone":"aa","white_crucial_stone":"aa","black_ko_rule":"allow_ko","white_ko_rule":"allow_ko"}';
  const emptyRegionRawJson =
    '{"masked_sgf_str":"(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa])","winning_color":"B","turn_color":"B","black_search_goal":"TOKILL","white_search_goal":"TOLIVE","black_crucial_stone":"aa","white_crucial_stone":"aa","black_ko_rule":"allow_ko","white_ko_rule":"allow_ko","region":""}';
  const maRegionRawJson =
    '{"masked_sgf_str":"(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa]MA[aa][ab][ba])","winning_color":"B","turn_color":"B","black_search_goal":"TOKILL","white_search_goal":"TOLIVE","black_crucial_stone":"aa","white_crucial_stone":"aa","black_ko_rule":"allow_ko","white_ko_rule":"allow_ko"}';
  const explicitRegionRawJson =
    '{"masked_sgf_str":"(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa])","winning_color":"B","turn_color":"B","black_search_goal":"TOKILL","white_search_goal":"TOLIVE","black_crucial_stone":"aa","white_crucial_stone":"aa","black_ko_rule":"allow_ko","white_ko_rule":"allow_ko","region":"aa,ab,ba"}';
  const invalidRegionRawJson =
    '{"masked_sgf_str":"(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa])","winning_color":"B","turn_color":"B","black_search_goal":"TOKILL","white_search_goal":"TOLIVE","black_crucial_stone":"aa","white_crucial_stone":"aa","black_ko_rule":"allow_ko","white_ko_rule":"allow_ko","region":"aa,zz"}';

  const specAbsent = parseStudyLdRzJsonToProblemSpec(
    'r8_two_stone_absent.json',
    JSON.parse(baseRawJson) as RawStudyLdRzProblemJson
  );
  const specEmpty = parseStudyLdRzJsonToProblemSpec(
    'r8_two_stone_empty.json',
    JSON.parse(emptyRegionRawJson) as RawStudyLdRzProblemJson
  );
  const specMa = parseStudyLdRzJsonToProblemSpec(
    'r8_two_stone_ma.json',
    JSON.parse(maRegionRawJson) as RawStudyLdRzProblemJson
  );
  const specExplicit = parseStudyLdRzJsonToProblemSpec(
    'r8_two_stone_explicit.json',
    JSON.parse(explicitRegionRawJson) as RawStudyLdRzProblemJson
  );
  const invalidRegionVal = validateStudyLdRzContract(
    JSON.parse(invalidRegionRawJson) as Partial<RawStudyLdRzProblemJson>
  );

  // R8 §1: Absent and empty `region` without MA[...] must be unrestricted with ZERO fabricated immortal walls
  check(
    specAbsent.hasRegionHint === false &&
      specAbsent.regionCoords.length === 0 &&
      specAbsent.immortalWallCoords.length === 0,
    'R8 §1 absent region -> hasRegionHint=false, regionCoords=[], immortalWallCoords=[]',
    `hasRegionHint=${String(specAbsent.hasRegionHint)}, region=${specAbsent.regionCoords.length}, wall=${specAbsent.immortalWallCoords.length}`
  );
  check(
    specEmpty.hasRegionHint === false &&
      specEmpty.regionCoords.length === 0 &&
      specEmpty.immortalWallCoords.length === 0,
    'R8 §1 empty region="" -> hasRegionHint=false, regionCoords=[], immortalWallCoords=[]',
    `hasRegionHint=${String(specEmpty.hasRegionHint)}, region=${specEmpty.regionCoords.length}, wall=${specEmpty.immortalWallCoords.length}`
  );
  check(
    specMa.hasRegionHint === true &&
      specMa.regionCoords.join(',') === '0,1,19' &&
      specMa.immortalWallCoords.length === 0,
    'R8 §1 SGF MA[aa][ab][ba] -> hasRegionHint=true, regionCoords=[0,1,19], immortalWallCoords=[]',
    `hasRegionHint=${String(specMa.hasRegionHint)}, region=[${specMa.regionCoords.join(',')}], wall=${specMa.immortalWallCoords.length}`
  );
  check(
    specExplicit.hasRegionHint === true &&
      specExplicit.regionCoords.join(',') === '0,1,19' &&
      specExplicit.immortalWallCoords.length === 0,
    'R8 §1 explicit region="aa,ab,ba" -> hasRegionHint=true, regionCoords=[0,1,19], immortalWallCoords=[]',
    `hasRegionHint=${String(specExplicit.hasRegionHint)}, region=[${specExplicit.regionCoords.join(',')}], wall=${specExplicit.immortalWallCoords.length}`
  );
  check(
    !invalidRegionVal.valid &&
      invalidRegionVal.code.startsWith('FR1-INVALID-REGION-COORD'),
    'R8 §1 invalid region coordinate "zz" rejected -> FR1-INVALID-REGION-COORD',
    `valid=${invalidRegionVal.valid}, code=${invalidRegionVal.code}`
  );

  // Solve & verify all 4 variants: all must prove PROVEN_WIN with B[ba] (coord 1) in 2 nodes!
  const r8Cfg: SolverConfig = { ...defaultConfig(200), useProblemDefaultKo: true };
  for (const [label, spec] of [
    ['absent', specAbsent],
    ['empty', specEmpty],
    ['MA', specMa],
    ['explicit', specExplicit],
  ] as const) {
    const solver = new DfpnSolver(r8Cfg);
    const rep = solver.solveProblem(spec);
    check(
      rep.rootStatus === ProofOutcome.ProvenWin &&
        rep.bestMove === 1 &&
        rep.bestMoveSgf === 'ba' &&
        rep.numNodes <= 4 &&
        rep.proofDagNodes.length === 2,
      `R8 §1 two-stone (${label}) solves to PROVEN_WIN bestMove=ba (coord 1) in 2 DAG nodes`,
      `status=${rep.rootStatus}, best=${rep.bestMoveSgf}(${rep.bestMove}), numNodes=${rep.numNodes}, dag=${rep.proofDagNodes.length}`
    );
    const ctx = DfpnSolver.buildProofContext(spec, r8Cfg);
    const initPos = DfpnSolver.buildInitialPosition(spec, ctx);
    const memVer = checker.verifyProofDag(initPos, ctx, rep);
    const fileVer = checker.verifySerializedLProofJson(rep.lproofJson, {
      problem: spec,
      scope: 'original_root',
    });
    check(
      memVer.passed &&
        fileVer.passed &&
        memVer.canonicalDagChecksum === fileVer.canonicalDagChecksum,
      `R8 §1 two-stone (${label}) passes memory & external-bound file verification with identical canonical digest`,
      `mem=${memVer.errorCode}, file=${fileVer.errorCode}`
    );
  }

  // R8 §1 cross-binding: absent-region proof binds cleanly to empty-region spec (both unrestricted)
  const solverAbsent = new DfpnSolver(r8Cfg);
  const repAbsent = solverAbsent.solveProblem(specAbsent);
  const crossBindEmpty = checker.verifySerializedLProofJson(
    repAbsent.lproofJson,
    { problem: specEmpty, scope: 'original_root' }
  );
  const crossBindExplicit = checker.verifySerializedLProofJson(
    repAbsent.lproofJson,
    { problem: specExplicit, scope: 'original_root' }
  );
  check(
    crossBindEmpty.passed &&
      !crossBindExplicit.passed &&
      crossBindExplicit.errorCode === 'LP-P01',
    'R8 §1 absent-region proof binds to empty-region spec (PASS) and rejects explicit-region spec (LP-P01)',
    `empty=${crossBindEmpty.errorCode}, explicit=${crossBindExplicit.errorCode}`
  );

  // R8 §2: Reverse witness on full_state_table (p001 ba with hasRegionHint=true, regionCoords=[]) -> LP-R02
  const p001 = getSpec('p001');
  const solver1 = new DfpnSolver(defaultConfig(500));
  const rep1 = solver1.solveProblem(p001);
  const revFullObj = JSON.parse(rep1.lproofJson) as Record<string, unknown>;
  const revFullSetup = revFullObj.problemSetup as Record<string, unknown>;
  revFullSetup.hasRegionHint = true;
  revFullSetup.regionCoords = [];
  revFullSetup.rawRegionPointCount = 0;
  const revFullVer = checker.verifySerializedLProofJson(
    resignLProof(revFullObj).json
  );
  check(
    !revFullVer.passed && revFullVer.errorCode === 'LP-R02',
    'R8 §2 full_state_table reverse witness (p001 ba with hasRegionHint=true, regionCoords=[]) -> LP-R02',
    `code=${revFullVer.errorCode}`
  );

  // R8 §3: Contradictory hasRegionHint=false + non-empty regionCoords rejected across ALL TS object entrypoints
  const badSpec: TsumegoProblemSpec = {
    ...p001,
    hasRegionHint: false,
    regionCoords: [0, 1, 2],
  };
  let solverThrew = false;
  try {
    new DfpnSolver(defaultConfig(100)).solveProblem(badSpec);
  } catch (err) {
    solverThrew = String(err).includes('LP-J02');
  }
  check(
    solverThrew,
    'R8 §3 DfpnSolver.solveProblem rejects contradictory hasRegionHint=false + non-empty regionCoords (LP-J02)'
  );

  const ctx1 = DfpnSolver.buildProofContext(p001, defaultConfig(500));
  const pos1 = DfpnSolver.buildInitialPosition(p001, ctx1);
  const contraMemVer = checker.verifyProofDag(pos1, ctx1, {
    ...rep1,
    hasRegionHint: false,
    regionCoords: [0, 1, 2],
  });
  check(
    !contraMemVer.passed && contraMemVer.errorCode === 'LP-J02',
    'R8 §3 verifyProofDag memory entrypoint rejects contradictory hasRegionHint=false + non-empty regionCoords -> LP-J02',
    `code=${contraMemVer.errorCode}`
  );

  const contraBindVer = checker.verifySerializedLProofJson(rep1.lproofJson, {
    problem: badSpec,
    scope: 'original_root',
  });
  check(
    !contraBindVer.passed && contraBindVer.errorCode === 'LP-J02',
    'R8 §3 verifySerializedLProofJson rejects contradictory expectedBinding.problem -> LP-J02',
    `code=${contraBindVer.errorCode}`
  );

  // R8 §3: Non-boolean problemSetup.hasRegionHint ("false", 0) rejected with LP-J02
  for (const badVal of ['false', 0, []] as unknown[]) {
    const badTypeObj = JSON.parse(rep1.lproofJson) as Record<string, unknown>;
    (badTypeObj.problemSetup as Record<string, unknown>).hasRegionHint = badVal;
    const badTypeVer = checker.verifySerializedLProofJson(
      resignLProof(badTypeObj).json
    );
    check(
      !badTypeVer.passed && badTypeVer.errorCode === 'LP-J02',
      `R8 §3 non-boolean problemSetup.hasRegionHint=${JSON.stringify(badVal)} rejected -> LP-J02`,
      `code=${badTypeVer.errorCode}`
    );
  }
});

// =============================================================================
// Section 7: Real-Problem Solver Breakthrough (p031 Proven + Zero-Leaf Barrier)
// =============================================================================
runSection('Section 7: Real-Problem Solver Breakthrough (p031 + Zero-Leaf Guardrails)', () => {
  const realCfg: SolverConfig = {
    ...defaultConfig(3500),
    maxDepth: 48,
    memoryBudgetMb: 512,
    useProblemDefaultKo: true,
  };

  // p031: full unmodified region, original_root PROVEN_WIN with B[sr] & verified certificate
  const p031 = getSpec('chao_vol1_p031');
  const ctx31 = DfpnSolver.buildProofContext(p031, realCfg);
  const pos31 = DfpnSolver.buildInitialPosition(p031, ctx31);
  const rep31 = new DfpnSolver(realCfg).solveFromPosition(p031, pos31, ctx31);
  check(
    rep31.rootStatus === ProofOutcome.ProvenWin && rep31.bestMoveSgf === 'sr',
    'p031 solves to PROVEN_WIN with bestMove=sr under 3500-node budget',
    `status=${rep31.rootStatus}, best=${rep31.bestMoveSgf}, nodes=${rep31.numNodes}`
  );
  check(
    rep31.numNodes <= 2800 && rep31.prunedOutsideRzCount > 0,
    'p031 stays within <= 2800 nodes with active OutsideRZRevalidated pruning',
    `nodes=${rep31.numNodes}, pruned=${rep31.prunedOutsideRzCount}`
  );
  const mem31 = checker.verifyProofDag(pos31, ctx31, rep31, {
    verifiedScope: 'original_root',
  });
  const file31 = checker.verifySerializedLProofJson(rep31.lproofJson, {
    problem: p031,
    scope: 'original_root',
  });
  check(
    mem31.passed &&
      file31.passed &&
      mem31.canonicalDagChecksum === file31.canonicalDagChecksum,
    'p031 passes memory & external-bound original_root verification with matching canonicalDagChecksum',
    `mem=${mem31.errorCode}, file=${file31.errorCode}`
  );
  console.log(
    `  [INFO] p031: outcome=${rep31.rootStatus}, best=${rep31.bestMoveSgf}, nodes=${rep31.numNodes}, dag=${rep31.proofDagNodes.length}, pruned=${rep31.prunedOutsideRzCount}, timeMs=${rep31.timeMs.toFixed(1)}`
  );

  // Zero-leaf barrier guardrails: previously 0-leaf breadth-stalled real problems must reach terminal leaves
  for (const idPrefix of ['chao_vol1_p057', 'chao_vol1_p060', 'chao_vol2_p162']) {
    const spec = getSpec(idPrefix);
    const rep = new DfpnSolver(realCfg).solveProblem(spec);
    const leafCount = rep.proofDagNodes.filter(
      (n) =>
        n.terminalEvidence === 'BENSON_UCA' ||
        n.terminalEvidence === 'TOKENS_CAPTURED' ||
        n.terminalEvidence === 'DOUBLE_PASS_RESOLUTION'
    ).length;
    check(
      leafCount > 0,
      `${idPrefix} breaks zero-leaf barrier within 3500 nodes`,
      `leaves=${leafCount}, dag=${rep.proofDagNodes.length}, pruned=${rep.prunedOutsideRzCount}`
    );
  }
});

// =============================================================================
// Section 8: R9 §1 Eye-Like Heuristic & AND-Node PASS Score Parity
// =============================================================================
runSection('Section 8: R9 §1 Eye-Like Heuristic & AND-Node PASS Score Parity', () => {
  const cfgRz: SolverConfig = {
    ...defaultConfig(3500),
    maxDepth: 48,
    memoryBudgetMb: 512,
    useProblemDefaultKo: true,
    enableRzPruning: true,
  };
  const cfgNoRz: SolverConfig = {
    ...cfgRz,
    enableRzPruning: false,
  };
  const solverRz = new DfpnSolver(cfgRz);
  const solverNoRz = new DfpnSolver(cfgNoRz);

  const eyeCases: Array<{
    name: string;
    sgf: string;
    crucial: string;
    expectedEyeLike: number;
    expectedPassRz: number;
    expectedPassNoRz: number;
  }> = [
    {
      name: 'full_eye_corner',
      sgf: '(;GM[1]FF[4]SZ[19]PL[W]AB[ba][ab][bb]AW[dd])',
      crucial: 'bb',
      expectedEyeLike: 2,
      expectedPassRz: 3850,
      expectedPassNoRz: 3850,
    },
    {
      name: 'single_tiger_mouth',
      sgf: '(;GM[1]FF[4]SZ[19]PL[W]AB[ba][bb][cb]AW[dd])',
      crucial: 'bb',
      expectedEyeLike: 1,
      expectedPassRz: 3450,
      expectedPassNoRz: 360,
    },
    {
      name: 'double_tiger_mouth',
      sgf: '(;GM[1]FF[4]SZ[19]PL[W]AB[ca][cb][cc][dc][ec][eb][ea]AW[gg])',
      crucial: 'dc',
      expectedEyeLike: 2,
      expectedPassRz: 3850,
      expectedPassNoRz: 3850,
    },
    {
      name: 'diag_enemy_full_eye',
      sgf: '(;GM[1]FF[4]SZ[19]PL[W]AB[ba][ab][ca][cb][cc][bc][ac]AW[bb])',
      crucial: 'ba',
      expectedEyeLike: 2,
      expectedPassRz: 3850,
      expectedPassNoRz: 3850,
    },
  ];

  for (const tc of eyeCases) {
    const raw: RawStudyLdRzProblemJson = {
      masked_sgf_str: tc.sgf,
      winning_color: 'b',
      turn_color: 'w',
      black_crucial_stone: tc.crucial,
      white_crucial_stone: '',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_ko_rule: 'disallow_ko',
      white_ko_rule: 'allow_ko',
      region: 'aa,ba,ca,da,ab,bb,cb,db,ac,bc,cc,dc',
      answer_firstmove: '',
    };
    const spec = parseStudyLdRzJsonToProblemSpec(`r9_eye_${tc.name}`, raw);
    const ctx = DfpnSolver.buildProofContext(spec, cfgRz);
    const pos = DfpnSolver.buildInitialPosition(spec, ctx);
    const eyeLike = solverRz.evaluateParentEyeLikeCount(pos, ctx);
    const passRz = solverRz.evaluatePassMoveScore(pos, ctx, false);
    const passNoRz = solverNoRz.evaluatePassMoveScore(pos, ctx, false);
    check(
      eyeLike === tc.expectedEyeLike &&
        passRz === tc.expectedPassRz &&
        passNoRz === tc.expectedPassNoRz,
      `R9 §1 eye-shape ${tc.name}: eyeLike=${tc.expectedEyeLike}, passRz=${tc.expectedPassRz}, passNoRz=${tc.expectedPassNoRz}`,
      `got eyeLike=${eyeLike}, passRz=${passRz}, passNoRz=${passNoRz}`
    );
  }

  // Real p031 defensive line: B[sr] -> W[pass] -> B[qs] forms two tiger's mouths (rs, ss)
  const p031 = getSpec('chao_vol1_p031');
  const ctx31 = DfpnSolver.buildProofContext(p031, cfgRz);
  const pos31 = DfpnSolver.buildInitialPosition(p031, ctx31);
  const okSr = pos31.playMove(sgfToCoord('sr', 19));
  const okPass = pos31.playMove(PASS_MOVE);
  const okQs = pos31.playMove(sgfToCoord('qs', 19));
  const p31Eye = solverRz.evaluateParentEyeLikeCount(pos31, ctx31);
  const p31Pass = solverRz.evaluatePassMoveScore(pos31, ctx31, false);
  const solverNoOrder = new DfpnSolver({
    ...cfgRz,
    enableFastCaptureOrdering: false,
  });
  const p31PassNoOrder = solverNoOrder.evaluatePassMoveScore(pos31, ctx31, false);
  check(
    okSr && okPass && okQs && p31Eye === 2 && p31Pass === 3850 && p31PassNoOrder === 0,
    'R9/R10 §1 p031 after B[sr]->W[pass]->B[qs] yields eyeLike=2, PASS score=3850 (ordering on) and 0 (ordering off)',
    `ok=${okSr}/${okPass}/${okQs}, eyeLike=${p31Eye}, passScore=${p31Pass}, passNoOrder=${p31PassNoOrder}`
  );

  // R10 generic path observer (default off): enabling tracePathFilters must be read-only
  // and emit enter/select/rep_proof/rz_prune/return events without altering canonicalDagChecksum.
  const p042 = getSpec('chao_vol1_p042');
  const rep42Plain = new DfpnSolver(cfgRz).solveProblem(p042);
  const traceKinds = new Set<string>();
  let repProofCount = 0;
  let rzPruneCount = 0;
  const rep42Traced = new DfpnSolver({
    ...cfgRz,
    tracePathFilters: ['rs'],
    onPathTrace: (ev) => {
      traceKinds.add(ev.kind);
      if (ev.kind === 'rep_proof') repProofCount++;
      if (ev.kind === 'rz_prune') rzPruneCount++;
    },
  }).solveProblem(p042);
  const verPlain = checker.verifySerializedLProofJson(rep42Plain.lproofJson, {
    problem: p042,
    scope: 'original_root',
  });
  const verTraced = checker.verifySerializedLProofJson(rep42Traced.lproofJson, {
    problem: p042,
    scope: 'original_root',
  });
  check(
    rep42Plain.numNodes === rep42Traced.numNodes &&
      verPlain.passed &&
      verTraced.passed &&
      verPlain.canonicalDagChecksum === verTraced.canonicalDagChecksum &&
      traceKinds.has('enter') &&
      traceKinds.has('select') &&
      traceKinds.has('return') &&
      repProofCount > 0 &&
      rzPruneCount > 0,
    'R10 generic path trace observer is read-only (identical nodes & canonicalDagChecksum) and logs enter/select/rep_proof/rz_prune/return on p042 rs',
    `nodes=${rep42Plain.numNodes}/${rep42Traced.numNodes}, rep=${repProofCount}, prunes=${rzPruneCount}`
  );
});

runSection('Section 9: R11 Observer Terminal Completeness, Branch Coverage Snapshots & Sub-Proof Fragment Verifier', () => {
  const cfgRz: SolverConfig = {
    ...defaultConfig(3500),
    maxDepth: 48,
    memoryBudgetMb: 512,
    enableRzPruning: true,
    useProblemDefaultKo: true,
  };

  // 9.1 p001 watching ['', 'ba']: immediate BENSON_UCA terminal leaf MUST emit paired enter + return
  const p001 = getSpec('p001');
  const p001Events: import('../src/engine/types').SearchPathTraceEvent[] = [];
  const rep001 = new DfpnSolver({
    ...cfgRz,
    tracePathFilters: ['', 'ba'],
    onPathTrace: (ev) => p001Events.push(ev),
  }).solveProblem(p001);

  const baEnters = p001Events.filter((e) => e.path === 'ba' && e.kind === 'enter');
  const baReturns = p001Events.filter((e) => e.path === 'ba' && e.kind === 'return');
  const baSnap = rep001.branchCoverageSnapshots?.find((s) => s.path === 'ba');
  check(
    baEnters.length === 1 &&
      baReturns.length === 1 &&
      baEnters[0].invocationId === baReturns[0].invocationId &&
      baEnters[0].entryCallIndex === baReturns[0].entryCallIndex &&
      baReturns[0].exitReason === 'terminal' &&
      baReturns[0].terminalEvidence === 'BENSON_UCA' &&
      baReturns[0].dagNodeId === 0,
    'R11 §1 p001 watching ["", "ba"] emits paired enter + return on immediate BENSON_UCA terminal leaf ba',
    `enters=${baEnters.length}, returns=${baReturns.length}, exit=${baReturns[0]?.exitReason}, ev=${baReturns[0]?.terminalEvidence}, dag=${baReturns[0]?.dagNodeId}`
  );
  check(
    Boolean(baSnap) &&
      baSnap!.nodeOutcome === ProofOutcome.ProvenWin &&
      baSnap!.nodeDagNodeId === 0 &&
      baSnap!.terminalEvidence === 'BENSON_UCA' &&
      baSnap!.runSource === 'original_root',
    'R11 §2 p001 branchCoverageSnapshots captures direct terminal child ba with BENSON_UCA evidence',
    `snap=${JSON.stringify(baSnap && { outcome: baSnap.nodeOutcome, dag: baSnap.nodeDagNodeId, ev: baSnap.terminalEvidence })}`
  );

  // 9.2 p162 original root vs standalone p162/sr/pass
  const p162 = getSpec('chao_vol2_p162');
  const ctx162 = DfpnSolver.buildProofContext(p162, cfgRz);
  const rep162Orig = new DfpnSolver(cfgRz).solveProblem(p162);
  const srSnap = rep162Orig.branchCoverageSnapshots?.find((s) => s.path === 'sr');
  check(
    rep162Orig.rootStatus === ProofOutcome.Unknown &&
      Boolean(srSnap) &&
      srSnap!.runSource === 'original_root' &&
      srSnap!.rootOutcome === ProofOutcome.Unknown &&
      srSnap!.totalLegalMoves === 130 &&
      srSnap!.closedCount === 0 &&
      srSnap!.provenSourceCount === 0 &&
      srSnap!.rzRevalidatedCount === 0 &&
      srSnap!.deferredOutsideRzCount === 0 &&
      srSnap!.nodeDagNodeId === -1,
    'R11 §2 p162 original-root snapshot accurately reports sr coverage 0/130 (UNKNOWN, zero RZ/source closure)',
    `root=${rep162Orig.rootStatus}, total=${srSnap?.totalLegalMoves}, closed=${srSnap?.closedCount}, dag=${srSnap?.nodeDagNodeId}`
  );

  const srMove = sgfToCoord('sr', 19);
  const frag162Sr = checker.verifySubproofFragment({
    problem: p162,
    context: ctx162,
    report: rep162Orig,
    targetPathMoves: [srMove],
    targetDagNodeId: srSnap?.nodeDagNodeId ?? -1,
  });
  check(
    frag162Sr.sourceReceipt.status === 'UNCLOSED' &&
      !frag162Sr.sourceReceipt.passed &&
      frag162Sr.sourceReceipt.errorCode === 'LP-U01' &&
      frag162Sr.queryReplayReceipt.status === 'NOT_REQUESTED',
    'R11 §3 verifySubproofFragment on unclosed original-root p162/sr returns UNCLOSED (LP-U01)',
    `status=${frag162Sr.sourceReceipt.status}, code=${frag162Sr.sourceReceipt.errorCode}`
  );

  // Standalone p162/sr/pass re-solve
  const subPos162 = DfpnSolver.buildInitialPosition(p162, ctx162);
  const playedSr = subPos162.playMove(srMove);
  const playedPass = subPos162.playMove(PASS_MOVE);
  const rep162Sub = new DfpnSolver(cfgRz).solveFromPosition(p162, subPos162, ctx162);
  const ver162Traced = checker.verifySerializedLProofJson(rep162Sub.lproofJson, {
    problem: p162,
    scope: 'traced_within_rules',
  });
  const ver162Orig = checker.verifySerializedLProofJson(rep162Sub.lproofJson, {
    problem: p162,
    scope: 'original_root',
  });
  const subRootSnap = rep162Sub.branchCoverageSnapshots?.find((s) => s.path === '');
  check(
    playedSr.legal &&
      playedPass.legal &&
      rep162Sub.rootStatus === ProofOutcome.ProvenWin &&
      rep162Sub.bestMoveSgf === 'os' &&
      rep162Sub.numNodes === 315 &&
      subRootSnap?.runSource === 'standalone_subposition' &&
      ver162Traced.passed &&
      !ver162Orig.passed &&
      ver162Orig.errorCode === 'LP-P02',
    'R11 §4 standalone p162/sr/pass solves in 315 nodes (best=os), traced_within_rules=PASS, original_root=LP-P02',
    `status=${rep162Sub.rootStatus}, best=${rep162Sub.bestMoveSgf}, nodes=${rep162Sub.numNodes}, traced=${ver162Traced.errorCode}, orig=${ver162Orig.errorCode}`
  );

  // 9.3 p042 original root: verifySubproofFragment source verification + outside-RZ query replay + tamper/binding rejections
  const p042 = getSpec('chao_vol1_p042');
  const ctx42 = DfpnSolver.buildProofContext(p042, cfgRz);
  const rep42 = new DfpnSolver(cfgRz).solveProblem(p042);
  const rsSnap = rep42.branchCoverageSnapshots?.find((s) => s.path === 'rs');
  const passEntry = rsSnap?.moves.find((m) => m.move === PASS_MOVE);
  const rzEntry = rsSnap?.moves.find((m) => m.status === 'RZ_REVALIDATED');
  const rsMove = sgfToCoord('rs', 19);

  check(
    rep42.numNodes === 331 &&
      rep42.bestMoveSgf === 'rs' &&
      Boolean(rsSnap) &&
      rsSnap!.closedCount === rsSnap!.totalLegalMoves &&
      rsSnap!.provenSourceCount > 0 &&
      rsSnap!.rzRevalidatedCount > 0 &&
      rsSnap!.deferredOutsideRzCount === 0 &&
      Boolean(passEntry) &&
      passEntry!.status === 'PROVEN_SOURCE' &&
      passEntry!.dagNodeId >= 0 &&
      Boolean(rzEntry),
    'R11 §2 p042/rs snapshot achieves full closure (source + RZ revalidated, 0 deferred) with unchanged 331-node baseline',
    `nodes=${rep42.numNodes}, closed=${rsSnap?.closedCount}/${rsSnap?.totalLegalMoves}, src=${rsSnap?.provenSourceCount}, rz=${rsSnap?.rzRevalidatedCount}, def=${rsSnap?.deferredOutsideRzCount}`
  );

  if (passEntry && rzEntry) {
    const frag42 = checker.verifySubproofFragment({
      problem: p042,
      context: ctx42,
      report: rep42,
      targetPathMoves: [rsMove, PASS_MOVE],
      targetDagNodeId: passEntry.dagNodeId,
      queryPathMoves: [rsMove, rzEntry.move],
    });
    check(
      frag42.sourceReceipt.status === 'SOURCE_VERIFIED' &&
        frag42.sourceReceipt.passed &&
        frag42.sourceReceipt.errorCode === 'PASS' &&
        frag42.queryReplayReceipt.status === 'QUERY_REPLAY_VERIFIED' &&
        frag42.queryReplayReceipt.passed &&
        frag42.queryReplayReceipt.errorCode === 'PASS',
      `R11 §3 verifySubproofFragment verifies p042 rs/pass source AND query replay on rs/${rzEntry.moveSgf} independently`,
      `src=${frag42.sourceReceipt.status}/${frag42.sourceReceipt.errorCode}, q=${frag42.queryReplayReceipt.status}/${frag42.queryReplayReceipt.errorCode}`
    );

    // Binding mismatch rejection (LP-N10)
    const fragWrongPath = checker.verifySubproofFragment({
      problem: p042,
      context: ctx42,
      report: rep42,
      targetPathMoves: [rsMove, rzEntry.move],
      targetDagNodeId: passEntry.dagNodeId,
    });
    check(
      fragWrongPath.sourceReceipt.status === 'VERIFICATION_FAILED' &&
        !fragWrongPath.sourceReceipt.passed &&
        fragWrongPath.sourceReceipt.errorCode === 'LP-N10',
      'R11 §3 verifySubproofFragment rejects wrong-path state binding with LP-N10',
      `status=${fragWrongPath.sourceReceipt.status}, code=${fragWrongPath.sourceReceipt.errorCode}`
    );

    // Tampered fragment rejection (dropping children from rs/pass DAG node)
    const tamperedReport = {
      ...rep42,
      proofDagNodes: rep42.proofDagNodes.map((n) =>
        n.nodeId === passEntry.dagNodeId
          ? { ...n, childNodeIds: [], childMoves: [] }
          : n
      ),
    };
    const fragTampered = checker.verifySubproofFragment({
      problem: p042,
      context: ctx42,
      report: tamperedReport,
      targetPathMoves: [rsMove, PASS_MOVE],
      targetDagNodeId: passEntry.dagNodeId,
    });
    check(
      fragTampered.sourceReceipt.status === 'VERIFICATION_FAILED' &&
        !fragTampered.sourceReceipt.passed,
      'R11 §3 verifySubproofFragment rejects tampered rs/pass fragment with missing children',
      `status=${fragTampered.sourceReceipt.status}, code=${fragTampered.sourceReceipt.errorCode}`
    );
  }

  // Verify p031 baseline stays untouched at 1892 nodes
  const p031 = getSpec('chao_vol1_p031');
  const rep031 = new DfpnSolver(cfgRz).solveProblem(p031);
  check(
    rep031.rootStatus === ProofOutcome.ProvenWin &&
      rep031.bestMoveSgf === 'sr' &&
      rep031.numNodes === 1892,
    'R11 baseline guard: p031 still proves B[sr] in exactly 1892 nodes',
    `status=${rep031.rootStatus}, best=${rep031.bestMoveSgf}, nodes=${rep031.numNodes}`
  );
});

runSection('Section 10: R12 Fragment Contract Binding, Full-Table Integrity, Run-Source Provenance & Coverage Semantics', () => {
  const cfgRz: SolverConfig = {
    ...defaultConfig(3500),
    maxDepth: 48,
    memoryBudgetMb: 512,
    enableRzPruning: true,
    useProblemDefaultKo: true,
  };

  // 10.1 R12 §2: Problem-context goal conflict MUST be rejected with LP-P01 even when old context is passed
  const p001 = getSpec('p001');
  const ctx001Live = DfpnSolver.buildProofContext(p001, cfgRz);
  const rep001 = new DfpnSolver(cfgRz).solveProblem(p001);
  const baMove = sgfToCoord('ba', 19);
  const p001ToKill: TsumegoProblemSpec = {
    ...p001,
    blackSearchGoal: SearchGoal.ToKill,
  };

  const fragGoalConflict = checker.verifySubproofFragment({
    problem: p001ToKill,
    context: ctx001Live,
    report: rep001,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
    queryPathMoves: [baMove],
  });
  check(
    fragGoalConflict.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      !fragGoalConflict.sourceReceipt.passed &&
      fragGoalConflict.sourceReceipt.errorCode === 'LP-P01' &&
      fragGoalConflict.queryReplayReceipt.status === 'QUERY_REPLAY_FAILED' &&
      fragGoalConflict.queryReplayReceipt.errorCode === 'LP-P01',
    'R12 §2 rejects p001 ToLive->ToKill goal conflict even when stale ToLive context is explicitly passed (LP-P01)',
    `src=${fragGoalConflict.sourceReceipt.status}/${fragGoalConflict.sourceReceipt.errorCode}, q=${fragGoalConflict.queryReplayReceipt.status}/${fragGoalConflict.queryReplayReceipt.errorCode}`
  );

  // Legitimate runtime config override (attackerAllowKo: true) MUST pass when report & context match,
  // and MUST fail (LP-P01) when caller passes mismatched ko config.
  const cfgKoOverride: SolverConfig = {
    ...cfgRz,
    useProblemDefaultKo: false,
    attackerAllowKo: true,
    defenderAllowKo: true,
  };
  const ctx001KoOverride = DfpnSolver.buildProofContext(p001, cfgKoOverride);
  const rep001KoOverride = new DfpnSolver(cfgKoOverride).solveProblem(p001);
  const fragKoOverrideOk = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001KoOverride,
    report: rep001KoOverride,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  const fragKoOverrideMismatch = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001Live,
    report: rep001KoOverride,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  check(
    fragKoOverrideOk.sourceReceipt.status === 'SOURCE_VERIFIED' &&
      fragKoOverrideOk.sourceReceipt.passed &&
      fragKoOverrideMismatch.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      fragKoOverrideMismatch.sourceReceipt.errorCode === 'LP-P01',
    'R12 §2 preserves legitimate runtime ko override (PASS) while rejecting mismatched ko context against report contract (LP-P01)',
    `ok=${fragKoOverrideOk.sourceReceipt.status}/${fragKoOverrideOk.sourceReceipt.errorCode}, mismatch=${fragKoOverrideMismatch.sourceReceipt.status}/${fragKoOverrideMismatch.sourceReceipt.errorCode}`
  );

  // 10.2 R12 §3: Full-table index, cross-table, descendant corruption & out-of-bounds positive DAG ID
  const cloneReport = (r: typeof rep001): typeof rep001 =>
    JSON.parse(JSON.stringify(r));

  // Control: intact p001 ba leaf & root pass in full_state_table mode
  const frag001RootOk = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001Live,
    report: rep001,
    targetPathMoves: [],
    targetDagNodeId: rep001.rootDagNodeId,
  });
  check(
    frag001RootOk.sourceReceipt.status === 'SOURCE_VERIFIED' &&
      frag001RootOk.sourceReceipt.passed &&
      frag001RootOk.sourceReceipt.verificationMode === 'full_state_table' &&
      frag001RootOk.runSource === 'original_root' &&
      frag001RootOk.runRootOutcome === ProofOutcome.ProvenWin &&
      frag001RootOk.originalRootOutcome === ProofOutcome.ProvenWin,
    'R12 §3 positive control: intact p001 root verifies in full_state_table mode',
    `status=${frag001RootOk.sourceReceipt.status}, mode=${frag001RootOk.sourceReceipt.verificationMode}`
  );

  // (a) ba leaf stateId out of bounds -> LP-S10
  const rBadStateId = cloneReport(rep001);
  rBadStateId.proofDagNodes[0].stateId = 999;
  const fBadStateId = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001Live,
    report: rBadStateId,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  check(
    fBadStateId.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      fBadStateId.sourceReceipt.errorCode === 'LP-S10',
    'R12 §3 rejects ba leaf with out-of-bounds stateId (LP-S10)',
    `status=${fBadStateId.sourceReceipt.status}, code=${fBadStateId.sourceReceipt.errorCode}`
  );

  // (b) ba leaf historyId out of bounds -> LP-S10
  const rBadHistId = cloneReport(rep001);
  rBadHistId.proofDagNodes[0].historyId = 999;
  const fBadHistId = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001Live,
    report: rBadHistId,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  check(
    fBadHistId.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      fBadHistId.sourceReceipt.errorCode === 'LP-S10',
    'R12 §3 rejects ba leaf with out-of-bounds historyId (LP-S10)',
    `status=${fBadHistId.sourceReceipt.status}, code=${fBadHistId.sourceReceipt.errorCode}`
  );

  // (c) stateTable[ba.stateId].historyId changed to 0 (disagrees with node.historyId) -> LP-S10
  const rCrossHist = cloneReport(rep001);
  const baStateId = rCrossHist.proofDagNodes[0].stateId;
  rCrossHist.stateTable[baStateId].historyId = 0;
  const fCrossHist = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001Live,
    report: rCrossHist,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  check(
    fCrossHist.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      fCrossHist.sourceReceipt.errorCode === 'LP-S10',
    'R12 §3 rejects cross-table state.historyId != node.historyId mismatch on ba leaf (LP-S10)',
    `status=${fCrossHist.sourceReceipt.status}, code=${fCrossHist.sourceReceipt.errorCode}`
  );

  // (d) Root target with corrupted descendant ba stateId -> LP-S10
  const fDescBadStateId = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001Live,
    report: rBadStateId,
    targetPathMoves: [],
    targetDagNodeId: rep001.rootDagNodeId,
  });
  check(
    fDescBadStateId.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      fDescBadStateId.sourceReceipt.errorCode === 'LP-S10',
    'R12 §3 root verification rejects out-of-bounds stateId on descendant ba (LP-S10)',
    `status=${fDescBadStateId.sourceReceipt.status}, code=${fDescBadStateId.sourceReceipt.errorCode}`
  );

  // (e) Root target with descendant ba stateTable row whiteCoords cleared -> LP-N10
  const rDescWhiteCleared = cloneReport(rep001);
  rDescWhiteCleared.stateTable[baStateId].whiteCoords = [];
  const fDescWhiteCleared = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001Live,
    report: rDescWhiteCleared,
    targetPathMoves: [],
    targetDagNodeId: rep001.rootDagNodeId,
  });
  check(
    fDescWhiteCleared.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      fDescWhiteCleared.sourceReceipt.errorCode === 'LP-N10',
    'R12 §3 root verification rejects descendant ba state row with cleared whiteCoords (LP-N10)',
    `status=${fDescWhiteCleared.sourceReceipt.status}, code=${fDescWhiteCleared.sourceReceipt.errorCode}`
  );

  // (f) Positive out-of-bounds DAG node ID -> VERIFICATION_FAILED / LP-N01 (distinct from -1 -> UNCLOSED / LP-U01)
  const fPosOob = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001Live,
    report: rep001,
    targetPathMoves: [],
    targetDagNodeId: 999,
  });
  const fUnclosedSentinel = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001Live,
    report: rep001,
    targetPathMoves: [],
    targetDagNodeId: -1,
  });
  check(
    fPosOob.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      fPosOob.sourceReceipt.errorCode === 'LP-N01' &&
      fUnclosedSentinel.sourceReceipt.status === 'UNCLOSED' &&
      fUnclosedSentinel.sourceReceipt.errorCode === 'LP-U01',
    'R12 §3 distinguishes corrupted positive out-of-bounds targetDagNodeId (LP-N01) from unclosed sentinel -1 (LP-U01)',
    `posOob=${fPosOob.sourceReceipt.status}/${fPosOob.sourceReceipt.errorCode}, sentinel=${fUnclosedSentinel.sourceReceipt.status}/${fUnclosedSentinel.sourceReceipt.errorCode}`
  );

  // (g) Explicit compact_dag semantic mode when stateTable is absent
  const rCompact = cloneReport(rep001);
  rCompact.stateTable = [];
  rCompact.historyTable = [];
  const fCompact = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001Live,
    report: rCompact,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  check(
    fCompact.sourceReceipt.status === 'SOURCE_VERIFIED' &&
      fCompact.sourceReceipt.verificationMode === 'compact_dag',
    'R12 §3 explicitly tags state-table-free fragment checks with verificationMode=compact_dag',
    `status=${fCompact.sourceReceipt.status}, mode=${fCompact.sourceReceipt.verificationMode}`
  );

  // 10.3 R12 §4: Authentic runSource derivation & separating runRootOutcome vs originalRootOutcome on p162
  const p162 = getSpec('chao_vol2_p162');
  const ctx162 = DfpnSolver.buildProofContext(p162, cfgRz);
  const rep162Orig = new DfpnSolver(cfgRz).solveProblem(p162);
  const srMove = sgfToCoord('sr', 19);
  const subPos162 = DfpnSolver.buildInitialPosition(p162, ctx162);
  subPos162.playMove(srMove);
  subPos162.playMove(PASS_MOVE);
  const rep162Sub = new DfpnSolver(cfgRz).solveFromPosition(
    p162,
    subPos162,
    ctx162
  );

  // Omitting runSource MUST still derive standalone_subposition and keep originalRootOutcome === null!
  const frag162Omitted = checker.verifySubproofFragment({
    problem: p162,
    context: ctx162,
    report: rep162Sub,
    targetPathMoves: [srMove, PASS_MOVE],
    targetDagNodeId: rep162Sub.rootDagNodeId,
  });
  check(
    frag162Omitted.runSource === 'standalone_subposition' &&
      frag162Omitted.runStartPathSgf.join('/') === 'sr/pass' &&
      frag162Omitted.runRootOutcome === ProofOutcome.ProvenWin &&
      frag162Omitted.originalRootOutcome === null &&
      frag162Omitted.sourceReceipt.status === 'SOURCE_VERIFIED' &&
      frag162Omitted.sourceReceipt.passed,
    'R12 §4 omitting runSource on standalone p162/sr/pass derives standalone_subposition and leaves originalRootOutcome=null (never upgrades original root to PROVEN_WIN)',
    `src=${frag162Omitted.runSource}, start=${frag162Omitted.runStartPathSgf.join('/')}, runRoot=${frag162Omitted.runRootOutcome}, origRoot=${String(frag162Omitted.originalRootOutcome)}, receipt=${frag162Omitted.sourceReceipt.status}`
  );

  // Passing explicit contradictory runSource: 'original_root' MUST reject with LP-P02
  const frag162Contradict = checker.verifySubproofFragment({
    problem: p162,
    context: ctx162,
    report: rep162Sub,
    targetPathMoves: [srMove, PASS_MOVE],
    targetDagNodeId: rep162Sub.rootDagNodeId,
    runSource: 'original_root',
  });
  check(
    frag162Contradict.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      frag162Contradict.sourceReceipt.errorCode === 'LP-P02' &&
      frag162Contradict.runSource === 'standalone_subposition' &&
      frag162Contradict.originalRootOutcome === null,
    'R12 §4 rejects explicit contradictory runSource=original_root on standalone p162/sr/pass report (LP-P02)',
    `status=${frag162Contradict.sourceReceipt.status}, code=${frag162Contradict.sourceReceipt.errorCode}, derived=${frag162Contradict.runSource}`
  );

  // Target path not belonging to standalone run starting trajectory MUST reject with LP-P02
  const frag162WrongPrefix = checker.verifySubproofFragment({
    problem: p162,
    context: ctx162,
    report: rep162Sub,
    targetPathMoves: [],
    targetDagNodeId: rep162Sub.rootDagNodeId,
  });
  check(
    frag162WrongPrefix.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      frag162WrongPrefix.sourceReceipt.errorCode === 'LP-P02',
    'R12 §4 rejects targetPathMoves outside standalone subposition arrival prefix (LP-P02)',
    `status=${frag162WrongPrefix.sourceReceipt.status}, code=${frag162WrongPrefix.sourceReceipt.errorCode}`
  );

  // Supplying authentic originalRootReport exposes originalRootOutcome=UNKNOWN alongside runRootOutcome=PROVEN_WIN
  const frag162WithOrig = checker.verifySubproofFragment({
    problem: p162,
    context: ctx162,
    report: rep162Sub,
    targetPathMoves: [srMove, PASS_MOVE],
    targetDagNodeId: rep162Sub.rootDagNodeId,
    originalRootReport: rep162Orig,
  });
  check(
    frag162WithOrig.runSource === 'standalone_subposition' &&
      frag162WithOrig.runRootOutcome === ProofOutcome.ProvenWin &&
      frag162WithOrig.originalRootOutcome === ProofOutcome.Unknown &&
      frag162WithOrig.sourceReceipt.passed,
    'R12 §4 binding authentic originalRootReport reports runRootOutcome=PROVEN_WIN alongside originalRootOutcome=UNKNOWN',
    `runRoot=${frag162WithOrig.runRootOutcome}, origRoot=${String(frag162WithOrig.originalRootOutcome)}`
  );

  // 10.4 R12 §5: Outcome-aware coverageObligation (p007 OR loss = FULL_COVERAGE) + p042 140th move replay
  const p007 = getSpec('p007');
  const rep007 = new DfpnSolver(cfgRz).solveProblem(p007);
  const p007RootSnap = rep007.branchCoverageSnapshots?.find((s) => s.path === '');
  const p001RootSnap = rep001.branchCoverageSnapshots?.find((s) => s.path === '');
  check(
    Boolean(p007RootSnap) &&
      p007RootSnap!.nodeRole === 'OR_ATTACKER' &&
      p007RootSnap!.nodeOutcome === ProofOutcome.ProvenLoss &&
      p007RootSnap!.coverageObligation === 'FULL_COVERAGE' &&
      p007RootSnap!.closedCount === 3 &&
      p007RootSnap!.totalLegalMoves === 3 &&
      p001RootSnap?.nodeRole === 'OR_ATTACKER' &&
      p001RootSnap?.coverageObligation === 'SINGLE_WITNESS',
    'R12 §5 p007 OR PROVEN_LOSS (3/3) reports nodeRole=OR_ATTACKER & coverageObligation=FULL_COVERAGE while p001 OR PROVEN_WIN reports SINGLE_WITNESS',
    `p007=${p007RootSnap?.nodeRole}/${p007RootSnap?.coverageObligation} (${p007RootSnap?.closedCount}/${p007RootSnap?.totalLegalMoves}), p001=${p001RootSnap?.coverageObligation}`
  );

  const p042 = getSpec('chao_vol1_p042');
  const ctx42 = DfpnSolver.buildProofContext(p042, cfgRz);
  const rep42 = new DfpnSolver(cfgRz).solveProblem(p042);
  const rsSnap = rep42.branchCoverageSnapshots?.find((s) => s.path === 'rs');
  const passEntry42 = rsSnap?.moves.find((m) => m.move === PASS_MOVE);
  const lastMoveEntry42 = rsSnap?.moves[139];
  const rsMove = sgfToCoord('rs', 19);
  check(
    Boolean(rsSnap) &&
      rsSnap!.nodeRole === 'AND_DEFENDER' &&
      rsSnap!.coverageObligation === 'FULL_COVERAGE' &&
      rsSnap!.moves.length === 140 &&
      Boolean(passEntry42) &&
      Boolean(lastMoveEntry42),
    'R12 §5 p042/rs exposes all 140 legal moves with nodeRole=AND_DEFENDER & coverageObligation=FULL_COVERAGE',
    `role=${rsSnap?.nodeRole}, obl=${rsSnap?.coverageObligation}, len=${rsSnap?.moves.length}`
  );
  if (passEntry42 && lastMoveEntry42) {
    const frag42Tail = checker.verifySubproofFragment({
      problem: p042,
      context: ctx42,
      report: rep42,
      targetPathMoves: [rsMove, PASS_MOVE],
      targetDagNodeId: passEntry42.dagNodeId,
      queryPathMoves: [rsMove, lastMoveEntry42.move],
    });
    check(
      frag42Tail.sourceReceipt.status === 'SOURCE_VERIFIED' &&
        frag42Tail.sourceReceipt.verificationMode === 'full_state_table' &&
        frag42Tail.queryReplayReceipt.status === 'QUERY_REPLAY_VERIFIED',
      `R12 §5 p042 rs/pass source + 140th sibling move (${lastMoveEntry42.moveSgf}) query replay passes in full_state_table mode`,
      `src=${frag42Tail.sourceReceipt.status}/${frag42Tail.sourceReceipt.verificationMode}, q=${frag42Tail.queryReplayReceipt.status}`
    );
  }
});

runSection('Section 11: R13 Original-Root Binding, Entry-Point-Invariant Full-Table Audit & Unified Run-Contract Verification', () => {
  const cfgRz: SolverConfig = {
    ...defaultConfig(3500),
    maxDepth: 48,
    memoryBudgetMb: 512,
    enableRzPruning: true,
    useProblemDefaultKo: true,
  };
  const cloneReport = <T,>(r: T): T => JSON.parse(JSON.stringify(r));

  // 11.1 R13 §1: Authentic originalRootOutcome binding & rejection of cross-contract / unverified originalRootReport
  const p162 = getSpec('chao_vol2_p162');
  const ctx162 = DfpnSolver.buildProofContext(p162, cfgRz);
  const rep162Orig = new DfpnSolver(cfgRz).solveProblem(p162);
  const srMove = sgfToCoord('sr', 19);
  const subPos162 = DfpnSolver.buildInitialPosition(p162, ctx162);
  subPos162.playMove(srMove);
  subPos162.playMove(PASS_MOVE);
  const rep162Sub = new DfpnSolver(cfgRz).solveFromPosition(
    p162,
    subPos162,
    ctx162
  );

  // Empty-region same-board p162 variant produces PROVEN_LOSS in ~3 nodes
  const p162EmptyRegion: TsumegoProblemSpec = {
    ...p162,
    hasRegionHint: true,
    regionCoords: [],
  };
  const rep162Empty = new DfpnSolver(cfgRz).solveProblem(p162EmptyRegion);
  const vr162EmptyFile = checker.verifySerializedLProofJson(
    rep162Empty.lproofJson,
    { problem: p162, context: ctx162, scope: 'original_root' }
  );
  check(
    rep162Empty.rootStatus === ProofOutcome.ProvenLoss &&
      !vr162EmptyFile.passed &&
      vr162EmptyFile.errorCode === 'LP-P01',
    'R13 §1 setup: empty-region p162 variant yields PROVEN_LOSS and fails whole-file original_root check with LP-P01',
    `variantStatus=${rep162Empty.rootStatus}, fileErr=${vr162EmptyFile.errorCode}`
  );

  // Positive control: official UNKNOWN originalRootReport binds cleanly as UNKNOWN (3500 nodes)
  const frag162OfficialOrig = checker.verifySubproofFragment({
    problem: p162,
    context: ctx162,
    report: rep162Sub,
    targetPathMoves: [srMove, PASS_MOVE],
    targetDagNodeId: rep162Sub.rootDagNodeId,
    originalRootReport: rep162Orig,
  });
  check(
    frag162OfficialOrig.originalRootOutcome === ProofOutcome.Unknown &&
      frag162OfficialOrig.originalRootNodes === 3500 &&
      frag162OfficialOrig.originalRootBindingNote === undefined &&
      frag162OfficialOrig.runRootOutcome === ProofOutcome.ProvenWin &&
      frag162OfficialOrig.sourceReceipt.status === 'SOURCE_VERIFIED' &&
      frag162OfficialOrig.sourceReceipt.passed,
    'R13 §1 positive control: official p162 UNKNOWN originalRootReport binds originalRootOutcome=UNKNOWN (3500 nodes) alongside standalone PROVEN_WIN',
    `orig=${String(frag162OfficialOrig.originalRootOutcome)}, nodes=${String(frag162OfficialOrig.originalRootNodes)}, note=${String(frag162OfficialOrig.originalRootBindingNote)}`
  );

  // Counterexample: attaching empty-region PROVEN_LOSS variant as originalRootReport MUST NOT taint originalRootOutcome!
  const frag162VariantOrig = checker.verifySubproofFragment({
    problem: p162,
    context: ctx162,
    report: rep162Sub,
    targetPathMoves: [srMove, PASS_MOVE],
    targetDagNodeId: rep162Sub.rootDagNodeId,
    originalRootReport: rep162Empty,
  });
  check(
    frag162VariantOrig.originalRootOutcome === null &&
      Boolean(frag162VariantOrig.originalRootBindingNote?.includes('LP-P01')) &&
      frag162VariantOrig.runRootOutcome === ProofOutcome.ProvenWin &&
      frag162VariantOrig.sourceReceipt.status === 'SOURCE_VERIFIED' &&
      frag162VariantOrig.sourceReceipt.passed,
    'R13 §1 rejects empty-region p162 PROVEN_LOSS variant attached as originalRootReport (originalRootOutcome=null with LP-P01 note) while preserving standalone sourceReceipt',
    `orig=${String(frag162VariantOrig.originalRootOutcome)}, note=${frag162VariantOrig.originalRootBindingNote}, src=${frag162VariantOrig.sourceReceipt.status}`
  );

  // Counterexample: attaching standalone subposition report as originalRootReport MUST NOT upgrade originalRootOutcome!
  const frag162SubAsOrig = checker.verifySubproofFragment({
    problem: p162,
    context: ctx162,
    report: rep162Sub,
    targetPathMoves: [srMove, PASS_MOVE],
    targetDagNodeId: rep162Sub.rootDagNodeId,
    originalRootReport: rep162Sub,
  });
  check(
    frag162SubAsOrig.originalRootOutcome === null &&
      Boolean(frag162SubAsOrig.originalRootBindingNote?.includes('LP-P02')) &&
      frag162SubAsOrig.sourceReceipt.passed,
    'R13 §1 rejects standalone subposition report attached as originalRootReport (LP-P02)',
    `orig=${String(frag162SubAsOrig.originalRootOutcome)}, note=${frag162SubAsOrig.originalRootBindingNote}`
  );

  // 11.2 R13 §2 Case A: p042 RZ-referenced source descendant stateId corruption must fail identically from BOTH direct and RZ entry points
  const p042 = getSpec('chao_vol1_p042');
  const ctx42 = DfpnSolver.buildProofContext(p042, cfgRz);
  const rep42 = new DfpnSolver(cfgRz).solveProblem(p042);
  const rsMove = sgfToCoord('rs', 19);
  const rsSnap42 = rep42.branchCoverageSnapshots?.find((s) => s.path === 'rs');
  const passEntry42 = rsSnap42?.moves.find((m) => m.move === PASS_MOVE);
  const rzEntry42 = rsSnap42?.moves.find(
    (m) =>
      m.status === 'RZ_REVALIDATED' &&
      m.sourceProofNodeId === passEntry42?.dagNodeId
  );

  check(
    Boolean(passEntry42 && rzEntry42),
    'R13 §2A setup: located p042 rs/pass source node and an RZ_REVALIDATED sibling referencing it',
    `pass=#${passEntry42?.dagNodeId}, rz=${rzEntry42?.moveSgf}/#${rzEntry42?.dagNodeId}`
  );

  if (passEntry42 && rzEntry42) {
    // Positive control: intact p042 passes from both direct source and RZ sibling entry
    const okDirect42 = checker.verifySubproofFragment({
      problem: p042,
      context: ctx42,
      report: rep42,
      targetPathMoves: [rsMove, PASS_MOVE],
      targetDagNodeId: passEntry42.dagNodeId,
    });
    const okViaRz42 = checker.verifySubproofFragment({
      problem: p042,
      context: ctx42,
      report: rep42,
      targetPathMoves: [rsMove, rzEntry42.move],
      targetDagNodeId: rzEntry42.dagNodeId,
    });
    check(
      okDirect42.sourceReceipt.status === 'SOURCE_VERIFIED' &&
        okDirect42.sourceReceipt.verificationMode === 'full_state_table' &&
        okViaRz42.sourceReceipt.status === 'SOURCE_VERIFIED' &&
        okViaRz42.sourceReceipt.verificationMode === 'full_state_table',
      'R13 §2A positive control: intact p042 verifies both direct rs/pass source and RZ sibling in full_state_table mode',
      `direct=${okDirect42.sourceReceipt.status}, viaRz=${okViaRz42.sourceReceipt.status}`
    );

    // Mutate ordinary child of rs/pass source node to out-of-bounds stateId
    const srcDagNode = rep42.proofDagNodes[passEntry42.dagNodeId];
    const childToCorrupt = srcDagNode.childNodeIds[0];
    const rep42MutDesc = cloneReport(rep42);
    rep42MutDesc.proofDagNodes[childToCorrupt].stateId =
      rep42MutDesc.stateTable.length;

    const failDirect42 = checker.verifySubproofFragment({
      problem: p042,
      context: ctx42,
      report: rep42MutDesc,
      targetPathMoves: [rsMove, PASS_MOVE],
      targetDagNodeId: passEntry42.dagNodeId,
    });
    const failViaRz42 = checker.verifySubproofFragment({
      problem: p042,
      context: ctx42,
      report: rep42MutDesc,
      targetPathMoves: [rsMove, rzEntry42.move],
      targetDagNodeId: rzEntry42.dagNodeId,
    });
    check(
      failDirect42.sourceReceipt.status === 'VERIFICATION_FAILED' &&
        failDirect42.sourceReceipt.errorCode === 'LP-S10' &&
        failViaRz42.sourceReceipt.status === 'VERIFICATION_FAILED' &&
        failViaRz42.sourceReceipt.errorCode === 'LP-S10' &&
        failViaRz42.originalRootOutcome === null,
      `R13 §2A entry-point invariance: corrupting source child #${childToCorrupt}.stateId fails BOTH direct (#${passEntry42.dagNodeId}) and RZ ref (${rzEntry42.moveSgf}/#${rzEntry42.dagNodeId}) with LP-S10`,
      `direct=${failDirect42.sourceReceipt.status}/${failDirect42.sourceReceipt.errorCode}, viaRz=${failViaRz42.sourceReceipt.status}/${failViaRz42.sourceReceipt.errorCode}, origRoot=${String(failViaRz42.originalRootOutcome)}`
    );
  }

  // 11.3 R13 §2 Case B: p001 ba leaf self-loop parentStateId must fail identically from BOTH root and direct ba entry
  const p001 = getSpec('p001');
  const ctx001 = DfpnSolver.buildProofContext(p001, cfgRz);
  const rep001 = new DfpnSolver(cfgRz).solveProblem(p001);
  const baMove = sgfToCoord('ba', 19);

  const rep001SelfLoop = cloneReport(rep001);
  const baStateId = rep001SelfLoop.proofDagNodes[0].stateId;
  rep001SelfLoop.proofDagNodes[0].parentStateId = baStateId;
  rep001SelfLoop.stateTable[baStateId].parentStateId = baStateId;

  const failLoopFromRoot = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001,
    report: rep001SelfLoop,
    targetPathMoves: [],
    targetDagNodeId: rep001SelfLoop.rootDagNodeId,
  });
  const failLoopDirectBa = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001,
    report: rep001SelfLoop,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  check(
    failLoopFromRoot.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      failLoopFromRoot.sourceReceipt.errorCode === 'LP-S10' &&
      failLoopDirectBa.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      failLoopDirectBa.sourceReceipt.errorCode === 'LP-S10' &&
      failLoopDirectBa.originalRootOutcome === null,
    'R13 §2B entry-point invariance: p001 ba leaf self-loop parentStateId fails BOTH root and direct ba entry with LP-S10',
    `root=${failLoopFromRoot.sourceReceipt.status}/${failLoopFromRoot.sourceReceipt.errorCode}, directBa=${failLoopDirectBa.sourceReceipt.status}/${failLoopDirectBa.sourceReceipt.errorCode}`
  );

  // 11.4 R13 §3: Cross-binding between in-memory SolveReport and embedded lproofJson + mandatory context/runContract checks
  const p001EmptyRegion: TsumegoProblemSpec = {
    ...p001,
    hasRegionHint: true,
    regionCoords: [],
  };
  const rep001Empty = new DfpnSolver(cfgRz).solveProblem(p001EmptyRegion);

  // Case A: swap official p001 report.lproofJson with real empty-region p001 PROVEN_LOSS lproofJson
  const rep001SwappedLproof = cloneReport(rep001);
  rep001SwappedLproof.lproofJson = rep001Empty.lproofJson;
  const failSwappedLproof = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001,
    report: rep001SwappedLproof,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  check(
    failSwappedLproof.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      failSwappedLproof.sourceReceipt.errorCode === 'LP-P01',
    'R13 §3A rejects official p001 in-memory report paired with swapped empty-region lproofJson (LP-P01)',
    `status=${failSwappedLproof.sourceReceipt.status}, code=${failSwappedLproof.sourceReceipt.errorCode}`
  );

  // Case B: delete context from report.lproofJson (must reject with LP-J02, NEVER silently skip!)
  const rep001NoLpCtx = cloneReport(rep001);
  const lpObjNoCtx = JSON.parse(rep001NoLpCtx.lproofJson);
  delete lpObjNoCtx.context;
  rep001NoLpCtx.lproofJson = JSON.stringify(lpObjNoCtx);

  const ctx001OppositeKo: ProofContext = {
    ...ctx001,
    attackerAllowKo: !ctx001.attackerAllowKo,
  };
  const failNoCtxOppositeKo = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001OppositeKo,
    report: rep001NoLpCtx,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  const failNoCtxSameKo = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001,
    report: rep001NoLpCtx,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  check(
    failNoCtxOppositeKo.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      (failNoCtxOppositeKo.sourceReceipt.errorCode === 'LP-P01' ||
        failNoCtxOppositeKo.sourceReceipt.errorCode === 'LP-J02') &&
      failNoCtxSameKo.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      failNoCtxSameKo.sourceReceipt.errorCode === 'LP-J02',
    'R13 §3B rejects stripped lproofJson.context (LP-J02 / LP-P01) instead of silently skipping context binding',
    `oppKo=${failNoCtxOppositeKo.sourceReceipt.status}/${failNoCtxOppositeKo.sourceReceipt.errorCode}, sameKo=${failNoCtxSameKo.sourceReceipt.status}/${failNoCtxSameKo.sourceReceipt.errorCode}`
  );

  // Case C: omitted lproofJson with opposite attackerAllowKo still rejected via runContract AND configFingerprint fallback
  const rep001EmptyLpStr = cloneReport(rep001);
  rep001EmptyLpStr.lproofJson = '';
  const failEmptyLpOppositeKo = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001OppositeKo,
    report: rep001EmptyLpStr,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  const rep001NoLpNoRc = cloneReport(rep001EmptyLpStr);
  delete rep001NoLpNoRc.runContract;
  const failFpFallbackOppositeKo = checker.verifySubproofFragment({
    problem: p001,
    context: ctx001OppositeKo,
    report: rep001NoLpNoRc,
    targetPathMoves: [baMove],
    targetDagNodeId: 0,
  });
  check(
    failEmptyLpOppositeKo.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      failEmptyLpOppositeKo.sourceReceipt.errorCode === 'LP-P01' &&
      failFpFallbackOppositeKo.sourceReceipt.status === 'VERIFICATION_FAILED' &&
      failFpFallbackOppositeKo.sourceReceipt.errorCode === 'LP-P01',
    'R13 §3C rejects mismatched attackerAllowKo even when lproofJson is omitted (via runContract and configFingerprint fallback, LP-P01)',
    `rc=${failEmptyLpOppositeKo.sourceReceipt.errorCode}, fp=${failFpFallbackOppositeKo.sourceReceipt.errorCode}`
  );

  // 11.5 Baseline & canonical digest invariance guard (p031 & p042 byte-exact R12 canonical checksums)
  const p031 = getSpec('chao_vol1_p031');
  const ctx031 = DfpnSolver.buildProofContext(p031, cfgRz);
  const rep031 = new DfpnSolver(cfgRz).solveProblem(p031);
  const vr031 = checker.verifySerializedLProofJson(rep031.lproofJson, {
    problem: p031,
    context: ctx031,
    scope: 'original_root',
  });
  const vr042 = checker.verifySerializedLProofJson(rep42.lproofJson, {
    problem: p042,
    context: ctx42,
    scope: 'original_root',
  });
  check(
    rep031.rootStatus === ProofOutcome.ProvenWin &&
      rep031.bestMoveSgf === 'sr' &&
      rep031.numNodes === 1892 &&
      vr031.passed &&
      vr031.canonicalDagChecksum ===
        'sha256-jcs:134cdbdb6f5909f57979f89ecdd8760466c327b4b2ccbd4e48d9d8f9da3a74a7' &&
      rep42.rootStatus === ProofOutcome.ProvenWin &&
      rep42.bestMoveSgf === 'rs' &&
      rep42.numNodes === 331 &&
      vr042.passed &&
      vr042.canonicalDagChecksum ===
        'sha256-jcs:879d82fa63abb4f6fc76cb8e16adc14e4f6f671d89af630f18b62bd91fa29c16',
    'R13 baseline guard: p031 (1892 nodes) and p042 (331 nodes) preserve exact R12 canonical DAG digests',
    `p031=${rep031.numNodes}/${vr031.canonicalDagChecksum}, p042=${rep42.numNodes}/${vr042.canonicalDagChecksum}`
  );
});

console.log(
  `\n========================================\nR5 TS Regression Summary: ${passedAssertions}/${totalAssertions} passed, ${failures.length} failed.\n========================================`
);
if (failures.length > 0) {
  process.exit(1);
}


