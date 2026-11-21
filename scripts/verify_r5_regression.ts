// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Versioned R4 + R5 Regression & Cross-Verification Test Suite (TypeScript)
// Run via: npx tsx scripts/verify_r5_regression.ts

import { DfpnSolver } from '../src/engine/dfpnSolver';
import { coordFromRowCol, GoPosition } from '../src/engine/position';
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
  KoRule,
  ProofOutcome,
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
    rep42.numNodes <= 1300,
    'p042 search nodes stay optimized (<= 1300)',
    `nodes=${rep42.numNodes}`
  );
  const ver42 = checker.verifySerializedLProofJson(rep42.lproofJson, {
    problem: p042,
    scope: 'original_root',
  });
  check(
    ver42.passed,
    'p042 standalone file verification PASS',
    `code=${ver42.errorCode}`
  );
  console.log(
    `  [INFO] p042: outcome=${rep42.rootStatus}, nodes=${rep42.numNodes}, dag=${rep42.proofDagNodes.length}, timeMs=${rep42.timeMs.toFixed(1)}`
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

console.log(
  `\n========================================\nR5 TS Regression Summary: ${passedAssertions}/${totalAssertions} passed, ${failures.length} failed.\n========================================`
);
if (failures.length > 0) {
  process.exit(1);
}
