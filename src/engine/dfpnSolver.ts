// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// TypeScript 1:1 execution mirror of src/search/dfpn_solver.cc (FR-4.1..FR-4.10)

import { BensonTerminalEvaluator } from './bensonUca';
import {
  coordToHumanLabel,
  coordToSgf,
  GoPosition,
  PASS_MOVE,
} from './position';
import { ProofArtifactManager } from './proofChecker';
import { ProofCertificateRZ, RelevanceZoneEngine } from './relevanceZone';
import { TranspositionStore } from './transpositionTable';
import {
  CanonicalSnapshot,
  Color,
  LogicalOp,
  oppositeColor,
  PN_DN_SATURATION,
  ProofContext,
  ProofDagNode,
  ProofOutcome,
  PrunedCertificateRecord,
  SolveReport,
  SolverConfig,
  StateTableEntry,
  TerminalStatus,
  TsumegoProblemSpec,
  UnknownReason,
} from './types';

function clampSat(val: number): number {
  return val >= PN_DN_SATURATION ? PN_DN_SATURATION : Math.max(0, Math.floor(val));
}

interface SearchChildSlot {
  move: number;
  tacticalScore: number;
  pn: number;
  dn: number;
  outcome: ProofOutcome;
  expanded: boolean;
  prunedOutsideRz: boolean;
  koDependent: boolean;
  stateId: number;
  hasCapture: boolean;
  dagNodeId: number;
  proofRz: ProofCertificateRZ;
  disproofRz: ProofCertificateRZ;
  prunedCert?: PrunedCertificateRecord;
}

interface CachedNodeFrontier {
  children: SearchChildSlot[];
  wideningLevel: number;
  activeNullMoveRz: ProofCertificateRZ | null;
  representativeDagId: number;
  representativeMove: number;
  representativeOutcome: ProofOutcome;
  anyKoDependent: boolean;
}

export class DfpnSolver {
  private readonly config: SolverConfig;
  private readonly terminalEval = new BensonTerminalEvaluator();
  private readonly rzEngine = new RelevanceZoneEngine();
  private readonly ttStore = new TranspositionStore();
  private readonly nodeFrontierCache = new Map<string, CachedNodeFrontier>();

  private numNodes = 0;
  private prunedOutsideRzCount = 0;
  private wideningUpgrades = 0;
  private cycleDetections = 0;
  private koDependentRejections = 0;
  private resourceExhausted = false;
  private unknownReason: UnknownReason = UnknownReason.None;

  private proofDagNodes: ProofDagNode[] = [];
  private dagHasCapture: boolean[] = [];
  private stateTable: StateTableEntry[] = [];
  private historyTable: CanonicalSnapshot[][] = [];
  private rootBestMove: number = PASS_MOVE;

  constructor(config: SolverConfig) {
    this.config = { ...config };
  }


  public solveProblem(problem: TsumegoProblemSpec): SolveReport {
    const startTime = performance.now();
    this.ttStore.clearAll();
    this.nodeFrontierCache.clear();
    this.numNodes = 0;
    this.prunedOutsideRzCount = 0;
    this.wideningUpgrades = 0;
    this.cycleDetections = 0;
    this.koDependentRejections = 0;
    this.resourceExhausted = false;
    this.unknownReason = UnknownReason.None;
    this.proofDagNodes = [];
    this.dagHasCapture = [];
    this.stateTable = [];
    this.historyTable = [];
    this.rootBestMove = PASS_MOVE;

    const context = DfpnSolver.buildProofContext(problem, this.config);
    const initialPos = DfpnSolver.buildInitialPosition(problem, context);

    const rootStateId = this.registerState(initialPos, -1, PASS_MOVE);
    const inPathHashes = new Set<string>();

    const rootResult = this.midSearch(
      initialPos,
      context,
      problem.regionCoords,
      PN_DN_SATURATION,
      PN_DN_SATURATION,
      0,
      rootStateId,
      PASS_MOVE,
      inPathHashes
    );

    if (
      rootResult.koDependent &&
      rootResult.outcome === ProofOutcome.Unknown &&
      this.unknownReason === UnknownReason.None
    ) {
      this.unknownReason = UnknownReason.KoDependent;
    }

    const rootEval = this.terminalEval.evaluateTerminal(initialPos, context);
    const pv = this.extractPrincipalVariation(
      initialPos.clone(),
      context,
      rootResult.dagNodeId,
      problem.boardSize
    );

    const elapsedMs = Math.max(1, Math.round(performance.now() - startTime));
    const artifactManager = new ProofArtifactManager();

    const partialReport: SolveReport = {
      problemId: problem.id,
      problemTitle: problem.title,
      inputHash: initialPos.computeZobristHex(),
      configFingerprint: `${this.config.ttMode}:${this.config.koRule}:rz=${this.config.enableRzPruning}:ko=${this.config.attackerAllowKo}`,
      solverVersion: 'LDProver-1.8.0-cxx20',
      rootStatus: rootResult.outcome,
      unknownReason:
        rootResult.outcome === ProofOutcome.Unknown
          ? this.unknownReason === UnknownReason.None
            ? UnknownReason.NodeLimit
            : this.unknownReason
          : null,
      rootPn: rootResult.pn,
      rootDn: rootResult.dn,
      bestMove: this.rootBestMove,
      bestMoveSgf:
        this.rootBestMove >= 0
          ? coordToSgf(this.rootBestMove, problem.boardSize)
          : this.rootBestMove === PASS_MOVE
          ? 'pass'
          : null,
      numNodes: this.numNodes,
      timeMs: elapsedMs,
      boardTtHits: this.ttStore.boardHits,
      patternTtHits: this.ttStore.patternHits,
      patternProofReusableHits: this.ttStore.patternProofReusableHits,
      ghiRejectedCount: this.ttStore.ghiRejectedCount,
      prunedOutsideRzCount: this.prunedOutsideRzCount,
      wideningUpgrades: this.wideningUpgrades,
      cycleDetections: this.cycleDetections,
      koDependentRejections: this.koDependentRejections,
      rzSizeAtRoot:
        rootResult.outcome === ProofOutcome.ProvenWin
          ? rootResult.proofRz.size
          : rootResult.disproofRz.size,
      resourceExhausted: this.resourceExhausted,
      artifactsComplete: true,
      rootProofRzCoords: rootResult.proofRz.toArray(),
      rootDisproofRzCoords: rootResult.disproofRz.toArray(),
      bensonAliveCoords: rootEval.bensonAliveCoords,
      eyeTopologyRegions: rootEval.eyeTopologyRegions,
      principalVariation: pv,
      proofDagNodes: this.proofDagNodes,
      stateTable: this.stateTable,
      historyTable: this.historyTable,
      rootDagNodeId: rootResult.dagNodeId,
      proofChecksum: '',
      sgfContent: '',
      sgfChecksum: '',
      lproofJson: '',
      resultJson: '',
    };

    const { json: lproofJson, checksum: proofChecksum } =
      artifactManager.serializeLProofJson(initialPos, context, partialReport);
    const { sgf: sgfContent, checksum: sgfChecksum } =
      artifactManager.exportSolutionTreeSgf(initialPos, context, partialReport);

    partialReport.lproofJson = lproofJson;
    partialReport.proofChecksum = proofChecksum;
    partialReport.sgfContent = sgfContent;
    partialReport.sgfChecksum = sgfChecksum;
    partialReport.resultJson = artifactManager.serializeResultJson(partialReport);

    return partialReport;
  }

  public static buildProofContext(
    problem: TsumegoProblemSpec,
    config: SolverConfig
  ): ProofContext {
    const rootAttacker =
      problem.winningColor === 'W' ? Color.White : Color.Black;
    const attackerGoal =
      problem.winningColor === 'W'
        ? problem.whiteSearchGoal
        : problem.blackSearchGoal;
    const crucialExpr =
      problem.winningColor === 'W'
        ? problem.whiteCrucialStone
        : problem.blackCrucialStone;

    let crucialOp = LogicalOp.Single;
    if (crucialExpr.includes('&')) crucialOp = LogicalOp.Conjunction;
    else if (crucialExpr.includes('|') || crucialExpr.includes(','))
      crucialOp = LogicalOp.Disjunction;

    const groups = crucialExpr
      .split(/[&|,]/)
      .map((s) => s.trim())
      .filter(Boolean);

    const initialTokens = groups.map((sgf, idx) => {
      const c = sgf.charCodeAt(0) - 97;
      const r = sgf.charCodeAt(1) - 97;
      const coord = r * problem.boardSize + c;
      const stoneColor = problem.blackInitialCoords.includes(coord)
        ? Color.Black
        : Color.White;
      return {
        tokenId: idx,
        initialCoord: coord,
        groupIndex: idx,
        stoneColor,
      };
    });

    return {
      contextId: `ctx_${problem.id}_${config.koRule}_${attackerGoal}_ko${config.attackerAllowKo ? 1 : 0}`,
      rootAttacker,
      attackerGoal,
      crucialStoneOp: crucialOp,
      koRule: config.koRule,
      attackerAllowKo: config.attackerAllowKo,
      defenderAllowKo: config.defenderAllowKo,
      initialTokens,
    };
  }

  public static buildInitialPosition(
    problem: TsumegoProblemSpec,
    context: ProofContext
  ): GoPosition {
    const pos = new GoPosition(
      context,
      problem.boardSize,
      problem.immortalWallCoords
    );
    const firstToPlay = problem.turnColor === 'W' ? Color.White : Color.Black;
    pos.setupInitialStones(
      problem.blackInitialCoords,
      problem.whiteInitialCoords,
      firstToPlay
    );
    return pos;
  }

  private registerState(
    pos: GoPosition,
    parentStateId: number,
    moveFromParent: number
  ): number {
    const historyId = this.historyTable.length;
    this.historyTable.push(pos.historySnapshots.slice());

    const stateId = this.stateTable.length;
    this.stateTable.push({
      stateId,
      parentStateId,
      moveFromParent,
      toPlay: pos.toPlay,
      koPoint: pos.koPoint,
      consecutivePasses: pos.consecutivePasses,
      survivingTokensMask: pos.survivingTargetTokensMask,
      zobristHex: pos.computeZobristHex(),
      blackCoords: pos.getBlackCoords(),
      whiteCoords: pos.getWhiteCoords(),
      historyId,
    });
    return stateId;
  }

  // FR-4.10: Deterministic FastCapture tactical move ordering
  private scoreMoveFastCapture(
    pos: GoPosition,
    context: ProofContext,
    move: number
  ): number {
    if (move === PASS_MOVE) return -2000;
    let score = 0;

    // 1. Proximity to crucial target chains and their liberties
    context.initialTokens.forEach((tok, idx) => {
      if ((pos.survivingTargetTokensMask & (1 << idx)) === 0) return;
      const { stones, liberties } = pos.floodFillChain(tok.initialCoord);
      if (liberties.has(move)) {
        score += 550;
        if (liberties.size <= 2) score += 750;
      }
      // Check eye-making / eye-stealing points adjacent to crucial chain
      const adjCount = pos
        .orthogonalNeighbors(move)
        .filter((n) => stones.has(n)).length;
      if (adjCount >= 2) score += 620;
    });

    const enemyColor = oppositeColor(pos.toPlay);

    // Pre-move liberty count of adjacent non-immortal enemy chains (for Semeai liberty-race detection)
    let tightenedLowLibEnemy = false;
    let tightenedCuttingEnemy = false;
    const seenEnemyBefore = new Set<number>();
    for (const nb of pos.orthogonalNeighbors(move)) {
      if (
        pos.stoneAt(nb) === enemyColor &&
        !pos.immortalWallSet.has(nb) &&
        !seenEnemyBefore.has(nb)
      ) {
        const echBefore = pos.floodFillChain(nb);
        for (const s of echBefore.stones) seenEnemyBefore.add(s);
        if (echBefore.liberties.size <= 3) {
          tightenedLowLibEnemy = true;
          // Check if this enemy chain separates >= 2 distinct friendly chains
          const adjFriendlyRoots = new Set<number>();
          for (const es of echBefore.stones) {
            for (const enb of pos.orthogonalNeighbors(es)) {
              if (pos.stoneAt(enb) === pos.toPlay) {
                const fch = pos.floodFillChain(enb);
                adjFriendlyRoots.add(Math.min(...Array.from(fch.stones)));
              }
            }
          }
          if (adjFriendlyRoots.size >= 2) {
            tightenedCuttingEnemy = true;
          }
        }
      }
    }

    // 2. Simulate move to detect captures, Throw-In / Snapback / Squatting-Ox, and atari
    const probe = pos.clone();
    const res = probe.playMove(move);
    if (!res.legal) return -9999;

    if (res.capturedCoords.length > 0) {
      score += 1200 + res.capturedCoords.length * 300;
    }

    const ourChain = probe.floodFillChain(move);
    if (ourChain.liberties.size === 1) {
      // Throw-in (扑 / 倒扑 / 脹牯牛) detector: simulate opponent capturing our 1-liberty stone(s).
      // If opponent's capturing chain ends up with <= 2 liberties (Snapback, Oiotoshi, or Squatting Ox),
      // boost aggressively into the first Progressive Widening window!
      let isTesujiThrowIn = false;
      if (res.capturedCoords.length === 0) {
        const soleLib = Array.from(ourChain.liberties)[0];
        const capProbe = probe.clone();
        const capRes = capProbe.playMove(soleLib);
        if (capRes.legal) {
          const enemyAfterCap = capProbe.floodFillChain(soleLib);
          if (enemyAfterCap.liberties.size <= 2) {
            isTesujiThrowIn = true;
          }
        }
      }
      if (isTesujiThrowIn) {
        score += 860;
      } else {
        const adjToCrucial = pos
          .orthogonalNeighbors(move)
          .some((n) => probe.stoneAt(n) !== Color.Empty);
        score += adjToCrucial ? 180 : -450;
      }
    } else if (ourChain.liberties.size >= 3) {
      score += 240;
    }

    if (tightenedLowLibEnemy && ourChain.liberties.size >= 2) {
      score += tightenedCuttingEnemy ? 680 : 380;
    }

    // Check if move puts an enemy non-immortal chain into atari or 2-liberty squeeze
    for (const nb of pos.orthogonalNeighbors(move)) {
      if (probe.stoneAt(nb) === enemyColor && !probe.immortalWallSet.has(nb)) {
        const enemyCh = probe.floodFillChain(nb);
        if (enemyCh.liberties.size === 1) {
          score += 680;
        } else if (enemyCh.liberties.size === 2) {
          score += 260;
        }
      }
    }

    // 3. Go Tsumego Shape Heuristics (2-2 vital point, chain connection, border post vs eye-filling)
    const r = Math.floor(move / pos.boardSize);
    const c = move % pos.boardSize;
    const distR = Math.min(r, pos.boardSize - 1 - r);
    const distC = Math.min(c, pos.boardSize - 1 - c);
    const distEdge = Math.min(distR, distC);

    if (distR === 1 && distC === 1) {
      score += 480;
    } else if (distEdge === 1) {
      score += 260;
    } else if (distEdge === 0) {
      score += 140;
    }

    const friendlyChainRoots = new Set<number>();
    let friendlyOrthoCount = 0;
    let enemyOrthoCount = 0;
    for (const nb of pos.orthogonalNeighbors(move)) {
      const st = pos.stoneAt(nb);
      if (st === pos.toPlay) {
        friendlyOrthoCount++;
        const ch = pos.floodFillChain(nb);
        if (ch.liberties.size >= 2) {
          friendlyChainRoots.add(Math.min(...Array.from(ch.stones)));
        }
      } else if (st === enemyColor) {
        enemyOrthoCount++;
      }
    }
    if (friendlyChainRoots.size >= 2) {
      score += 850;
    }

    let friendlyDiagCount = 0;
    let enemyDiagCount = 0;
    for (const d of pos.diagonalNeighbors(move)) {
      const st = pos.stoneAt(d);
      if (st === pos.toPlay) friendlyDiagCount++;
      else if (st === enemyColor) enemyDiagCount++;
    }
    if (friendlyDiagCount >= 2 && enemyOrthoCount === 0) {
      score += 520;
      for (const enb of pos.orthogonalNeighbors(move)) {
        if (pos.stoneAt(enb) === Color.Empty) {
          const enbFriendlyWalls = pos
            .orthogonalNeighbors(enb)
            .filter((n) => n === move || pos.stoneAt(n) === pos.toPlay).length;
          if (enbFriendlyWalls >= 3) {
            score += 750;
          }
        }
      }
    }
    if (friendlyOrthoCount >= 1 && enemyDiagCount >= 1) {
      score += 340;
    }

    if (distEdge === 0 && enemyOrthoCount === 0 && enemyDiagCount === 0 && friendlyOrthoCount === 1) {
      const friendlyNb = pos.orthogonalNeighbors(move).find((n) => pos.stoneAt(n) === pos.toPlay)!;
      const friendlyNbSameLineCount = pos
        .orthogonalNeighbors(friendlyNb)
        .filter((nn) => pos.stoneAt(nn) === pos.toPlay).length;
      if (friendlyNbSameLineCount >= 2) {
        score -= 480;
      }
    }

    return score;
  }

  // FR-5.5: Revalidate source proof witness path under QueryState + HistorySet
  private revalidateSourceProofOnQueryState(
    queryPos: GoPosition,
    context: ProofContext,
    sourceDagNodeId: number,
    expectedOutcome: ProofOutcome
  ): boolean {
    if (
      sourceDagNodeId < 0 ||
      sourceDagNodeId >= this.proofDagNodes.length
    ) {
      return false;
    }
    const sourceNode = this.proofDagNodes[sourceDagNodeId];
    if (sourceNode.outcome !== expectedOutcome) return false;

    const term = this.terminalEval.evaluateTerminal(queryPos, context);
    if (term.status === TerminalStatus.Win) {
      return expectedOutcome === ProofOutcome.ProvenWin;
    }
    if (term.status === TerminalStatus.Loss) {
      return expectedOutcome === ProofOutcome.ProvenLoss;
    }

    if (sourceNode.childNodeIds.length === 0) return false;
    const isOr = queryPos.toPlay === context.rootAttacker;

    if (
      (isOr && expectedOutcome === ProofOutcome.ProvenWin) ||
      (!isOr && expectedOutcome === ProofOutcome.ProvenLoss)
    ) {
      for (let i = 0; i < sourceNode.childNodeIds.length; i++) {
        const nextPos = queryPos.clone();
        const playRes = nextPos.playMove(sourceNode.childMoves[i]);
        if (!playRes.legal) continue;
        if (
          this.revalidateSourceProofOnQueryState(
            nextPos,
            context,
            sourceNode.childNodeIds[i],
            expectedOutcome
          )
        ) {
          return true;
        }
      }
      return false;
    }

    return true;
  }

  private midSearch(
    pos: GoPosition,
    context: ProofContext,
    regionCoords: number[],
    thPn: number,
    thDn: number,
    depth: number,
    currentStateId: number,
    incomingMove: number,
    inPathHashes: Set<string>
  ): {
    pn: number;
    dn: number;
    outcome: ProofOutcome;
    koDependent: boolean;
    proofRz: ProofCertificateRZ;
    disproofRz: ProofCertificateRZ;
    dagNodeId: number;
  } {
    this.numNodes++;
    const isOrNode = pos.toPlay === context.rootAttacker;

    // Step 1 (FR-3.2, FR-3.8): Evaluate Terminal BEFORE InPath cycle check
    const term = this.terminalEval.evaluateTerminal(pos, context);
    if (
      term.status === TerminalStatus.Win ||
      term.status === TerminalStatus.Loss
    ) {
      const isWin = term.status === TerminalStatus.Win;
      const pn = isWin ? 0 : PN_DN_SATURATION;
      const dn = isWin ? PN_DN_SATURATION : 0;
      const outcome = isWin ? ProofOutcome.ProvenWin : ProofOutcome.ProvenLoss;
      const proofRz = isWin
        ? new ProofCertificateRZ(term.leafCertificateRz)
        : new ProofCertificateRZ();
      const disproofRz = !isWin
        ? new ProofCertificateRZ(term.leafCertificateRz)
        : new ProofCertificateRZ();

      const dagNodeId = this.proofDagNodes.length;
      const stEntry = this.stateTable[currentStateId];
      this.proofDagNodes.push({
        nodeId: dagNodeId,
        stateId: currentStateId,
        historyId: stEntry.historyId,
        parentStateId: stEntry.parentStateId,
        isOrNode,
        toPlay: pos.toPlay,
        incomingMove,
        incomingMoveSgf: coordToSgf(incomingMove, pos.boardSize),
        pn,
        dn,
        outcome,
        terminalEvidence: term.evidenceKind,
        isPrunedOutsideRz: false,
        isTtHit: false,
        isKoDependentBarrier: false,
        sourceProofNodeId: null,
        proofRzCoords: proofRz.toArray(),
        disproofRzCoords: disproofRz.toArray(),
        childNodeIds: [],
        childMoves: [],
      });
      this.dagHasCapture.push(false);

      return {
        pn,
        dn,
        outcome,
        koDependent: false,
        proofRz,
        disproofRz,
        dagNodeId,
      };
    }

    // Step 2 (FR-4.5): Conservative InPath cycle guard
    const zHex = pos.computeZobristHex();
    if (inPathHashes.has(zHex)) {
      this.cycleDetections++;
      if (this.unknownReason === UnknownReason.None) {
        this.unknownReason = UnknownReason.Cycle;
      }
      return {
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        koDependent: false,
        proofRz: new ProofCertificateRZ(),
        disproofRz: new ProofCertificateRZ(),
        dagNodeId: -1,
      };
    }

    // Step 3 (FR-4.7): Resource & depth guardrails
    if (depth >= this.config.maxDepth) {
      this.resourceExhausted = true;
      this.unknownReason = UnknownReason.DepthLimit;
      return {
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        koDependent: false,
        proofRz: new ProofCertificateRZ(),
        disproofRz: new ProofCertificateRZ(),
        dagNodeId: -1,
      };
    }
    if (this.numNodes >= this.config.maxNodes) {
      this.resourceExhausted = true;
      this.unknownReason = UnknownReason.NodeLimit;
      return {
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        koDependent: false,
        proofRz: new ProofCertificateRZ(),
        disproofRz: new ProofCertificateRZ(),
        dagNodeId: -1,
      };
    }

    // Step 4 (FR-6.1, FR-6.3, FR-6.9): History-safe BoardTT & PatternTT lookup
    const revalidateCb = (dagId: number, out: ProofOutcome) =>
      this.revalidateSourceProofOnQueryState(
        pos,
        context,
        dagId,
        out,
        regionCoords
      );

    const boardHit = this.ttStore.lookupBoardTT(pos, context, revalidateCb);
    if (
      boardHit &&
      boardHit.outcome !== ProofOutcome.Unknown &&
      boardHit.proofClosureAvailable
    ) {
      return {
        pn: boardHit.pn,
        dn: boardHit.dn,
        outcome: boardHit.outcome,
        koDependent: false,
        proofRz: boardHit.proofRz,
        disproofRz: boardHit.disproofRz,
        dagNodeId: boardHit.proofDagNodeId,
      };
    }

    if (this.config.ttMode === 'pattern-tt') {
      const patHit = this.ttStore.lookupPatternTT(pos, context);
      if (patHit.grade === 'PROOF_REUSABLE' && patHit.record) {
        return {
          pn: patHit.record.pn,
          dn: patHit.record.dn,
          outcome: patHit.record.outcome,
          koDependent: false,
          proofRz: patHit.record.storedRz,
          disproofRz: patHit.record.storedRz,
          dagNodeId: patHit.record.proofDagNodeId,
        };
      }
    }

    // Step 5: Lookup or initialize cached frontier node for persistent DFPN bounds
    const frontierKey = `${zHex}:${pos.toPlay}:${pos.koPoint}:${pos.consecutivePasses}:${pos.survivingTargetTokensMask}`;
    let frontier = this.nodeFrontierCache.get(frontierKey);
    if (!frontier) {
      const legalMoves = pos.generateLegalMoves(regionCoords);
      const children: SearchChildSlot[] = legalMoves.map((mv) => ({
        move: mv,
        tacticalScore: this.config.enableFastCaptureOrdering
          ? this.scoreMoveFastCapture(pos, context, mv)
          : 0,
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        expanded: false,
        prunedOutsideRz: false,
        koDependent: false,
        stateId: -1,
        hasCapture: false,
        dagNodeId: -1,
        proofRz: new ProofCertificateRZ(),
        disproofRz: new ProofCertificateRZ(),
      }));

      if (this.config.enableFastCaptureOrdering) {
        children.sort((a, b) => b.tacticalScore - a.tacticalScore);
      }

      frontier = {
        children,
        wideningLevel: 0,
        activeNullMoveRz: null,
        representativeDagId: -1,
        representativeMove: PASS_MOVE,
        representativeOutcome: ProofOutcome.Unknown,
        anyKoDependent: false,
      };
      this.nodeFrontierCache.set(frontierKey, frontier);
    }

    const children = frontier.children;
    inPathHashes.add(zHex);

    let finalPn = 1;
    let finalDn = 1;
    let finalOutcome = ProofOutcome.Unknown;
    let finalProofRz = new ProofCertificateRZ();
    let finalDisproofRz = new ProofCertificateRZ();
    let finalDagNodeId = -1;

    while (true) {
      const totalLegal = children.length;
      let windowSize = totalLegal;
      if (this.config.enableProgressiveWidening && frontier.wideningLevel < 4) {
        const cap = this.config.wideningBaseK * Math.pow(2, frontier.wideningLevel);
        if (cap < totalLegal) windowSize = cap;
      }

      // FR-5.5: OutsideRZRevalidated null-move certificate pruning
      if (
        this.config.enableRzPruning &&
        frontier.activeNullMoveRz &&
        frontier.representativeDagId >= 0
      ) {
        for (let i = 0; i < windowSize; i++) {
          const ch = children[i];
          if (ch.expanded || ch.outcome !== ProofOutcome.Unknown) continue;
          if (this.rzEngine.isOutsideRZCandidate(ch.move, frontier.activeNullMoveRz)) {
            const nextPos = pos.clone();
            const playRes = nextPos.playMove(ch.move);
            if (
              playRes.legal &&
              this.revalidateSourceProofOnQueryState(
                nextPos,
                context,
                frontier.representativeDagId,
                frontier.representativeOutcome,
                regionCoords
              )
            ) {
              const qStateId =
                ch.stateId >= 0
                  ? ch.stateId
                  : this.registerState(nextPos, currentStateId, ch.move);
              ch.stateId = qStateId;
              ch.hasCapture = playRes.capturedCoords.length > 0;
              const qStateEntry = this.stateTable[qStateId];
              const srcNode = this.proofDagNodes[frontier.representativeDagId];

              const prunedCert: PrunedCertificateRecord = {
                queryStateId: qStateId,
                queryHistoryId: qStateEntry.historyId,
                sourceStateId: srcNode.stateId,
                sourceHistoryId: srcNode.historyId,
                sourceProofNodeId: frontier.representativeDagId,
                contextId: context.contextId,
                prunedMove: ch.move,
                representativeMove: frontier.representativeMove,
                certificateRzCoords: frontier.activeNullMoveRz.toArray(),
                reason: 'OutsideRZRevalidated',
              };

              const prunedNodeId = this.proofDagNodes.length;
              this.proofDagNodes.push({
                nodeId: prunedNodeId,
                stateId: qStateId,
                historyId: qStateEntry.historyId,
                parentStateId: currentStateId,
                isOrNode: !isOrNode,
                toPlay: nextPos.toPlay,
                incomingMove: ch.move,
                incomingMoveSgf: coordToSgf(ch.move, pos.boardSize),
                pn:
                  frontier.representativeOutcome === ProofOutcome.ProvenWin
                    ? 0
                    : PN_DN_SATURATION,
                dn:
                  frontier.representativeOutcome === ProofOutcome.ProvenWin
                    ? PN_DN_SATURATION
                    : 0,
                outcome: frontier.representativeOutcome,
                terminalEvidence: 'OUTSIDE_RZ_REVALIDATED',
                isPrunedOutsideRz: true,
                isTtHit: false,
                isKoDependentBarrier: false,
                sourceProofNodeId: frontier.representativeDagId,
                proofRzCoords: frontier.activeNullMoveRz.toArray(),
                disproofRzCoords: frontier.activeNullMoveRz.toArray(),
                childNodeIds: [],
                childMoves: [],
                prunedCertificate: prunedCert,
              });
              this.dagHasCapture.push(
                ch.hasCapture ||
                  Boolean(this.dagHasCapture[frontier.representativeDagId])
              );

              ch.expanded = true;
              ch.prunedOutsideRz = true;
              ch.outcome = frontier.representativeOutcome;
              ch.pn =
                frontier.representativeOutcome === ProofOutcome.ProvenWin
                  ? 0
                  : PN_DN_SATURATION;
              ch.dn =
                frontier.representativeOutcome === ProofOutcome.ProvenWin
                  ? PN_DN_SATURATION
                  : 0;
              ch.proofRz = frontier.activeNullMoveRz;
              ch.disproofRz = frontier.activeNullMoveRz;
              ch.dagNodeId = prunedNodeId;
              ch.prunedCert = prunedCert;
              this.prunedOutsideRzCount++;
            }
          }
        }
      }

      // FR-4.1: Frontier PN/DN aggregation with implicit unexpanded cost U
      const unexpandedU = Math.max(0, totalLegal - windowSize);
      let curPn = 1;
      let curDn = 1;

      if (isOrNode) {
        let minPn = unexpandedU > 0 ? 1 : PN_DN_SATURATION;
        let sumDn = unexpandedU;
        for (let i = 0; i < windowSize; i++) {
          minPn = Math.min(minPn, children[i].pn);
          sumDn += children[i].dn;
        }
        curPn = minPn;
        curDn = clampSat(sumDn);
      } else {
        let sumPn = unexpandedU;
        let minDn = unexpandedU > 0 ? 1 : PN_DN_SATURATION;
        for (let i = 0; i < windowSize; i++) {
          sumPn += children[i].pn;
          minDn = Math.min(minDn, children[i].dn);
        }
        curPn = clampSat(sumPn);
        curDn = minDn;
      }

      // Check asymmetric decisive completion conditions (FR-4.2)
      if (curPn === 0 || curDn === 0) {
        if (
          ((isOrNode && curDn === 0) || (!isOrNode && curPn === 0)) &&
          windowSize < totalLegal
        ) {
          frontier.wideningLevel++;
          this.wideningUpgrades++;
          continue;
        }

        finalPn = curPn;
        finalDn = curDn;
        finalOutcome =
          curPn === 0 ? ProofOutcome.ProvenWin : ProofOutcome.ProvenLoss;

        let subtreeHasCapture = false;

        // Backpropagate dual-chain Relevance Zone (FR-5.2, FR-5.3)
        if (isOrNode && curPn === 0) {
          const winChild = children.find((c) => c.pn === 0)!;
          finalProofRz = this.rzEngine.computeSingleWitnessRZ(
            pos,
            winChild.move,
            winChild.proofRz
          );
          subtreeHasCapture =
            winChild.hasCapture ||
            (winChild.dagNodeId >= 0 &&
              Boolean(this.dagHasCapture[winChild.dagNodeId]));
          if (depth === 0) this.rootBestMove = winChild.move;
        } else if (!isOrNode && curDn === 0) {
          const lossChild = children.find((c) => c.dn === 0)!;
          finalDisproofRz = this.rzEngine.computeSingleWitnessRZ(
            pos,
            lossChild.move,
            lossChild.disproofRz
          );
          subtreeHasCapture =
            lossChild.hasCapture ||
            (lossChild.dagNodeId >= 0 &&
              Boolean(this.dagHasCapture[lossChild.dagNodeId]));
          if (depth === 0) this.rootBestMove = lossChild.move;
        } else if (isOrNode && curDn === 0) {
          finalDisproofRz = this.rzEngine.computeAllChildrenUnionRZ(
            pos,
            children.map((c) => c.disproofRz)
          );
          subtreeHasCapture = children.some(
            (c) =>
              c.hasCapture ||
              (c.dagNodeId >= 0 && Boolean(this.dagHasCapture[c.dagNodeId]))
          );
        } else {
          finalProofRz = this.rzEngine.computeAllChildrenUnionRZ(
            pos,
            children.map((c) => c.proofRz)
          );
          subtreeHasCapture = children.some(
            (c) =>
              c.hasCapture ||
              (c.dagNodeId >= 0 && Boolean(this.dagHasCapture[c.dagNodeId]))
          );
        }

        finalDagNodeId = this.proofDagNodes.length;
        const stEntry = this.stateTable[currentStateId];
        const recordedChildren = children.filter(
          (c) => c.expanded && c.dagNodeId >= 0
        );

        this.proofDagNodes.push({
          nodeId: finalDagNodeId,
          stateId: currentStateId,
          historyId: stEntry.historyId,
          parentStateId: stEntry.parentStateId,
          isOrNode,
          toPlay: pos.toPlay,
          incomingMove,
          incomingMoveSgf: coordToSgf(incomingMove, pos.boardSize),
          pn: finalPn,
          dn: finalDn,
          outcome: finalOutcome,
          terminalEvidence: 'INTERNAL_AGGREGATION',
          isPrunedOutsideRz: false,
          isTtHit: false,
          isKoDependentBarrier: false,
          sourceProofNodeId: null,
          proofRzCoords: finalProofRz.toArray(),
          disproofRzCoords: finalDisproofRz.toArray(),
          childNodeIds: recordedChildren.map((c) => c.dagNodeId),
          childMoves: recordedChildren.map((c) => c.move),
        });
        this.dagHasCapture.push(subtreeHasCapture);

        this.ttStore.storeBoardTT(
          pos,
          context,
          finalPn,
          finalDn,
          finalOutcome,
          frontier.anyKoDependent,
          true,
          finalDagNodeId,
          finalProofRz,
          finalDisproofRz,
          subtreeHasCapture
        );

        if (this.config.ttMode === 'pattern-tt') {
          const activeZone =
            finalOutcome === ProofOutcome.ProvenWin
              ? finalProofRz
              : finalDisproofRz;
          this.ttStore.storePatternTT(
            pos,
            context,
            activeZone,
            finalPn,
            finalDn,
            finalOutcome,
            finalDagNodeId,
            true,
            subtreeHasCapture
          );
        }
        break;
      }

      // Threshold cutoff check (FR-4.3: OR condition)
      if (
        curPn >= thPn ||
        curDn >= thDn ||
        this.numNodes >= this.config.maxNodes
      ) {
        finalPn = curPn;
        finalDn = curDn;
        finalOutcome = ProofOutcome.Unknown;
        break;
      }

      // Select most-proving child within current window (skipping koDependent barriers)
      let bestIdx = -1;
      let bestMetric = PN_DN_SATURATION;
      let secondBestMetric = PN_DN_SATURATION;

      for (let i = 0; i < windowSize; i++) {
        if (children[i].koDependent) continue;
        const m = isOrNode ? children[i].pn : children[i].dn;
        if (m < bestMetric) {
          secondBestMetric = bestMetric;
          bestMetric = m;
          bestIdx = i;
        } else if (m < secondBestMetric) {
          secondBestMetric = m;
        }
      }

      if (unexpandedU > 0 && bestMetric > 1) {
        frontier.wideningLevel++;
        this.wideningUpgrades++;
        continue;
      }

      if (bestIdx < 0 || bestMetric >= PN_DN_SATURATION) {
        finalPn = curPn;
        finalDn = curDn;
        finalOutcome = ProofOutcome.Unknown;
        if (frontier.anyKoDependent && depth === 0) {
          const koChild = children.find((c) => c.koDependent);
          if (koChild) this.rootBestMove = koChild.move;
        }
        break;
      }

      const mpc = children[bestIdx];
      let childThPn = thPn;
      let childThDn = thDn;
      if (isOrNode) {
        childThPn = Math.min(thPn, clampSat(secondBestMetric + 1));
        const otherDn = curDn - mpc.dn;
        childThDn = thDn > otherDn ? Math.max(1, thDn - otherDn) : 1;
      } else {
        const otherPn = curPn - mpc.pn;
        childThPn = thPn > otherPn ? Math.max(1, thPn - otherPn) : 1;
        childThDn = Math.min(thDn, clampSat(secondBestMetric + 1));
      }

      const nextPos = pos.clone();
      const playRes = nextPos.playMove(mpc.move);
      if (!playRes.legal) {
        mpc.pn = isOrNode ? PN_DN_SATURATION : 0;
        mpc.dn = isOrNode ? 0 : PN_DN_SATURATION;
        continue;
      }

      if (mpc.stateId < 0) {
        mpc.stateId = this.registerState(nextPos, currentStateId, mpc.move);
      }
      mpc.hasCapture = playRes.capturedCoords.length > 0;

      const subRes = this.midSearch(
        nextPos,
        context,
        regionCoords,
        childThPn,
        childThDn,
        depth + 1,
        mpc.stateId,
        mpc.move,
        inPathHashes
      );

      mpc.pn = subRes.pn;
      mpc.dn = subRes.dn;
      mpc.outcome = subRes.outcome;
      mpc.proofRz = subRes.proofRz;
      mpc.disproofRz = subRes.disproofRz;
      mpc.dagNodeId = subRes.dagNodeId;
      mpc.expanded = true;

      // FR-5.7: KoDependent witness barrier check
      const restrictedSide =
        (pos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
        (pos.toPlay !== context.rootAttacker && !context.defenderAllowKo);

      if (
        (playRes.isKoCapture || subRes.koDependent) &&
        restrictedSide &&
        ((isOrNode && mpc.pn === 0) || (!isOrNode && mpc.dn === 0))
      ) {
        mpc.koDependent = true;
        mpc.outcome = ProofOutcome.Unknown;
        mpc.pn = Math.floor(PN_DN_SATURATION / 2);
        mpc.dn = Math.floor(PN_DN_SATURATION / 2);
        frontier.anyKoDependent = true;
        this.koDependentRejections++;
      }

      // Record sibling certificate RZ for OutsideRZRevalidated pruning (FR-5.5)
      if (
        !frontier.activeNullMoveRz &&
        !isOrNode &&
        mpc.pn === 0 &&
        mpc.proofRz.size > 0 &&
        mpc.dagNodeId >= 0
      ) {
        frontier.activeNullMoveRz = mpc.proofRz;
        frontier.representativeDagId = mpc.dagNodeId;
        frontier.representativeMove = mpc.move;
        frontier.representativeOutcome = ProofOutcome.ProvenWin;
      } else if (
        !frontier.activeNullMoveRz &&
        isOrNode &&
        mpc.dn === 0 &&
        mpc.disproofRz.size > 0 &&
        mpc.dagNodeId >= 0
      ) {
        frontier.activeNullMoveRz = mpc.disproofRz;
        frontier.representativeDagId = mpc.dagNodeId;
        frontier.representativeMove = mpc.move;
        frontier.representativeOutcome = ProofOutcome.ProvenLoss;
      }
    }

    inPathHashes.delete(zHex);

    return {
      pn: finalPn,
      dn: finalDn,
      outcome: finalOutcome,
      koDependent: frontier.anyKoDependent,
      proofRz: finalProofRz,
      disproofRz: finalDisproofRz,
      dagNodeId: finalDagNodeId,
    };
  }

  private extractPrincipalVariation(
    pos: GoPosition,
    context: ProofContext,
    rootNodeId: number,
    boardSize: number
  ): { move: number; sgf: string; color: Color; comment: string }[] {
    const pv: { move: number; sgf: string; color: Color; comment: string }[] =
      [];
    if (rootNodeId < 0 || rootNodeId >= this.proofDagNodes.length) return pv;

    let curNode = this.proofDagNodes[rootNodeId];
    let safety = 0;

    while (curNode && curNode.childNodeIds.length > 0 && safety < 20) {
      safety++;
      let chosenChildIdx = 0;
      for (let i = 0; i < curNode.childNodeIds.length; i++) {
        const chNode = this.proofDagNodes[curNode.childNodeIds[i]];
        if (chNode && chNode.outcome === curNode.outcome) {
          chosenChildIdx = i;
          break;
        }
      }

      const nextNodeId = curNode.childNodeIds[chosenChildIdx];
      const move = curNode.childMoves[chosenChildIdx];
      const nextNode = this.proofDagNodes[nextNodeId];
      if (!nextNode) break;

      const playedColor = pos.toPlay;
      pos.playMove(move);

      pv.push({
        move,
        sgf: coordToSgf(move, boardSize),
        color: playedColor,
        comment: `${
          playedColor === Color.Black ? '黑 (B)' : '白 (W)'
        } 落子 ${coordToHumanLabel(move, boardSize)} → 节点 #${
          nextNode.nodeId
        } (${nextNode.outcome}, Evidence: ${nextNode.terminalEvidence})`,
      });

      curNode = nextNode;
    }

    return pv;
  }
}
