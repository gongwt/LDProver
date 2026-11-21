// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// TypeScript 1:1 execution mirror of src/search/dfpn_solver.cc (FR-4.1..FR-4.10, FR-5.5, FR-5.7)

import { BensonTerminalEvaluator } from './bensonUca';
import {
  coordToHumanLabel,
  coordToSgf,
  GoPosition,
  PASS_MOVE,
} from './position';
import { ProofArtifactManager } from './proofChecker';
import {
  NNAttentionMask,
  ProofCertificateRZ,
  RelevanceZoneEngine,
} from './relevanceZone';
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
  SearchGoal,
  SolveReport,
  SolverConfig,
  StateTableEntry,
  TerminalStatus,
  TsumegoProblemSpec,
  UnknownReason,
} from './types';

function clampSat(val: number): number {
  return val >= PN_DN_SATURATION
    ? PN_DN_SATURATION
    : Math.max(0, Math.floor(val));
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
  checkedNullMoveDagId: number;
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
  private activeAttentionMask: NNAttentionMask | null = null;

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
    const context = DfpnSolver.buildProofContext(problem, this.config);
    const initialPos = DfpnSolver.buildInitialPosition(problem, context);
    return this.solveFromPosition(problem, initialPos, context);
  }

  /**
   * Solves from an arbitrary legal `GoPosition` (either the problem root or an interactive
   * manual move sequence carrying authentic `historySnapshots` and `survivingTargetTokensMask`).
   */
  public solveFromPosition(
    problem: TsumegoProblemSpec,
    initialPos: GoPosition,
    context: ProofContext
  ): SolveReport {
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

    this.activeAttentionMask =
      problem.attentionCoords && problem.attentionCoords.length > 0
        ? new NNAttentionMask(problem.attentionCoords)
        : null;

    const rootPos = initialPos.clone();
    const rootStateId = this.registerState(rootPos, -1, PASS_MOVE);
    const inPathHashes = new Set<string>();

    const rootResult = this.midSearch(
      rootPos,
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

    const rootEval = this.terminalEval.evaluateTerminal(rootPos, context);
    const pv = this.extractPrincipalVariation(
      rootPos.clone(),
      context,
      rootResult.dagNodeId,
      problem.boardSize
    );

    this.compactProofStateAndHistoryTables();

    const elapsedMs = Math.max(1, Math.round(performance.now() - startTime));
    const artifactManager = new ProofArtifactManager();
    const rawRegionCount =
      problem.rawRegionCoords?.length ?? problem.regionCoords.length;

    const partialReport: SolveReport = {
      problemId: problem.id,
      problemTitle: problem.title,
      boardSize: rootPos.boardSize,
      firstToPlay: rootPos.toPlay,
      blackInitialCoords: rootPos.getBlackCoords(),
      whiteInitialCoords: rootPos.getWhiteCoords(),
      immortalWallCoords: Array.from(rootPos.immortalWallSet).sort(
        (a, b) => a - b
      ),
      regionCoords: problem.regionCoords.slice(),
      rawRegionPointCount: rawRegionCount,
      isFullRegionSearch: problem.regionCoords.length >= rawRegionCount,
      inputHash: rootPos.computeZobristHex(),
      configFingerprint: `${this.config.ttMode}:${this.config.koRule}:rz=${this.config.enableRzPruning}:ako=${context.attackerAllowKo}:dko=${context.defenderAllowKo}:reg=${problem.regionCoords.length}/${rawRegionCount}`,
      solverVersion: 'LDProver-1.8.2-cxx20',
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
      artifactManager.serializeLProofJson(rootPos, context, partialReport);
    const { sgf: sgfContent, checksum: sgfChecksum } =
      artifactManager.exportSolutionTreeSgf(rootPos, context, partialReport);

    partialReport.lproofJson = lproofJson;
    partialReport.proofChecksum = proofChecksum;
    partialReport.sgfContent = sgfContent;
    partialReport.sgfChecksum = sgfChecksum;
    partialReport.resultJson =
      artifactManager.serializeResultJson(partialReport);

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

    const expectedTokenColor =
      attackerGoal === SearchGoal.ToLive
        ? rootAttacker
        : oppositeColor(rootAttacker);

    const groups = crucialExpr
      .split(/[&|,]/)
      .map((s) => s.trim())
      .filter(Boolean);

    const initialTokens = groups
      .map((sgf, idx) => {
        if (sgf.length < 2) return null;
        const c = sgf.charCodeAt(0) - 97;
        const r = sgf.charCodeAt(1) - 97;
        if (c < 0 || c >= problem.boardSize || r < 0 || r >= problem.boardSize) {
          return null;
        }
        const coord = r * problem.boardSize + c;
        const isBlack = problem.blackInitialCoords.includes(coord);
        const isWhite = problem.whiteInitialCoords.includes(coord);
        const stoneColor = isBlack
          ? Color.Black
          : isWhite
          ? Color.White
          : expectedTokenColor;
        return {
          tokenId: idx,
          initialCoord: coord,
          groupIndex: idx,
          stoneColor,
        };
      })
      .filter((t): t is NonNullable<typeof t> => t !== null);

    const useProblemDefaults = config.useProblemDefaultKo ?? false;
    const attackerAllowKo = useProblemDefaults
      ? Boolean(problem.attackerAllowKo ?? problem.defaultAllowKo)
      : config.attackerAllowKo;
    const defenderAllowKo = useProblemDefaults
      ? problem.defenderAllowKo ?? true
      : config.defenderAllowKo;

    return {
      contextId: `ctx_${problem.id}_${config.koRule}_${attackerGoal}_ako${
        attackerAllowKo ? 1 : 0
      }_dko${defenderAllowKo ? 1 : 0}`,
      rootAttacker,
      attackerGoal,
      crucialStoneOp: crucialOp,
      koRule: config.koRule,
      attackerAllowKo,
      defenderAllowKo,
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

  /**
   * Prunes unproven df-pn probe scratch states that are never referenced by `proofDagNodes`,
   * while preserving `stateId = 0` and the complete `parentStateId` replay ancestor chain
   * of every node and pruned certificate in `proofDagNodes` in strict topological order.
   */
  private compactProofStateAndHistoryTables(): void {
    if (this.stateTable.length <= 1) return;
    const needed = new Uint8Array(this.stateTable.length);
    needed[0] = 1;

    const markAncestors = (sid: number) => {
      let cur = sid;
      while (cur >= 0 && cur < this.stateTable.length && !needed[cur]) {
        needed[cur] = 1;
        cur = this.stateTable[cur].parentStateId;
      }
    };

    for (let i = 0; i < this.proofDagNodes.length; i++) {
      const n = this.proofDagNodes[i];
      markAncestors(n.stateId);
      if (n.parentStateId >= 0) markAncestors(n.parentStateId);
      if (n.prunedCertificate) {
        markAncestors(n.prunedCertificate.queryStateId);
        markAncestors(n.prunedCertificate.sourceStateId);
      }
    }

    const oldToNewState = new Int32Array(this.stateTable.length).fill(-1);
    const oldToNewHist = new Int32Array(this.historyTable.length).fill(-1);
    const newStates: StateTableEntry[] = [];
    const newHistories: CanonicalSnapshot[][] = [];

    for (let oldId = 0; oldId < this.stateTable.length; oldId++) {
      if (!needed[oldId]) continue;
      const st = this.stateTable[oldId];
      const newSid = newStates.length;
      oldToNewState[oldId] = newSid;

      let newHid = oldToNewHist[st.historyId];
      if (newHid < 0) {
        newHid = newHistories.length;
        oldToNewHist[st.historyId] = newHid;
        newHistories.push(this.historyTable[st.historyId]);
      }

      newStates.push({
        ...st,
        stateId: newSid,
        parentStateId:
          st.parentStateId < 0 ? -1 : oldToNewState[st.parentStateId],
        historyId: newHid,
      });
    }

    if (newStates.length === this.stateTable.length) return;

    for (let i = 0; i < this.proofDagNodes.length; i++) {
      const n = this.proofDagNodes[i];
      n.stateId = oldToNewState[n.stateId];
      n.historyId = oldToNewHist[n.historyId];
      n.parentStateId =
        n.parentStateId < 0 ? -1 : oldToNewState[n.parentStateId];
      if (n.prunedCertificate) {
        const pc = n.prunedCertificate;
        pc.queryStateId = oldToNewState[pc.queryStateId];
        pc.queryHistoryId = oldToNewHist[pc.queryHistoryId];
        pc.sourceStateId = oldToNewState[pc.sourceStateId];
        pc.sourceHistoryId = oldToNewHist[pc.sourceHistoryId];
      }
    }

    this.stateTable = newStates;
    this.historyTable = newHistories;
  }

  // FR-4.10: Fast tactical move ordering & heuristic initial (pn, dn) estimation
  private evaluateCandidateMove(
    pos: GoPosition,
    context: ProofContext,
    move: number,
    isOrNode: boolean,
    parentEyeLikeCount: number
  ): {
    score: number;
    immediateWin: boolean;
    immediateLoss: boolean;
    inAttention: boolean;
  } {
    if (move === PASS_MOVE) {
      if (pos.consecutivePasses >= 1) {
        const probe = pos.clone();
        probe.playMove(PASS_MOVE);
        const term = this.terminalEval.evaluateTerminal(probe, context);
        if (isOrNode && term.status === TerminalStatus.Win) {
          return {
            score: 60000,
            immediateWin: true,
            immediateLoss: false,
            inAttention: true,
          };
        }
        if (!isOrNode && term.status === TerminalStatus.Loss) {
          return {
            score: 60000,
            immediateWin: false,
            immediateLoss: true,
            inAttention: true,
          };
        }
      }
      // At AND nodes (consecutivePasses === 0), keep Null-Move (PASS) inside the initial window:
      // #1 priority when attacker already has >= 2 eye-like pockets, or mid-window (#4..#6)
      // otherwise so W[pass] establishes a compact activeNullMoveRz for OutsideRZRevalidated
      // across the full 153-point region once urgent tactical refutations fail!
      if (!isOrNode && pos.consecutivePasses === 0) {
        if (parentEyeLikeCount >= 2) {
          return {
            score: 1650,
            immediateWin: false,
            immediateLoss: false,
            inAttention: true,
          };
        }
        return {
          score: 360,
          immediateWin: false,
          immediateLoss: false,
          inAttention: true,
        };
      }
      return {
        score: -2500,
        immediateWin: false,
        immediateLoss: false,
        inAttention: false,
      };
    }

    const inAttention = this.activeAttentionMask
      ? this.activeAttentionMask.coords.has(move)
      : true;

    // Fast O(1) path for outer buffer-moat moves (`!inAttention`) that touch no tactical
    // (non-immortal) stones: prevents outer-wall contact from out-scoring local eye/Null-Move!
    if (!inAttention) {
      let touchesTacticalStone = false;
      const nbs = pos.orthogonalNeighbors(move);
      for (let i = 0; i < nbs.length; i++) {
        const nb = nbs[i];
        if (pos.grid[nb] !== Color.Empty && !pos.immortalWallSet.has(nb)) {
          touchesTacticalStone = true;
          break;
        }
      }
      if (!touchesTacticalStone) {
        return {
          score: -950,
          immediateWin: false,
          immediateLoss: false,
          inAttention: false,
        };
      }
    }

    let score = inAttention ? 150 : -950;

    // 1. Proximity to crucial target chains and their liberties
    context.initialTokens.forEach((tok, idx) => {
      if ((pos.survivingTargetTokensMask & (1 << idx)) === 0) return;
      const { stones, liberties } = pos.floodFillChain(tok.initialCoord);
      if (liberties.has(move)) {
        score += 550;
        if (liberties.size === 1) score += 1350;
        else if (liberties.size === 2) score += 720;
      }
      const adjCount = pos
        .orthogonalNeighbors(move)
        .filter((n) => stones.has(n)).length;
      if (adjCount >= 2) score += 620;
    });

    const enemyColor = oppositeColor(pos.toPlay);

    // Pre-move liberty count of adjacent non-immortal enemy chains (Semeai / cutting stones)
    let tightenedLowLibEnemy = false;
    let tightenedCuttingEnemy = false;
    let minEnemyLibBefore = 99;
    const seenEnemyBefore = new Set<number>();
    for (const nb of pos.orthogonalNeighbors(move)) {
      if (
        pos.stoneAt(nb) === enemyColor &&
        !pos.immortalWallSet.has(nb) &&
        !seenEnemyBefore.has(nb)
      ) {
        const echBefore = pos.floodFillChain(nb);
        for (const s of echBefore.stones) seenEnemyBefore.add(s);
        if (echBefore.liberties.size < minEnemyLibBefore) {
          minEnemyLibBefore = echBefore.liberties.size;
        }
        if (echBefore.liberties.size <= 3) {
          tightenedLowLibEnemy = true;
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

    // 2. Simulate move on probe for fast capture & chain liberty checks
    const probe = pos.clone();
    const res = probe.playMove(move);
    if (!res.legal) {
      return {
        score: -99999,
        immediateWin: false,
        immediateLoss: false,
        inAttention: false,
      };
    }

    // Fast O(tokens) crucial-token capture check without full board Benson flood-fill
    if (res.capturedCoords.length > 0) {
      score += 1300 + res.capturedCoords.length * 320;
      const allCrucialGone =
        context.crucialStoneOp === LogicalOp.Conjunction
          ? context.initialTokens.some(
              (_, idx) => (probe.survivingTargetTokensMask & (1 << idx)) === 0
            )
          : context.initialTokens.every(
              (_, idx) => (probe.survivingTargetTokensMask & (1 << idx)) === 0
            );
      if (allCrucialGone) {
        const tokCapIsWin = context.attackerGoal === SearchGoal.ToKill;
        if (isOrNode && tokCapIsWin) {
          return {
            score: 55000,
            immediateWin: true,
            immediateLoss: false,
            inAttention: true,
          };
        }
        if (!isOrNode && !tokCapIsWin) {
          return {
            score: 55000,
            immediateWin: false,
            immediateLoss: true,
            inAttention: true,
          };
        }
      }
    }

    const ourChain = probe.floodFillChain(move);
    if (ourChain.liberties.size === 1) {
      let isTesujiThrowIn = false;
      if (res.capturedCoords.length === 0 && inAttention) {
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
        score += 920;
      } else {
        const adjStone = pos
          .orthogonalNeighbors(move)
          .some((n) => probe.stoneAt(n) !== Color.Empty);
        score += adjStone ? -180 : -750;
      }
    } else if (ourChain.liberties.size >= 3) {
      score += 240;
    }

    if (tightenedLowLibEnemy && ourChain.liberties.size >= 2) {
      score += tightenedCuttingEnemy ? 780 : 420;
    }

    for (const nb of pos.orthogonalNeighbors(move)) {
      if (probe.stoneAt(nb) === enemyColor && !probe.immortalWallSet.has(nb)) {
        const enemyCh = probe.floodFillChain(nb);
        if (enemyCh.liberties.size === 1) {
          score += 760;
        } else if (
          enemyCh.liberties.size === 2 &&
          enemyCh.liberties.size < minEnemyLibBefore
        ) {
          score += 360;
        }
      }
    }

    // 3. Corner / Edge vital geometry heuristics
    const r = Math.floor(move / pos.boardSize);
    const c = move % pos.boardSize;
    const distR = Math.min(r, pos.boardSize - 1 - r);
    const distC = Math.min(c, pos.boardSize - 1 - c);
    const distEdge = Math.min(distR, distC);

    if (distR === 1 && distC === 1) {
      score += 440;
    } else if (distEdge === 1) {
      score += 240;
    } else if (distEdge === 0) {
      score += 160;
    }

    const friendlyChainRoots = new Set<number>();
    let hasTacticalFriendlyAdj = false;
    let friendlyOrthoCount = 0;
    let enemyOrthoCount = 0;
    for (const nb of pos.orthogonalNeighbors(move)) {
      const st = pos.stoneAt(nb);
      if (st === pos.toPlay) {
        friendlyOrthoCount++;
        if (!pos.immortalWallSet.has(nb)) {
          hasTacticalFriendlyAdj = true;
        }
        const ch = pos.floodFillChain(nb);
        if (ch.liberties.size >= 2) {
          friendlyChainRoots.add(Math.min(...Array.from(ch.stones)));
        }
      } else if (st === enemyColor) {
        enemyOrthoCount++;
      }
    }
    if (friendlyChainRoots.size >= 2 && hasTacticalFriendlyAdj) {
      score += 860;
    }

    let friendlyDiagCount = 0;
    let enemyDiagCount = 0;
    for (const d of pos.diagonalNeighbors(move)) {
      const st = pos.stoneAt(d);
      if (st === pos.toPlay) friendlyDiagCount++;
      else if (st === enemyColor) enemyDiagCount++;
    }
    const emptyOrthoNbs = pos
      .orthogonalNeighbors(move)
      .filter((n) => pos.stoneAt(n) === Color.Empty);
    if (emptyOrthoNbs.length >= 2 && inAttention) {
      // Check if two empty orthogonal neighbors are separated (vital eye-splitting / nakade point!)
      let splitsEyeCavity = false;
      for (let i = 0; i < emptyOrthoNbs.length && !splitsEyeCavity; i++) {
        for (let j = i + 1; j < emptyOrthoNbs.length; j++) {
          const a = emptyOrthoNbs[i];
          const b = emptyOrthoNbs[j];
          const sharedEmpty = pos
            .orthogonalNeighbors(a)
            .some(
              (x) =>
                x !== move &&
                pos.stoneAt(x) === Color.Empty &&
                pos.orthogonalNeighbors(b).includes(x)
            );
          if (!sharedEmpty) {
            splitsEyeCavity = true;
            break;
          }
        }
      }
      if (splitsEyeCavity && (friendlyOrthoCount >= 1 || enemyOrthoCount >= 1 || friendlyDiagCount >= 2 || enemyDiagCount >= 2)) {
        score += 950;
      }
    }

    if (
      friendlyDiagCount >= 2 &&
      enemyOrthoCount === 0 &&
      (friendlyOrthoCount === 0 ||
        friendlyChainRoots.size >= 2 ||
        enemyDiagCount >= 1)
    ) {
      score += 500;
      for (const enb of pos.orthogonalNeighbors(move)) {
        if (pos.stoneAt(enb) === Color.Empty) {
          const enbFriendlyWalls = pos
            .orthogonalNeighbors(enb)
            .filter((n) => n === move || pos.stoneAt(n) === pos.toPlay).length;
          if (enbFriendlyWalls >= 3) {
            score += 680;
          }
        }
      }
    } else if (
      emptyOrthoNbs.length <= 1 &&
      friendlyOrthoCount >= 1 &&
      friendlyChainRoots.size <= 1 &&
      friendlyDiagCount >= 2 &&
      enemyOrthoCount === 0 &&
      enemyDiagCount === 0
    ) {
      // Pure 1- or 2-point internal eye space under a single solid chain — avoid self-filling eye!
      score -= 320;
    }
    if (friendlyOrthoCount >= 1 && enemyOrthoCount >= 1) {
      score += 380;
    }
    if (friendlyOrthoCount >= 1 && enemyDiagCount >= 1) {
      score += 320;
    }

    return {
      score,
      immediateWin: false,
      immediateLoss: false,
      inAttention,
    };
  }

  // Assign heuristic initial (pn_0, dn_0) in [1, 200] to prevent uniform breadth-first collapse
  private computeInitialChildBounds(
    rankIdx: number,
    isOrNode: boolean,
    meta: {
      score: number;
      immediateWin: boolean;
      immediateLoss: boolean;
      inAttention: boolean;
    },
    move: number
  ): { pn: number; dn: number } {
    if (!this.config.enableFastCaptureOrdering) {
      return { pn: 1, dn: 1 };
    }
    if (isOrNode) {
      if (meta.immediateWin) return { pn: 1, dn: 10 };
      if (meta.immediateLoss) return { pn: 180, dn: 1 };
      if (move === PASS_MOVE) return { pn: 220, dn: 1 };
      if (!meta.inAttention) {
        return { pn: 2400 + rankIdx * 16, dn: 1 };
      }
      let pn = 1;
      if (rankIdx === 0) pn = 1;
      else if (rankIdx === 1) pn = 2;
      else if (rankIdx === 2) pn = 3;
      else if (rankIdx <= 5) pn = 4 + (rankIdx - 3) * 2;
      else if (rankIdx <= 10) pn = 10 + (rankIdx - 5) * 2;
      else pn = 22 + (rankIdx - 10) * 3;
      if (meta.score < 0) pn += 20;
      return { pn, dn: 1 };
    } else {
      // AND node: `dn` drives selection of defender refutations; `pn` aggregates proof obligation
      if (meta.immediateLoss) return { pn: 10, dn: 1 };
      if (move === PASS_MOVE) {
        return meta.score >= 1500 ? { pn: 1, dn: 1 } : { pn: 1, dn: 4 };
      }
      if (!meta.inAttention) {
        return { pn: 1, dn: 85 + rankIdx * 3 };
      }
      let dn = 1;
      if (rankIdx === 0) dn = 1;
      else if (rankIdx <= 2) dn = 2;
      else if (rankIdx <= 5) dn = 3 + (rankIdx - 2);
      else if (rankIdx <= 10) dn = 7 + (rankIdx - 5) * 2;
      else dn = 18 + (rankIdx - 10) * 3;
      if (meta.score < 0) dn += 12;
      return { pn: 1, dn };
    }
  }

  // FR-5.5: Revalidate source proof subgraph under QueryState + HistorySet (both witness & full-coverage!)
  private revalidateSourceProofOnQueryState(
    queryPos: GoPosition,
    context: ProofContext,
    regionCoords: number[],
    sourceDagNodeId: number,
    expectedOutcome: ProofOutcome,
    guardDepth = 0
  ): boolean {
    if (
      guardDepth > 48 ||
      sourceDagNodeId < 0 ||
      sourceDagNodeId >= this.proofDagNodes.length
    ) {
      return false;
    }

    let sourceNode = this.proofDagNodes[sourceDagNodeId];
    let unwrapSafety = 0;
    while (
      sourceNode &&
      (sourceNode.isPrunedOutsideRz || sourceNode.isTtHit) &&
      sourceNode.sourceProofNodeId !== null &&
      sourceNode.sourceProofNodeId >= 0 &&
      sourceNode.sourceProofNodeId < sourceNode.nodeId &&
      unwrapSafety < 32
    ) {
      unwrapSafety++;
      sourceNode = this.proofDagNodes[sourceNode.sourceProofNodeId];
    }
    if (!sourceNode || sourceNode.outcome !== expectedOutcome) return false;

    const checkEarlyTerminal = (): boolean | null => {
      const term = this.terminalEval.evaluateTerminal(queryPos, context, false);
      if (term.status === TerminalStatus.Win) {
        return expectedOutcome === ProofOutcome.ProvenWin;
      }
      if (term.status === TerminalStatus.Loss) {
        return expectedOutcome === ProofOutcome.ProvenLoss;
      }
      return null;
    };

    if (sourceNode.childNodeIds.length === 0 || queryPos.isAtDoublePass()) {
      return checkEarlyTerminal() === true;
    }

    const isOr = queryPos.toPlay === context.rootAttacker;
    const restrictedSide =
      (queryPos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
      (queryPos.toPlay !== context.rootAttacker && !context.defenderAllowKo);

    const allowedRegion =
      regionCoords.length > 0 ? new Set<number>(regionCoords) : null;

    // Case 1: Single-witness node (OR -> ProvenWin, or AND -> ProvenLoss)
    if (
      (isOr && expectedOutcome === ProofOutcome.ProvenWin) ||
      (!isOr && expectedOutcome === ProofOutcome.ProvenLoss)
    ) {
      for (let i = 0; i < sourceNode.childNodeIds.length; i++) {
        const mv = sourceNode.childMoves[i];
        if (mv !== PASS_MOVE && allowedRegion !== null && !allowedRegion.has(mv)) {
          continue;
        }
        const chNode = this.proofDagNodes[sourceNode.childNodeIds[i]];
        if (!chNode || chNode.outcome !== expectedOutcome) continue;
        const nextPos = queryPos.clone();
        const playRes = nextPos.playMove(mv);
        if (!playRes.legal) continue;
        if (playRes.isKoCapture && restrictedSide) continue;
        if (
          this.revalidateSourceProofOnQueryState(
            nextPos,
            context,
            regionCoords,
            sourceNode.childNodeIds[i],
            expectedOutcome,
            guardDepth + 1
          )
        ) {
          return true;
        }
      }
      return checkEarlyTerminal() === true;
    }

    // Case 2: Full-coverage node (AND -> ProvenWin, or OR -> ProvenLoss)
    // Every legal move on `queryPos` MUST be covered in `sourceNode` and recursively hold!
    const moveMap = new Map<number, number>();
    for (let i = 0; i < sourceNode.childMoves.length; i++) {
      moveMap.set(sourceNode.childMoves[i], sourceNode.childNodeIds[i]);
    }

    const queryLegalMoves = queryPos.generateLegalMoves(regionCoords);
    for (const mv of queryLegalMoves) {
      const childDagId = moveMap.get(mv);
      if (childDagId === undefined) {
        return checkEarlyTerminal() === true;
      }
      const nextPos = queryPos.clone();
      const playRes = nextPos.playMove(mv);
      if (!playRes.legal) continue;
      if (
        !this.revalidateSourceProofOnQueryState(
          nextPos,
          context,
          regionCoords,
          childDagId,
          expectedOutcome,
          guardDepth + 1
        )
      ) {
        return checkEarlyTerminal() === true;
      }
    }

    return true;
  }

  private isMemoryBudgetExceeded(): boolean {
    if (
      !Number.isFinite(this.config.memoryBudgetMb) ||
      this.config.memoryBudgetMb <= 0
    ) {
      return false;
    }
    const budgetBytes = this.config.memoryBudgetMb * 1024 * 1024;
    // Conservative byte estimate across stateTable, historyTable, DAG nodes, frontier cache, and TT
    const estimatedBytes =
      this.stateTable.length * 1024 +
      this.historyTable.length * 2048 +
      this.proofDagNodes.length * 768 +
      this.nodeFrontierCache.size * 4096 +
      this.ttStore.size * 1024;
    return estimatedBytes > budgetBytes;
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

    // Step 1 (FR-3.2, FR-3.8): Evaluate Terminal BEFORE InPath cycle detection
    const term = this.terminalEval.evaluateTerminal(pos, context, false);
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
    if (this.isMemoryBudgetExceeded()) {
      this.resourceExhausted = true;
      this.unknownReason = UnknownReason.MemoryBudget;
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

    const emitTtHitNode = (
      sourceDagNodeId: number,
      pn: number,
      dn: number,
      outcome: ProofOutcome,
      proofRz: ProofCertificateRZ,
      disproofRz: ProofCertificateRZ
    ): number => {
      const ttDagId = this.proofDagNodes.length;
      const stEntry = this.stateTable[currentStateId];
      this.proofDagNodes.push({
        nodeId: ttDagId,
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
        terminalEvidence: 'TT_REVALIDATED_REUSE',
        isPrunedOutsideRz: false,
        isTtHit: true,
        isKoDependentBarrier: false,
        sourceProofNodeId: sourceDagNodeId,
        proofRzCoords: proofRz.toArray(),
        disproofRzCoords: disproofRz.toArray(),
        childNodeIds: [],
        childMoves: [],
      });
      this.dagHasCapture.push(Boolean(this.dagHasCapture[sourceDagNodeId]));
      return ttDagId;
    };

    // Step 4 (FR-6.1, FR-6.3, FR-6.9): History-safe BoardTT & PatternTT lookup
    const boardHit = this.ttStore.lookupBoardTT(
      pos,
      context,
      (dagNodeId, outcome) =>
        this.revalidateSourceProofOnQueryState(
          pos,
          context,
          regionCoords,
          dagNodeId,
          outcome
        )
    );
    if (
      boardHit &&
      boardHit.outcome !== ProofOutcome.Unknown &&
      boardHit.proofClosureAvailable &&
      boardHit.proofDagNodeId >= 0
    ) {
      const ttNodeId = emitTtHitNode(
        boardHit.proofDagNodeId,
        boardHit.pn,
        boardHit.dn,
        boardHit.outcome,
        boardHit.proofRz,
        boardHit.disproofRz
      );
      return {
        pn: boardHit.pn,
        dn: boardHit.dn,
        outcome: boardHit.outcome,
        koDependent: false,
        proofRz: boardHit.proofRz,
        disproofRz: boardHit.disproofRz,
        dagNodeId: ttNodeId,
      };
    }

    if (this.config.ttMode === 'pattern-tt') {
      const patHit = this.ttStore.lookupPatternTT(pos, context);
      if (
        patHit.grade === 'PROOF_REUSABLE' &&
        patHit.record &&
        patHit.record.proofDagNodeId >= 0
      ) {
        const ttNodeId = emitTtHitNode(
          patHit.record.proofDagNodeId,
          patHit.record.pn,
          patHit.record.dn,
          patHit.record.outcome,
          patHit.record.storedRz,
          patHit.record.storedRz
        );
        return {
          pn: patHit.record.pn,
          dn: patHit.record.dn,
          outcome: patHit.record.outcome,
          koDependent: false,
          proofRz: patHit.record.storedRz,
          disproofRz: patHit.record.storedRz,
          dagNodeId: ttNodeId,
        };
      }
      if (
        patHit.grade === 'HEURISTIC_ONLY' &&
        patHit.record &&
        patHit.record.proofClosureAvailable &&
        patHit.record.proofDagNodeId >= 0 &&
        this.revalidateSourceProofOnQueryState(
          pos,
          context,
          regionCoords,
          patHit.record.proofDagNodeId,
          patHit.record.outcome
        )
      ) {
        this.ttStore.patternProofReusableHits++;
        const ttNodeId = emitTtHitNode(
          patHit.record.proofDagNodeId,
          patHit.record.pn,
          patHit.record.dn,
          patHit.record.outcome,
          patHit.record.storedRz,
          patHit.record.storedRz
        );
        return {
          pn: patHit.record.pn,
          dn: patHit.record.dn,
          outcome: patHit.record.outcome,
          koDependent: false,
          proofRz: patHit.record.storedRz,
          disproofRz: patHit.record.storedRz,
          dagNodeId: ttNodeId,
        };
      }
    }

    // Step 5: Lookup or initialize history-isolated cached frontier node for persistent DFPN bounds.
    // Includes `computeCanonicalHistoryKey()` so SSK/PSK histories never share cached child outcomes!
    const historyKey = pos.computeCanonicalHistoryKey();
    const frontierKey = `${zHex}:${pos.toPlay}:${pos.koPoint}:${pos.consecutivePasses}:${pos.survivingTargetTokensMask}:${historyKey}`;
    let frontier = this.nodeFrontierCache.get(frontierKey);
    if (!frontier) {
      const parentShape =
        !isOrNode && pos.consecutivePasses === 0 && this.config.enableFastCaptureOrdering
          ? this.terminalEval.estimateHeuristicShapePotential(
              pos,
              context.initialTokens
            )
          : { eyeLikeCount: 0, minCrucialLiberties: 0, minAdjacentEnemyLiberties: 99 };
      const legalMoves = pos.generateLegalMoves(regionCoords);
      const scored = legalMoves.map((mv) => {
        const meta = this.config.enableFastCaptureOrdering
          ? this.evaluateCandidateMove(
              pos,
              context,
              mv,
              isOrNode,
              parentShape.eyeLikeCount
            )
          : {
              score: 0,
              immediateWin: false,
              immediateLoss: false,
              inAttention: true,
            };
        return { mv, meta };
      });

      if (this.config.enableFastCaptureOrdering) {
        scored.sort((a, b) => b.meta.score - a.meta.score);
      }

      const children: SearchChildSlot[] = scored.map(({ mv, meta }, idx) => {
        const initBounds = this.computeInitialChildBounds(
          idx,
          isOrNode,
          meta,
          mv
        );
        return {
          move: mv,
          tacticalScore: meta.score,
          pn: initBounds.pn,
          dn: initBounds.dn,
          outcome: ProofOutcome.Unknown,
          expanded: false,
          prunedOutsideRz: false,
          koDependent: false,
          stateId: -1,
          hasCapture: false,
          checkedNullMoveDagId: -1,
          dagNodeId: -1,
          proofRz: new ProofCertificateRZ(),
          disproofRz: new ProofCertificateRZ(),
        };
      });

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
      if (this.config.enableProgressiveWidening && frontier.wideningLevel < 6) {
        const baseK = isOrNode
          ? this.config.wideningBaseK
          : Math.max(4, Math.floor(this.config.wideningBaseK / 2));
        const cap = baseK * Math.pow(2, frontier.wideningLevel);
        if (cap < totalLegal) windowSize = cap;
      }

      // FR-5.5: OutsideRZRevalidated sibling/null-move certificate pruning
      if (
        this.config.enableRzPruning &&
        frontier.activeNullMoveRz &&
        frontier.representativeDagId >= 0
      ) {
        const restrictedSide =
          (pos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
          (pos.toPlay !== context.rootAttacker && !context.defenderAllowKo);

        for (let i = 0; i < windowSize; i++) {
          const ch = children[i];
          if (
            ch.expanded ||
            ch.outcome !== ProofOutcome.Unknown ||
            ch.checkedNullMoveDagId === frontier.representativeDagId
          ) {
            continue;
          }
          ch.checkedNullMoveDagId = frontier.representativeDagId;
          if (
            this.rzEngine.isOutsideRZCandidate(
              ch.move,
              frontier.activeNullMoveRz
            )
          ) {
            const nextPos = pos.clone();
            const playRes = nextPos.playMove(ch.move);
            if (
              playRes.legal &&
              !(playRes.isKoCapture && restrictedSide) &&
              this.revalidateSourceProofOnQueryState(
                nextPos,
                context,
                regionCoords,
                frontier.representativeDagId,
                frontier.representativeOutcome
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

      // FR-4.1: Frontier PN/DN aggregation with consistent progressive-widening trigger
      const unexpandedU = Math.max(0, totalLegal - windowSize);
      const widenTrigger =
        unexpandedU > 0
          ? Math.max(
              isOrNode ? children[windowSize].pn : children[windowSize].dn,
              (isOrNode ? 14 : 10) * (frontier.wideningLevel + 1)
            )
          : PN_DN_SATURATION;
      let curPn = 1;
      let curDn = 1;

      let forceExpandPassIdx = -1;
      if (isOrNode) {
        let minPn = PN_DN_SATURATION;
        let windowSumDn = 0;
        for (let i = 0; i < windowSize; i++) {
          minPn = Math.min(minPn, children[i].pn);
          windowSumDn = clampSat(windowSumDn + children[i].dn);
        }
        if (unexpandedU > 0) {
          minPn = Math.min(minPn, widenTrigger);
        }
        if (windowSumDn === 0 && windowSize < totalLegal) {
          frontier.wideningLevel = frontier.activeNullMoveRz
            ? 6
            : frontier.wideningLevel + 1;
          this.wideningUpgrades++;
          continue;
        }
        curPn = minPn;
        curDn = clampSat(windowSumDn + (unexpandedU > 0 ? 1 : 0));
      } else {
        let windowSumPn = 0;
        let minDn = PN_DN_SATURATION;
        for (let i = 0; i < windowSize; i++) {
          windowSumPn = clampSat(windowSumPn + children[i].pn);
          minDn = Math.min(minDn, children[i].dn);
        }
        if (unexpandedU > 0) {
          minDn = Math.min(minDn, widenTrigger);
        }
        if (windowSumPn === 0 && windowSize < totalLegal) {
          // Before widening across the full 153-point region, ensure Null-Move (PASS_MOVE)
          // has been expanded first if legal, so `activeNullMoveRz` carries a stone-free
          // tenuki certificate capable of OutsideRZRevalidated-pruning the outer moat!
          const passIdx = children.findIndex(
            (c) => c.move === PASS_MOVE && !c.expanded && !c.koDependent
          );
          if (passIdx >= 0 && this.config.enableRzPruning) {
            forceExpandPassIdx = passIdx;
            curPn = 1;
            curDn = Math.max(1, children[passIdx].dn);
          } else {
            frontier.wideningLevel = frontier.activeNullMoveRz
              ? 6
              : frontier.wideningLevel + 1;
            this.wideningUpgrades++;
            continue;
          }
        } else {
          curPn = clampSat(windowSumPn + (unexpandedU > 0 ? 1 : 0));
          curDn = minDn;
        }
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
        this.numNodes >= this.config.maxNodes ||
        this.isMemoryBudgetExceeded()
      ) {
        if (this.isMemoryBudgetExceeded()) {
          this.resourceExhausted = true;
          this.unknownReason = UnknownReason.MemoryBudget;
        }
        finalPn = curPn;
        finalDn = curDn;
        finalOutcome = ProofOutcome.Unknown;
        break;
      }

      // Select most-proving child within current window (skipping koDependent barriers)
      let bestIdx = -1;
      let bestMetric = PN_DN_SATURATION;
      let secondBestMetric = PN_DN_SATURATION;

      if (forceExpandPassIdx >= 0) {
        bestIdx = forceExpandPassIdx;
        bestMetric = children[forceExpandPassIdx].dn;
        secondBestMetric = PN_DN_SATURATION;
      } else {
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

        // Progressive Widening upgrade condition: widen as soon as active window reaches widenTrigger
        if (unexpandedU > 0) {
          if (bestIdx < 0 || bestMetric >= widenTrigger) {
            frontier.wideningLevel++;
            this.wideningUpgrades++;
            continue;
          }
          secondBestMetric = Math.min(secondBestMetric, widenTrigger);
        }
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
      if (depth === 0) {
        this.rootBestMove = mpc.move;
      }
      // 1+epsilon df-pn (Pawlewicz & Lew / Kishimoto & Mueller) to prevent +1 ping-pong thrashing
      const epsMetricBound = clampSat(
        Math.max(secondBestMetric + 1, Math.ceil(secondBestMetric * 1.25) + 1)
      );
      let childThPn = thPn;
      let childThDn = thDn;
      if (isOrNode) {
        childThPn = Math.min(thPn, epsMetricBound);
        const otherDn = curDn - mpc.dn;
        childThDn =
          thDn >= PN_DN_SATURATION
            ? PN_DN_SATURATION
            : thDn > otherDn
            ? Math.max(2, thDn - otherDn)
            : 1;
      } else {
        const otherPn = curPn - mpc.pn;
        childThPn =
          thPn >= PN_DN_SATURATION
            ? PN_DN_SATURATION
            : thPn > otherPn
            ? Math.max(2, thPn - otherPn)
            : 1;
        childThDn = Math.min(thDn, epsMetricBound);
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

      // Record compact sibling certificate RZ for OutsideRZRevalidated pruning (FR-5.5).
      // Prefer PASS_MOVE (Null-Move) representative at AND nodes because no stone was added on
      // `sourcePos`, guaranteeing `queryLegalMoves ⊆ sourceLegalMoves` at full-coverage descendants!
      if (
        !isOrNode &&
        mpc.pn === 0 &&
        mpc.proofRz.size > 0 &&
        mpc.dagNodeId >= 0 &&
        (!frontier.activeNullMoveRz ||
          (mpc.move === PASS_MOVE && frontier.representativeMove !== PASS_MOVE) ||
          ((mpc.move === PASS_MOVE) ===
            (frontier.representativeMove === PASS_MOVE) &&
            mpc.proofRz.size < frontier.activeNullMoveRz.size))
      ) {
        frontier.activeNullMoveRz = mpc.proofRz;
        frontier.representativeDagId = mpc.dagNodeId;
        frontier.representativeMove = mpc.move;
        frontier.representativeOutcome = ProofOutcome.ProvenWin;
      } else if (
        isOrNode &&
        mpc.move !== PASS_MOVE &&
        mpc.dn === 0 &&
        mpc.disproofRz.size > 0 &&
        mpc.dagNodeId >= 0 &&
        (!frontier.activeNullMoveRz ||
          mpc.disproofRz.size < frontier.activeNullMoveRz.size)
      ) {
        frontier.activeNullMoveRz = mpc.disproofRz;
        frontier.representativeDagId = mpc.dagNodeId;
        frontier.representativeMove = mpc.move;
        frontier.representativeOutcome = ProofOutcome.ProvenLoss;
      }
    }

    inPathHashes.delete(zHex);

    if (depth === 0 && finalOutcome === ProofOutcome.Unknown && children.length > 0) {
      const viable = children.filter(
        (c) =>
          !c.koDependent &&
          (isOrNode ? c.dn > 0 && c.pn < PN_DN_SATURATION : c.pn > 0 && c.dn < PN_DN_SATURATION)
      );
      if (viable.length > 0) {
        viable.sort((a, b) => {
          if (isOrNode) {
            if (b.dn !== a.dn) return b.dn - a.dn;
            if (a.pn !== b.pn) return a.pn - b.pn;
            return b.tacticalScore - a.tacticalScore;
          }
          if (b.pn !== a.pn) return b.pn - a.pn;
          if (a.dn !== b.dn) return a.dn - b.dn;
          return b.tacticalScore - a.tacticalScore;
        });
        this.rootBestMove = viable[0].move;
      }
    }

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
    _context: ProofContext,
    rootNodeId: number,
    boardSize: number
  ): { move: number; sgf: string; color: Color; comment: string }[] {
    const pv: { move: number; sgf: string; color: Color; comment: string }[] =
      [];
    if (rootNodeId < 0 || rootNodeId >= this.proofDagNodes.length) return pv;

    let curNode = this.proofDagNodes[rootNodeId];
    let safety = 0;

    while (curNode && curNode.childNodeIds.length > 0 && safety < 24) {
      safety++;
      if (
        (curNode.isPrunedOutsideRz || curNode.isTtHit) &&
        curNode.sourceProofNodeId !== null &&
        this.proofDagNodes[curNode.sourceProofNodeId]
      ) {
        curNode = this.proofDagNodes[curNode.sourceProofNodeId];
        if (curNode.childNodeIds.length === 0) break;
      }

      let chosenChildIdx = 0;
      // Prefer non-pass tactical witness / non-pruned defense along the main line for clearer PV playback
      for (let i = 0; i < curNode.childNodeIds.length; i++) {
        const chNode = this.proofDagNodes[curNode.childNodeIds[i]];
        if (
          chNode &&
          chNode.outcome === curNode.outcome &&
          !chNode.isPrunedOutsideRz &&
          curNode.childMoves[i] !== PASS_MOVE
        ) {
          chosenChildIdx = i;
          break;
        }
      }
      if (
        !this.proofDagNodes[curNode.childNodeIds[chosenChildIdx]] ||
        this.proofDagNodes[curNode.childNodeIds[chosenChildIdx]].outcome !==
          curNode.outcome
      ) {
        for (let i = 0; i < curNode.childNodeIds.length; i++) {
          const chNode = this.proofDagNodes[curNode.childNodeIds[i]];
          if (chNode && chNode.outcome === curNode.outcome) {
            chosenChildIdx = i;
            break;
          }
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
