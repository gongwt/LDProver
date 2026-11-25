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
  BranchCoverageObligation,
  BranchCoverageSnapshot,
  BranchMoveCoverageEntry,
  BranchMoveCoverageStatus,
  CanonicalSnapshot,
  Color,
  FrontierMemoryDiagnostics,
  LogicalOp,
  oppositeColor,
  PN_DN_SATURATION,
  ParentUsableSubproofEvent,
  ProofContext,
  ProofDagNode,
  ProofOutcome,
  PrunedCertificateRecord,
  ResidualDivergenceKind,
  ResidualReplayDiagnostics,
  ResidualSiblingReplayMode,
  SearchGoal,
  SearchPathTraceEvent,
  ShortTacticalProbeConfig,
  ShortTacticalProbeDiagnostics,
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
  lastThPn?: number;
  lastThDn?: number;
  lastExitReason?: string;
  subtreeWorkNodes?: number;
  firstDivergence?: ResidualDivergenceKind;
  triedSourceDagIds?: Set<number>;
}

interface CachedNodeFrontier {
  children: SearchChildSlot[];
  wideningLevel: number;
  activeNullMoveRz: ProofCertificateRZ | null;
  representativeDagId: number;
  representativeMove: number;
  representativeOutcome: ProofOutcome;
  anyKoDependent: boolean;
  lastPn: number;
  lastDn: number;
  lastThPn: number;
  lastThDn: number;
  lastExitReason: string;
  lastWindowSize: number;
  nodeDagNodeId: number;
  nodeOutcome: ProofOutcome;
  provenSources?: Array<{
    move: number;
    dagId: number;
    rz: ProofCertificateRZ;
  }>;
}

interface NodeTacticalContext {
  chainIdAt: Int32Array;
  chainLibs: Int32Array;
  chainMinStone: Int32Array;
  chainIsImmortal: Uint8Array;
  chainIsCuttingEnemy: Uint8Array;
  crucialStoneMask: Uint8Array;
  crucialLibMinLibs: Int32Array;
  targetColor: Color;
}

export class DfpnSolver {
  private readonly config: SolverConfig;
  private readonly terminalEval = new BensonTerminalEvaluator();
  private readonly rzEngine = new RelevanceZoneEngine();
  private readonly ttStore = new TranspositionStore();
  private readonly nodeFrontierCache = new Map<number, CachedNodeFrontier>();
  private readonly revalCache = new Map<string, boolean>();
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
  private tracePathFilterSet: Set<string> | null = null;
  private residualDiag: ResidualReplayDiagnostics;
  private shortProbeDiag: ShortTacticalProbeDiagnostics;
  private lastSolveContext: ProofContext | null = null;
  private lastSolveRegionCoords: number[] | null = null;

  constructor(config: SolverConfig) {
    this.config = { ...config };
    this.residualDiag = this.createEmptyResidualDiagnostics();
    this.shortProbeDiag = this.createEmptyShortProbeDiagnostics();
  }

  private resolveShortProbeConfig(): {
    enabled: boolean;
    maxProbeSearchDepth: number;
    maxCandidatesPerFrontier: number;
    defenderBranchFactor: number;
    maxTotalProbeNodes: number;
  } {
    const raw: boolean | ShortTacticalProbeConfig | undefined =
      this.config.enableOrShortTacticalProbe;
    if (!raw) {
      return {
        enabled: false,
        maxProbeSearchDepth: 2,
        maxCandidatesPerFrontier: 5,
        defenderBranchFactor: 2,
        maxTotalProbeNodes: 180,
      };
    }
    const obj = typeof raw === 'object' ? raw : {};
    return {
      enabled: true,
      maxProbeSearchDepth: obj.maxProbeSearchDepth ?? 2,
      maxCandidatesPerFrontier: obj.maxCandidatesPerFrontier ?? 5,
      defenderBranchFactor: obj.defenderBranchFactor ?? 2,
      maxTotalProbeNodes: obj.maxTotalProbeNodes ?? 180,
    };
  }

  private createEmptyShortProbeDiagnostics(): ShortTacticalProbeDiagnostics {
    const cfg = this.resolveShortProbeConfig();
    return {
      enabled: cfg.enabled,
      maxProbeSearchDepth: cfg.maxProbeSearchDepth,
      maxCandidatesPerFrontier: cfg.maxCandidatesPerFrontier,
      defenderBranchFactor: cfg.defenderBranchFactor,
      maxTotalProbeNodes: cfg.maxTotalProbeNodes,
      probesTriggered: 0,
      candidatesProbed: 0,
      probeNodesUsed: 0,
      mainSearchNodesUsed: 0,
      probeTimeMs: 0,
      rankPromotions: 0,
      firstParentUsableSubproof: null,
    };
  }

  public getShortTacticalProbeDiagnostics(): ShortTacticalProbeDiagnostics {
    return {
      ...this.shortProbeDiag,
      mainSearchNodesUsed: Math.max(
        0,
        this.numNodes - this.shortProbeDiag.probeNodesUsed
      ),
      firstParentUsableSubproof: this.shortProbeDiag.firstParentUsableSubproof
        ? { ...this.shortProbeDiag.firstParentUsableSubproof }
        : null,
    };
  }

  private getResidualReplayMode(): ResidualSiblingReplayMode {
    if (
      !this.config.enableResidualSiblingReplay ||
      this.config.enableResidualSiblingReplay === 'off'
    ) {
      return 'off';
    }
    if (this.config.enableResidualSiblingReplay === true) {
      return 'grouped-1ply-filter';
    }
    return this.config.enableResidualSiblingReplay;
  }

  private createEmptyResidualDiagnostics(): ResidualReplayDiagnostics {
    return {
      mode: this.getResidualReplayMode(),
      sourcesRecorded: 0,
      prefilterSkips: 0,
      replayAttempts: 0,
      replaySuccesses: 0,
      replayFailures: 0,
      replayTimeMs: 0,
      divergenceClassifyTimeMs: 0,
      prefilterTimeMs: 0,
      replaySuccessTimeMs: 0,
      replayFailureTimeMs: 0,
      divergenceCounts: {
        WITNESS_OCCUPIED: 0,
        DESCENDANT_LEGAL_CHANGED: 0,
        LEAF_TERMINAL_FAILED: 0,
      },
      rootFirstSourceCallIndex: null,
      sourceClosureEvents: [],
    };
  }

  public getResidualReplayDiagnostics(): ResidualReplayDiagnostics {
    return {
      ...this.residualDiag,
      divergenceCounts: { ...this.residualDiag.divergenceCounts },
      sourceClosureEvents: this.residualDiag.sourceClosureEvents.map((ev) => ({
        ...ev,
        closedMovesSgf: ev.closedMovesSgf.slice(),
        failedMovesSgf: ev.failedMovesSgf.slice(),
        prefilterSkippedMovesSgf: ev.prefilterSkippedMovesSgf.slice(),
      })),
    };
  }

  private derivePathFromStateTable(stateId: number, boardSize: number): string {
    if (stateId <= 0 || stateId >= this.stateTable.length) return '';
    const movesSgf: string[] = [];
    let cur = stateId;
    let safety = 0;
    while (cur > 0 && cur < this.stateTable.length && safety < 256) {
      const st = this.stateTable[cur];
      if (!st || st.parentStateId < 0) break;
      movesSgf.push(coordToSgf(st.moveFromParent, boardSize));
      cur = st.parentStateId;
      safety++;
    }
    movesSgf.reverse();
    return movesSgf.join('/');
  }

  private static assertRegionHintConsistent(problem: TsumegoProblemSpec): void {
    if (
      problem.hasRegionHint !== undefined &&
      typeof problem.hasRegionHint !== 'boolean'
    ) {
      throw new Error(
        `LP-J02: Invalid non-boolean TsumegoProblemSpec.hasRegionHint=${String(
          problem.hasRegionHint
        )}.`
      );
    }
    if (problem.hasRegionHint === false && problem.regionCoords.length > 0) {
      throw new Error(
        `LP-J02: Contradictory TsumegoProblemSpec: hasRegionHint=false with non-empty regionCoords (length=${problem.regionCoords.length}).`
      );
    }
  }

  public solveProblem(problem: TsumegoProblemSpec): SolveReport {
    DfpnSolver.assertRegionHintConsistent(problem);
    const context = DfpnSolver.buildProofContext(problem, this.config);
    const initialPos = DfpnSolver.buildInitialPosition(problem, context);
    return this.solveFromPosition(problem, initialPos, context);
  }

  /**
   * Heuristic eye-like liberty potential of surviving crucial chains
   * (1:1 parity with C++ DfpnSolver<N>::EstimateParentEyeLikeCount).
   */
  public evaluateParentEyeLikeCount(
    pos: GoPosition,
    context: ProofContext
  ): number {
    return this.terminalEval.estimateHeuristicShapePotential(
      pos,
      context.initialTokens
    ).eyeLikeCount;
  }

  /**
   * Public diagnostic accessor for actual frontier PASS move tactical score.
   * Returns 0 when `enableFastCaptureOrdering` is false (matching frontier initialization).
   */
  public evaluatePassMoveScore(
    pos: GoPosition,
    context: ProofContext,
    isOrNode: boolean
  ): number {
    if (!this.config.enableFastCaptureOrdering) return 0;
    const parentEyeLikeCount =
      !isOrNode && pos.consecutivePasses === 0
        ? this.evaluateParentEyeLikeCount(pos, context)
        : 0;
    const emptyTacCtx = this.buildNodeTacticalContext(pos, context);
    return this.evaluateCandidateMove(
      pos,
      context,
      PASS_MOVE,
      isOrNode,
      parentEyeLikeCount,
      emptyTacCtx
    ).score;
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
    DfpnSolver.assertRegionHintConsistent(problem);
    const startTime = performance.now();
    this.ttStore.clearAll();
    this.nodeFrontierCache.clear();
    this.revalCache.clear();
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
    this.residualDiag = this.createEmptyResidualDiagnostics();
    this.shortProbeDiag = this.createEmptyShortProbeDiagnostics();

    this.activeAttentionMask =
      problem.attentionCoords && problem.attentionCoords.length > 0
        ? new NNAttentionMask(problem.attentionCoords)
        : null;

    const rootPos = initialPos.clone();
    const rootStateId = this.registerState(rootPos, -1, PASS_MOVE);
    const inPathHashes = new Set<string>();

    const hasRegionHint =
      problem.hasRegionHint !== undefined
        ? problem.hasRegionHint
        : problem.regionCoords.length > 0;
    const effectiveRegionMask: number[] | null = hasRegionHint
      ? problem.regionCoords
      : null;

    this.lastSolveContext = DfpnSolver.cloneProofContext(context);
    this.lastSolveRegionCoords = effectiveRegionMask
      ? [...effectiveRegionMask]
      : null;

    this.tracePathFilterSet =
      this.config.onPathTrace &&
      this.config.tracePathFilters &&
      this.config.tracePathFilters.length > 0
        ? new Set(this.config.tracePathFilters)
        : null;

    const rootResult = this.midSearch(
      rootPos,
      context,
      effectiveRegionMask,
      PN_DN_SATURATION,
      PN_DN_SATURATION,
      0,
      rootStateId,
      PASS_MOVE,
      inPathHashes,
      ''
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

    const runSource: 'original_root' | 'standalone_subposition' =
      initialPos.playedMoveTrace.length > 0
        ? 'standalone_subposition'
        : 'original_root';
    const branchCoverageSnapshots = this.buildBranchCoverageSnapshots(
      rootPos,
      context,
      rootStateId,
      rootResult,
      runSource
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
      hasRegionHint,
      regionCoords: hasRegionHint ? problem.regionCoords.slice() : [],
      rawRegionPointCount: hasRegionHint ? rawRegionCount : 0,
      isFullRegionSearch: !hasRegionHint || problem.regionCoords.length >= rawRegionCount,
      runContract: {
        boardSize: rootPos.boardSize,
        immortalWallCoords: Array.from(rootPos.immortalWallSet).sort(
          (a, b) => a - b
        ),
        hasRegionHint,
        regionCoords: hasRegionHint
          ? Array.from(new Set(problem.regionCoords)).sort((a, b) => a - b)
          : [],
        rootAttacker: context.rootAttacker,
        attackerGoal: context.attackerGoal,
        crucialStoneOp: context.crucialStoneOp,
        initialTokens: context.initialTokens.map((t) => ({ ...t })),
        koRule: context.koRule,
        attackerAllowKo: context.attackerAllowKo,
        defenderAllowKo: context.defenderAllowKo,
        rootKind:
          rootPos.playedMoveTrace.length > 0 ? 'traced_subposition' : 'initial',
        initialTraceMoves: rootPos.playedMoveTrace.slice(),
      },
      inputHash: rootPos.computeZobristHex(),
      configFingerprint: `${this.config.ttMode}:${this.config.koRule}:rz=${this.config.enableRzPruning}:ako=${context.attackerAllowKo}:dko=${context.defenderAllowKo}:reg=${hasRegionHint ? problem.regionCoords.length : 'all'}/${rawRegionCount}`,
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
      branchCoverageSnapshots,
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

  // Precompute all chain IDs, liberties, crucial-stone liberties, and cutting enemy chains ONCE per frontier node.
  private buildNodeTacticalContext(
    pos: GoPosition,
    context: ProofContext
  ): NodeTacticalContext {
    const gridLen = pos.grid.length;
    const chainIdAt = new Int32Array(gridLen).fill(-1);
    const maxChains = gridLen;
    const chainLibs = new Int32Array(maxChains);
    const chainMinStone = new Int32Array(maxChains);
    const chainIsImmortal = new Uint8Array(maxChains);
    const chainIsCuttingEnemy = new Uint8Array(maxChains);
    const crucialStoneMask = new Uint8Array(gridLen);
    const crucialLibMinLibs = new Int32Array(gridLen).fill(99);

    const q = new Int32Array(gridLen);
    const libStamp = new Int32Array(gridLen).fill(-1);
    const enemyColor = oppositeColor(pos.toPlay);
    let numChains = 0;

    for (let coord = 0; coord < gridLen; coord++) {
      const col = pos.grid[coord];
      if (col === Color.Empty || chainIdAt[coord] !== -1) continue;
      const cid = numChains++;
      chainIdAt[coord] = cid;
      q[0] = coord;
      let head = 0;
      let tail = 1;
      let minStone = coord;
      let immortal = pos.immortalWallSet.has(coord);
      let libs = 0;

      while (head < tail) {
        const cur = q[head++];
        if (cur < minStone) minStone = cur;
        const nbs = pos.orthogonalNeighbors(cur);
        for (let i = 0; i < nbs.length; i++) {
          const nb = nbs[i];
          const st = pos.grid[nb];
          if (st === col) {
            if (chainIdAt[nb] === -1) {
              chainIdAt[nb] = cid;
              if (!immortal && pos.immortalWallSet.has(nb)) immortal = true;
              q[tail++] = nb;
            }
          } else if (st === Color.Empty) {
            if (libStamp[nb] !== cid) {
              libStamp[nb] = cid;
              libs++;
            }
          }
        }
      }

      chainLibs[cid] = libs;
      chainMinStone[cid] = minStone;
      chainIsImmortal[cid] = immortal ? 1 : 0;
    }

    // Mark cutting enemy chains (non-immortal enemy chains with <= 3 liberties touching >= 2 friendly chains)
    const seenEnemyChain = new Uint8Array(numChains);
    for (let coord = 0; coord < gridLen; coord++) {
      if (pos.grid[coord] !== enemyColor) continue;
      const cid = chainIdAt[coord];
      if (
        cid < 0 ||
        seenEnemyChain[cid] ||
        chainIsImmortal[cid] ||
        chainLibs[cid] > 3
      ) {
        continue;
      }
      seenEnemyChain[cid] = 1;
      // Scan this enemy chain's orthogonal friendly neighbors
      let firstFriendlyCid = -1;
      let secondFriendlyFound = false;
      for (let p = coord; p < gridLen && !secondFriendlyFound; p++) {
        if (chainIdAt[p] !== cid) continue;
        const nbs = pos.orthogonalNeighbors(p);
        for (let i = 0; i < nbs.length; i++) {
          const nb = nbs[i];
          if (pos.grid[nb] === pos.toPlay) {
            const fcid = chainIdAt[nb];
            if (firstFriendlyCid === -1) {
              firstFriendlyCid = fcid;
            } else if (fcid !== firstFriendlyCid) {
              secondFriendlyFound = true;
              break;
            }
          }
        }
      }
      if (secondFriendlyFound) {
        chainIsCuttingEnemy[cid] = 1;
      }
    }

    // Mark surviving crucial target chains and their liberties
    const seenCrucialChains = new Set<number>();
    for (let idx = 0; idx < context.initialTokens.length; idx++) {
      if ((pos.survivingTargetTokensMask & (1 << idx)) === 0) continue;
      const tok = context.initialTokens[idx];
      const cid = chainIdAt[tok.initialCoord];
      if (cid < 0 || seenCrucialChains.has(cid)) continue;
      seenCrucialChains.add(cid);
      const libs = chainLibs[cid];
      for (let p = 0; p < gridLen; p++) {
        if (chainIdAt[p] !== cid) continue;
        crucialStoneMask[p] = 1;
        const nbs = pos.orthogonalNeighbors(p);
        for (let i = 0; i < nbs.length; i++) {
          const nb = nbs[i];
          if (pos.grid[nb] === Color.Empty && libs < crucialLibMinLibs[nb]) {
            crucialLibMinLibs[nb] = libs;
          }
        }
      }
    }

    const targetColor =
      context.initialTokens.length > 0
        ? context.initialTokens[0].stoneColor
        : context.attackerGoal === SearchGoal.ToLive
        ? context.rootAttacker
        : oppositeColor(context.rootAttacker);

    return {
      chainIdAt,
      chainLibs,
      chainMinStone,
      chainIsImmortal,
      chainIsCuttingEnemy,
      crucialStoneMask,
      crucialLibMinLibs,
      targetColor,
    };
  }

  // FR-4.10: Fast tactical move ordering & heuristic initial (pn, dn) estimation
  private evaluateCandidateMove(
    pos: GoPosition,
    context: ProofContext,
    move: number,
    isOrNode: boolean,
    parentEyeLikeCount: number,
    tacCtx: NodeTacticalContext
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
        const term = this.terminalEval.evaluateTerminal(probe, context, false);
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
      // At AND nodes (consecutivePasses === 0), place Null-Move (PASS) inside the initial
      // tactical window (right behind top immediate captures/vital refutations) so that once
      // the #1 defense does not immediately refute, PASS either seeds `activeNullMoveRz` to
      // prune 120+ outer-moat moves across the whole frontier or immediately refutes dead shapes.
      if (!isOrNode && pos.consecutivePasses === 0) {
        if (parentEyeLikeCount >= 2) {
          return {
            score: 3850,
            immediateWin: false,
            immediateLoss: false,
            inAttention: true,
          };
        }
        return {
          score: this.config.enableRzPruning ? 3450 : 360,
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

    const orthoNbs = pos.orthogonalNeighbors(move);
    let inAttention = this.activeAttentionMask
      ? this.activeAttentionMask.coords.has(move)
      : true;

    // Dynamic tactical attention: follow the live fight when crucial target chains extend
    // (or non-immortal chains drop to <= 3 liberties) beyond the static root bounding box.
    if (!inAttention && tacCtx.crucialLibMinLibs[move] < 99) {
      inAttention = true;
    }
    if (!inAttention) {
      for (let i = 0; i < orthoNbs.length; i++) {
        const nb = orthoNbs[i];
        if (pos.grid[nb] !== Color.Empty && !pos.immortalWallSet.has(nb)) {
          const cid = tacCtx.chainIdAt[nb];
          if (cid >= 0 && !tacCtx.chainIsImmortal[cid] && tacCtx.chainLibs[cid] <= 3) {
            inAttention = true;
            break;
          }
        }
      }
    }
    if (!inAttention) {
      const dNbs = pos.diagonalNeighbors(move);
      for (let i = 0; i < dNbs.length; i++) {
        if (tacCtx.crucialStoneMask[dNbs[i]]) {
          inAttention = true;
          break;
        }
      }
    }

    // Fast O(1) path for outer buffer-moat moves (`!inAttention`) that touch no tactical stones
    if (!inAttention) {
      let touchesTacticalStone = false;
      for (let i = 0; i < orthoNbs.length; i++) {
        const nb = orthoNbs[i];
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
    const enemyColor = oppositeColor(pos.toPlay);

    // 1. O(1) Precomputed proximity to crucial target chains and their liberties
    const r = Math.floor(move / pos.boardSize);
    const c = move % pos.boardSize;
    const distR = Math.min(r, pos.boardSize - 1 - r);
    const distC = Math.min(c, pos.boardSize - 1 - c);
    const distEdge = Math.min(distR, distC);

    const cLibs = tacCtx.crucialLibMinLibs[move];
    if (cLibs < 99) {
      if (cLibs === 1) score += 1750;
      else if (cLibs === 2) score += 1080;
      else if (cLibs <= 4 || distEdge <= 2) score += 480;
      else score += 220;
    }
    let adjCrucialCount = 0;
    for (let i = 0; i < orthoNbs.length; i++) {
      if (tacCtx.crucialStoneMask[orthoNbs[i]]) adjCrucialCount++;
    }
    if (adjCrucialCount >= 2) score += 580;

    // Pre-move neighbor chain inspection (O(1) via NodeTacticalContext — zero floodFill!)
    let tightenedLowLibEnemy = false;
    let tightenedCuttingEnemy = false;
    let minEnemyLibBefore = 99;
    let friendlyOrthoCount = 0;
    let enemyOrthoCount = 0;
    let hasTacticalFriendlyAdj = false;
    let firstFriendlyCid = -1;
    let connectsDistinctFriendly = false;
    let emptyOrthoCount = 0;
    let targetOrthoCount = 0;
    let oppTargetOrthoCount = 0;
    const oppTargetColor = oppositeColor(tacCtx.targetColor);

    for (let i = 0; i < orthoNbs.length; i++) {
      const nb = orthoNbs[i];
      const st = pos.grid[nb];
      if (st === Color.Empty) {
        emptyOrthoCount++;
      } else if (st === pos.toPlay) {
        friendlyOrthoCount++;
        const fcid = tacCtx.chainIdAt[nb];
        if (!tacCtx.chainIsImmortal[fcid]) {
          hasTacticalFriendlyAdj = true;
        }
        if (tacCtx.chainLibs[fcid] >= 2) {
          if (firstFriendlyCid === -1) firstFriendlyCid = fcid;
          else if (firstFriendlyCid !== fcid) connectsDistinctFriendly = true;
        }
      } else if (st === enemyColor) {
        enemyOrthoCount++;
        const ecid = tacCtx.chainIdAt[nb];
        if (!tacCtx.chainIsImmortal[ecid]) {
          const elibs = tacCtx.chainLibs[ecid];
          if (elibs < minEnemyLibBefore) minEnemyLibBefore = elibs;
          if (elibs <= 3) {
            tightenedLowLibEnemy = true;
            if (tacCtx.chainIsCuttingEnemy[ecid]) {
              tightenedCuttingEnemy = true;
            }
          }
        }
      }
      if (st === tacCtx.targetColor) targetOrthoCount++;
      else if (st === oppTargetColor) oppTargetOrthoCount++;
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
        score += 780;
      } else {
        const adjStone = orthoNbs.some((n) => probe.grid[n] !== Color.Empty);
        score += adjStone ? -240 : -780;
      }
    } else if (ourChain.liberties.size >= 3) {
      score += 240;
    }

    if (tightenedLowLibEnemy && ourChain.liberties.size >= 2) {
      score += tightenedCuttingEnemy ? 740 : 380;
    }

    if (enemyOrthoCount > 0) {
      for (let i = 0; i < orthoNbs.length; i++) {
        const nb = orthoNbs[i];
        if (probe.grid[nb] === enemyColor && !probe.immortalWallSet.has(nb)) {
          const enemyCh = probe.floodFillChain(nb);
          if (enemyCh.liberties.size === 1) {
            score += 740;
          } else if (
            enemyCh.liberties.size === 2 &&
            enemyCh.liberties.size < minEnemyLibBefore
          ) {
            score += 340;
          }
        }
      }
    }

    // 3. Corner / Edge & Symmetric Eye-Vitality Geometry Heuristics
    // ("My opponent's vital point is my vital point": evaluate eye-making/splitting for BOTH sides!)
    if (distR === 1 && distC === 1) {
      score += 560; // 2-2 vital corner point
    } else if (distEdge === 1) {
      score += 300; // 2nd-line base / eye-space point
    } else if (distEdge === 0) {
      score += 260; // 1st-line hane / descent / skirt point
    }

    if (connectsDistinctFriendly && hasTacticalFriendlyAdj) {
      score += 820;
    }

    const diagNbs = pos.diagonalNeighbors(move);
    let friendlyDiagCount = 0;
    let enemyDiagCount = 0;
    let targetDiagCount = 0;
    for (let i = 0; i < diagNbs.length; i++) {
      const st = pos.grid[diagNbs[i]];
      if (st === pos.toPlay) friendlyDiagCount++;
      else if (st === enemyColor) enemyDiagCount++;
      if (st === tacCtx.targetColor) targetDiagCount++;
    }

    let splitsEyeCavity = false;
    if (emptyOrthoCount >= 2 && inAttention) {
      // Check if two empty orthogonal neighbors are separated (vital eye-splitting / nakade point!)
      for (let i = 0; i < orthoNbs.length && !splitsEyeCavity; i++) {
        const a = orthoNbs[i];
        if (pos.grid[a] !== Color.Empty) continue;
        const aNbs = pos.orthogonalNeighbors(a);
        for (let j = i + 1; j < orthoNbs.length; j++) {
          const b = orthoNbs[j];
          if (pos.grid[b] !== Color.Empty) continue;
          const bNbs = pos.orthogonalNeighbors(b);
          let sharedEmpty = false;
          for (let x = 0; x < aNbs.length; x++) {
            const cand = aNbs[x];
            if (
              cand !== move &&
              pos.grid[cand] === Color.Empty &&
              bNbs.includes(cand)
            ) {
              sharedEmpty = true;
              break;
            }
          }
          if (!sharedEmpty) {
            splitsEyeCavity = true;
            break;
          }
        }
      }
      if (
        splitsEyeCavity &&
        (friendlyOrthoCount >= 1 ||
          enemyOrthoCount >= 1 ||
          friendlyDiagCount >= 2 ||
          enemyDiagCount >= 2)
      ) {
        score += 960;
      }
    }

    // Calm eye-making / eye-destroying vital point along target group's 1st/2nd-line cavity
    if (
      inAttention &&
      ourChain.liberties.size >= 2 &&
      distEdge <= 1 &&
      (targetDiagCount >= 1 || targetOrthoCount >= 1)
    ) {
      // Counts empty neighbors that become enclosed pockets around the target group
      let enclosedEdgePockets = 0;
      for (let i = 0; i < orthoNbs.length; i++) {
        const enb = orthoNbs[i];
        if (pos.grid[enb] !== Color.Empty) continue;
        const enbNbs = pos.orthogonalNeighbors(enb);
        let targetWalls = 0;
        for (let j = 0; j < enbNbs.length; j++) {
          const nn = enbNbs[j];
          if (nn === move || pos.grid[nn] === tacCtx.targetColor) {
            targetWalls++;
          }
        }
        if (targetWalls >= enbNbs.length - 1) {
          enclosedEdgePockets++;
        }
      }
      if (enclosedEdgePockets >= 1) {
        score += 480 + (enclosedEdgePockets >= 2 ? 360 : 0);
      } else if (distEdge === 0 && emptyOrthoCount >= 1 && (targetOrthoCount >= 1 || oppTargetOrthoCount >= 1)) {
        // 1st-line descent / hane extending or blocking eye base
        score += 340;
      }
    }

    if (
      friendlyDiagCount >= 2 &&
      enemyOrthoCount === 0 &&
      (friendlyOrthoCount === 0 ||
        connectsDistinctFriendly ||
        enemyDiagCount >= 1)
    ) {
      score += 520;
      for (let i = 0; i < orthoNbs.length; i++) {
        const enb = orthoNbs[i];
        if (pos.grid[enb] === Color.Empty) {
          const enbNbs = pos.orthogonalNeighbors(enb);
          let enbFriendlyWalls = 0;
          for (let j = 0; j < enbNbs.length; j++) {
            const n = enbNbs[j];
            if (n === move || pos.grid[n] === pos.toPlay) enbFriendlyWalls++;
          }
          if (enbFriendlyWalls >= 3) {
            score += 620;
          }
        }
      }
    } else if (
      enemyDiagCount >= 2 &&
      friendlyOrthoCount === 0 &&
      ourChain.liberties.size >= 2 &&
      inAttention
    ) {
      // Symmetric opponent eye-vitality point (nakade / eye-stealing placement!)
      score += 560;
    } else if (
      emptyOrthoCount <= 1 &&
      friendlyOrthoCount >= 1 &&
      !connectsDistinctFriendly &&
      friendlyDiagCount >= 2 &&
      enemyOrthoCount === 0 &&
      enemyDiagCount === 0
    ) {
      // Pure 1- or 2-point internal eye space under a single solid chain — avoid self-filling eye!
      score -= 340;
    }

    if (friendlyOrthoCount >= 1 && enemyOrthoCount >= 1) {
      score += 340;
    }
    if (friendlyOrthoCount >= 1 && enemyDiagCount >= 1) {
      score += 290;
    }

    // 4. Exact post-move single-point true-eye count & immediate Benson UCA detection.
    // Checking `evaluateTerminal` on the few high-potential in-attention OR-node moves
    // lets 1-move Benson lives jump directly to rank #0 (`pn=1, dn=10`), closing null-move
    // proofs in 1 node instead of grinding through tied-score alternatives.
    let postTrueEyes = 0;
    if (inAttention && ourChain.liberties.size >= 2) {
      for (let i = 0; i < orthoNbs.length; i++) {
        const ep = orthoNbs[i];
        if (probe.grid[ep] !== Color.Empty) continue;
        const epOrtho = probe.orthogonalNeighbors(ep);
        let allTarget = true;
        for (let j = 0; j < epOrtho.length; j++) {
          if (probe.grid[epOrtho[j]] !== tacCtx.targetColor) {
            allTarget = false;
            break;
          }
        }
        if (allTarget) {
          const epDiag = probe.diagonalNeighbors(ep);
          let enemyDiags = 0;
          for (let j = 0; j < epDiag.length; j++) {
            if (probe.grid[epDiag[j]] === oppTargetColor) enemyDiags++;
          }
          const maxEnemyDiags = epDiag.length === 4 ? 1 : 0;
          if (enemyDiags <= maxEnemyDiags) {
            postTrueEyes++;
          }
        }
      }
      if (postTrueEyes > 0) {
        score += postTrueEyes * 680;
      }

      // 4b. Crucial-chain liberty-delta heuristic (O(1), zero extra flood-fill):
      // Extending a living/escaping crucial chain outward to expand liberties & eye space
      // outranks cramping into an enemy wall and shrinking liberties without making an eye.
      if (cLibs < 99 && pos.toPlay === tacCtx.targetColor) {
        const libDelta = ourChain.liberties.size - cLibs;
        if (libDelta >= 2) {
          score += 560;
        } else if (libDelta === 1) {
          score += 260;
        } else if (
          libDelta < 0 &&
          res.capturedCoords.length === 0 &&
          postTrueEyes === 0 &&
          !splitsEyeCavity &&
          !connectsDistinctFriendly
        ) {
          score -= 220;
        }
      }

      if (
        isOrNode &&
        context.attackerGoal === SearchGoal.ToLive &&
        (postTrueEyes > 0 ||
          res.capturedCoords.length > 0 ||
          score >= 2200)
      ) {
        const term = this.terminalEval.evaluateTerminal(probe, context, false);
        if (term.status === TerminalStatus.Win) {
          return {
            score: 58000,
            immediateWin: true,
            immediateLoss: false,
            inAttention: true,
          };
        }
      }
    }

    return {
      score,
      immediateWin: false,
      immediateLoss: false,
      inAttention,
    };
  }

  // Assign heuristic initial (pn_0, dn_0) with gentle rank separation so winning moves at
  // rank #2..#4 are reached quickly while eps (+4, 1.5x) still prevents depth-2..4 bounce.
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
      else if (rankIdx === 1) pn = 4;
      else if (rankIdx === 2) pn = 8;
      else if (rankIdx <= 5) pn = 12 + (rankIdx - 3) * 4;
      else if (rankIdx <= 10) pn = 24 + (rankIdx - 5) * 5;
      else pn = 50 + (rankIdx - 10) * 6;
      if (meta.score < 0) pn += 24;
      return { pn, dn: 1 };
    } else {
      // AND node: `dn` drives selection of defender refutations; `pn` aggregates proof obligation
      if (meta.immediateLoss) return { pn: 10, dn: 1 };
      if (move === PASS_MOVE) {
        if (rankIdx === 0) return { pn: 1, dn: 1 };
        return meta.score >= 3400 ? { pn: 1, dn: 3 } : { pn: 1, dn: 5 };
      }
      if (!meta.inAttention) {
        return { pn: 1, dn: 96 + rankIdx * 4 };
      }
      let dn = 1;
      if (rankIdx === 0) dn = 1;
      else if (rankIdx === 1) dn = 4;
      else if (rankIdx === 2) dn = 8;
      else if (rankIdx <= 5) dn = 12 + (rankIdx - 3) * 4;
      else if (rankIdx <= 10) dn = 24 + (rankIdx - 5) * 5;
      else dn = 50 + (rankIdx - 10) * 6;
      if (meta.score < 0) dn += 16;
      return { pn: 1, dn };
    }
  }

  // FR-5.5: Memoized revalidation of source proof subgraph under QueryState + HistorySet
  private revalidateSourceProofOnQueryState(
    queryPos: GoPosition,
    context: ProofContext,
    regionCoords: number[] | null,
    sourceDagNodeId: number,
    expectedOutcome: ProofOutcome,
    guardDepth = 0,
    mutateCache = true,
    revalCacheOverride?: Map<string, boolean>
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

    const resolvedId = sourceNode.nodeId;
    const histTag = queryPos.isCaptureFreeMonotonicHistory()
      ? 'M'
      : queryPos.computeCanonicalHistoryKey();
    const cacheKey = `${queryPos.computeZobristHex()}:${queryPos.toPlay}:${
      queryPos.koPoint
    }:${queryPos.consecutivePasses}:${
      queryPos.survivingTargetTokensMask
    }:${histTag}:${resolvedId}:${expectedOutcome}`;
    const cache = revalCacheOverride ?? this.revalCache;
    const cached = cache.get(cacheKey);
    if (cached !== undefined) {
      return cached;
    }

    const finish = (ok: boolean): boolean => {
      if (mutateCache && (ok || guardDepth <= 40)) {
        cache.set(cacheKey, ok);
      }
      return ok;
    };

    const checkEarlyTerminal = (): boolean => {
      const term = this.terminalEval.evaluateTerminal(queryPos, context, false);
      if (term.status === TerminalStatus.Win) {
        return expectedOutcome === ProofOutcome.ProvenWin;
      }
      if (term.status === TerminalStatus.Loss) {
        return expectedOutcome === ProofOutcome.ProvenLoss;
      }
      return false;
    };

    if (sourceNode.childNodeIds.length === 0 || queryPos.isAtDoublePass()) {
      return finish(checkEarlyTerminal());
    }

    const isOr = queryPos.toPlay === context.rootAttacker;
    const restrictedSide =
      (queryPos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
      (queryPos.toPlay !== context.rootAttacker && !context.defenderAllowKo);

    const allowedRegion =
      regionCoords !== null ? new Set<number>(regionCoords) : null;

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
            guardDepth + 1,
            mutateCache,
            revalCacheOverride
          )
        ) {
          return finish(true);
        }
      }
      return finish(checkEarlyTerminal());
    }

    // Case 2: Full-coverage node (AND -> ProvenWin, or OR -> ProvenLoss)
    // Every legal move on `queryPos` MUST be covered in `sourceNode` and recursively hold!
    const moveMap = new Map<number, number>();
    for (let i = 0; i < sourceNode.childMoves.length; i++) {
      moveMap.set(sourceNode.childMoves[i], sourceNode.childNodeIds[i]);
    }

    const queryLegalMoves = queryPos.generateLegalMoves(regionCoords);
    for (let i = 0; i < queryLegalMoves.length; i++) {
      const mv = queryLegalMoves[i];
      const childDagId = moveMap.get(mv);
      if (childDagId === undefined) {
        return finish(checkEarlyTerminal());
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
          guardDepth + 1,
          mutateCache,
          revalCacheOverride
        )
      ) {
        return finish(checkEarlyTerminal());
      }
    }

    return finish(true);
  }

  private diagnoseFirstDivergence(
    queryPos: GoPosition,
    context: ProofContext,
    regionCoords: number[] | null,
    sourceDagNodeId: number,
    expectedOutcome: ProofOutcome,
    guardDepth = 0
  ): ResidualDivergenceKind | null {
    if (
      guardDepth > 48 ||
      sourceDagNodeId < 0 ||
      sourceDagNodeId >= this.proofDagNodes.length
    ) {
      return 'LEAF_TERMINAL_FAILED';
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
    if (!sourceNode || sourceNode.outcome !== expectedOutcome) {
      return 'LEAF_TERMINAL_FAILED';
    }

    if (sourceNode.childNodeIds.length === 0 || queryPos.isAtDoublePass()) {
      const term = this.terminalEval.evaluateTerminal(queryPos, context, false);
      const ok =
        (term.status === TerminalStatus.Win &&
          expectedOutcome === ProofOutcome.ProvenWin) ||
        (term.status === TerminalStatus.Loss &&
          expectedOutcome === ProofOutcome.ProvenLoss);
      return ok ? null : 'LEAF_TERMINAL_FAILED';
    }

    const isOr = queryPos.toPlay === context.rootAttacker;
    const restrictedSide =
      (queryPos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
      (queryPos.toPlay !== context.rootAttacker && !context.defenderAllowKo);

    const allowedRegion =
      regionCoords !== null ? new Set<number>(regionCoords) : null;

    if (
      (isOr && expectedOutcome === ProofOutcome.ProvenWin) ||
      (!isOr && expectedOutcome === ProofOutcome.ProvenLoss)
    ) {
      let fallbackDiv: ResidualDivergenceKind | null = null;
      for (let i = 0; i < sourceNode.childNodeIds.length; i++) {
        const mv = sourceNode.childMoves[i];
        if (mv !== PASS_MOVE && allowedRegion !== null && !allowedRegion.has(mv)) {
          continue;
        }
        const chNode = this.proofDagNodes[sourceNode.childNodeIds[i]];
        if (!chNode || chNode.outcome !== expectedOutcome) continue;
        const nextPos = queryPos.clone();
        const playRes = nextPos.playMove(mv);
        if (!playRes.legal || (playRes.isKoCapture && restrictedSide)) {
          if (!fallbackDiv) fallbackDiv = 'WITNESS_OCCUPIED';
          continue;
        }
        const sub = this.diagnoseFirstDivergence(
          nextPos,
          context,
          regionCoords,
          sourceNode.childNodeIds[i],
          expectedOutcome,
          guardDepth + 1
        );
        if (sub === null) return null;
        if (!fallbackDiv) fallbackDiv = sub;
      }
      return fallbackDiv ?? 'WITNESS_OCCUPIED';
    }

    const moveMap = new Map<number, number>();
    for (let i = 0; i < sourceNode.childMoves.length; i++) {
      moveMap.set(sourceNode.childMoves[i], sourceNode.childNodeIds[i]);
    }

    const queryLegalMoves = queryPos.generateLegalMoves(regionCoords);
    for (let i = 0; i < queryLegalMoves.length; i++) {
      if (!moveMap.has(queryLegalMoves[i])) {
        return 'DESCENDANT_LEGAL_CHANGED';
      }
    }

    queryLegalMoves.sort((a, b) => {
      const ca = moveMap.get(a)!;
      const cb = moveMap.get(b)!;
      const pa =
        a === PASS_MOVE ? 0 : !this.proofDagNodes[ca]?.isPrunedOutsideRz ? 1 : 2;
      const pb =
        b === PASS_MOVE ? 0 : !this.proofDagNodes[cb]?.isPrunedOutsideRz ? 1 : 2;
      return pa - pb;
    });

    for (let i = 0; i < queryLegalMoves.length; i++) {
      const mv = queryLegalMoves[i];
      const childDagId = moveMap.get(mv)!;
      const nextPos = queryPos.clone();
      const playRes = nextPos.playMove(mv);
      if (!playRes.legal) continue;
      const sub = this.diagnoseFirstDivergence(
        nextPos,
        context,
        regionCoords,
        childDagId,
        expectedOutcome,
        guardDepth + 1
      );
      if (sub !== null) return sub;
    }

    return null;
  }

  private unwrapSourceDagNode(dagNodeId: number): ProofDagNode | undefined {
    let node = this.proofDagNodes[dagNodeId];
    let unwrapSafety = 0;
    while (
      node &&
      (node.isPrunedOutsideRz || node.isTtHit) &&
      node.sourceProofNodeId !== null &&
      node.sourceProofNodeId >= 0 &&
      node.sourceProofNodeId < node.nodeId &&
      unwrapSafety < 32
    ) {
      unwrapSafety++;
      node = this.proofDagNodes[node.sourceProofNodeId];
    }
    return node;
  }

  /**
   * Side-effect-free assessment of whether `src`'s existing proof DAG can close
   * `sibPos` after `sibMove`. Never mutates `stateTable`, `historyTable`,
   * `proofDagNodes`, `dagHasCapture`, or `residualDiag`.
   */
  private assessSiblingReplayCandidate(
    sibMove: number,
    sibPos: GoPosition,
    src: { move: number; dagId: number; rz: ProofCertificateRZ },
    mode: ResidualSiblingReplayMode,
    context: ProofContext,
    regionCoords: number[] | null,
    triedSourceDagIds?: ReadonlySet<number>,
    mutateCache = true,
    revalCacheOverride?: Map<string, boolean>
  ): {
    status: 'closed' | 'failed' | 'prefilter_skip' | 'already_tried';
    prefilterDtMs: number;
    replayDtMs: number;
  } {
    if (triedSourceDagIds?.has(src.dagId)) {
      return {
        status: 'already_tried',
        prefilterDtMs: 0,
        replayDtMs: 0,
      };
    }

    const tPre0 = performance.now();
    const srcRoot = this.unwrapSourceDagNode(src.dagId);
    const winIndices: number[] = [];
    if (srcRoot) {
      for (let i = 0; i < srcRoot.childNodeIds.length; i++) {
        if (this.proofDagNodes[srcRoot.childNodeIds[i]]?.outcome === ProofOutcome.ProvenWin) {
          winIndices.push(i);
        }
      }
    }
    const singleWinIdx = winIndices.length === 1 ? winIndices[0] : -1;
    const w0 = singleWinIdx >= 0 && srcRoot ? srcRoot.childMoves[singleWinIdx] : -999;
    const c0 =
      singleWinIdx >= 0 && srcRoot
        ? this.unwrapSourceDagNode(srcRoot.childNodeIds[singleWinIdx])
        : undefined;

    if (sibMove !== PASS_MOVE && sibMove === w0) {
      return {
        status: 'already_tried',
        prefilterDtMs: performance.now() - tPre0,
        replayDtMs: 0,
      };
    }

    if (
      mode === 'grouped-1ply-filter' &&
      src.move !== PASS_MOVE &&
      !sibPos.isAtDoublePass() &&
      w0 >= 0 &&
      c0 &&
      c0.childNodeIds.length > 0 &&
      !c0.childMoves.includes(src.move)
    ) {
      const afterW0 = sibPos.clone();
      const w0Play = afterW0.playMove(w0);
      const w0InRegion =
        w0 === PASS_MOVE || regionCoords === null || regionCoords.includes(w0);
      const restrictedAttacker =
        (sibPos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
        (sibPos.toPlay !== context.rootAttacker && !context.defenderAllowKo);
      const w0Legal = w0InRegion && w0Play.legal && !(w0Play.isKoCapture && restrictedAttacker);
      const isSibEarlyWin = (): boolean =>
        this.terminalEval.evaluateTerminal(sibPos, context, false).status === TerminalStatus.Win;

      if (!w0Legal) {
        if (!isSibEarlyWin()) {
          return {
            status: 'prefilter_skip',
            prefilterDtMs: performance.now() - tPre0,
            replayDtMs: 0,
          };
        }
      } else if (!afterW0.isAtDoublePass() && afterW0.clone().playMove(src.move).legal) {
        const afterW0EarlyWin =
          this.terminalEval.evaluateTerminal(afterW0, context, false).status ===
          TerminalStatus.Win;
        if (!afterW0EarlyWin && !isSibEarlyWin()) {
          return {
            status: 'prefilter_skip',
            prefilterDtMs: performance.now() - tPre0,
            replayDtMs: 0,
          };
        }
      }
    }

    const prefilterDtMs = performance.now() - tPre0;
    const t0 = performance.now();
    const ok = this.revalidateSourceProofOnQueryState(
      sibPos,
      context,
      regionCoords,
      src.dagId,
      ProofOutcome.ProvenWin,
      0,
      mutateCache,
      revalCacheOverride
    );
    const replayDtMs = performance.now() - t0;

    return {
      status: ok ? 'closed' : 'failed',
      prefilterDtMs,
      replayDtMs,
    };
  }

  private tryReplaySourceOnSiblingSlot(
    sib: SearchChildSlot,
    sibPos: GoPosition,
    hasCaptureOnSibMove: boolean,
    parentPos: GoPosition,
    currentStateId: number,
    isOrNode: boolean,
    src: { move: number; dagId: number; rz: ProofCertificateRZ },
    mode: ResidualSiblingReplayMode,
    context: ProofContext,
    regionCoords: number[] | null
  ): 'closed' | 'failed' | 'prefilter_skip' | 'already_tried' {
    if (!sib.triedSourceDagIds) sib.triedSourceDagIds = new Set<number>();
    if (sib.triedSourceDagIds.has(src.dagId)) return 'already_tried';
    const assessment = this.assessSiblingReplayCandidate(
      sib.move,
      sibPos,
      src,
      mode,
      context,
      regionCoords,
      sib.triedSourceDagIds,
      true
    );
    sib.triedSourceDagIds.add(src.dagId);

    this.residualDiag.prefilterTimeMs += assessment.prefilterDtMs;
    this.residualDiag.replayTimeMs += assessment.prefilterDtMs;

    if (assessment.status === 'already_tried') {
      return 'already_tried';
    }
    if (assessment.status === 'prefilter_skip') {
      this.residualDiag.prefilterSkips++;
      return 'prefilter_skip';
    }

    this.residualDiag.replayTimeMs += assessment.replayDtMs;
    this.residualDiag.replayAttempts++;

    if (assessment.status === 'failed') {
      this.residualDiag.replayFailureTimeMs += assessment.replayDtMs;
      this.residualDiag.replayFailures++;
      return 'failed';
    }

    this.residualDiag.replaySuccessTimeMs += assessment.replayDtMs;
    this.residualDiag.replaySuccesses++;
    const qSid =
      sib.stateId >= 0
        ? sib.stateId
        : this.registerState(sibPos, currentStateId, sib.move);
    sib.stateId = qSid;
    sib.hasCapture = hasCaptureOnSibMove;
    const qStEntry = this.stateTable[qSid];
    const ttNodeId = this.proofDagNodes.length;
    this.proofDagNodes.push({
      nodeId: ttNodeId,
      stateId: qSid,
      historyId: qStEntry.historyId,
      parentStateId: currentStateId,
      isOrNode: !isOrNode,
      toPlay: sibPos.toPlay,
      incomingMove: sib.move,
      incomingMoveSgf: coordToSgf(sib.move, parentPos.boardSize),
      pn: 0,
      dn: PN_DN_SATURATION,
      outcome: ProofOutcome.ProvenWin,
      terminalEvidence: 'TT_REVALIDATED_REUSE',
      isPrunedOutsideRz: false,
      isTtHit: true,
      isKoDependentBarrier: false,
      sourceProofNodeId: src.dagId,
      proofRzCoords: src.rz.toArray(),
      disproofRzCoords: src.rz.toArray(),
      childNodeIds: [],
      childMoves: [],
    });
    this.dagHasCapture.push(
      sib.hasCapture || Boolean(this.dagHasCapture[src.dagId])
    );

    sib.expanded = true;
    sib.outcome = ProofOutcome.ProvenWin;
    sib.pn = 0;
    sib.dn = PN_DN_SATURATION;
    sib.proofRz = src.rz;
    sib.disproofRz = src.rz;
    sib.dagNodeId = ttNodeId;
    sib.lastExitReason = 'sibling_tt_replay';
    return 'closed';
  }

  private static cloneProofContext(ctx: ProofContext): ProofContext {
    return {
      contextId: ctx.contextId,
      rootAttacker: ctx.rootAttacker,
      attackerGoal: ctx.attackerGoal,
      crucialStoneOp: ctx.crucialStoneOp,
      koRule: ctx.koRule,
      attackerAllowKo: ctx.attackerAllowKo,
      defenderAllowKo: ctx.defenderAllowKo,
      initialTokens: ctx.initialTokens.map((t) => ({
        tokenId: t.tokenId,
        initialCoord: t.initialCoord,
        groupIndex: t.groupIndex,
        stoneColor: t.stoneColor,
      })),
    };
  }

  private static sameProofContext(a: ProofContext, b: ProofContext): boolean {
    if (
      a.contextId !== b.contextId ||
      a.rootAttacker !== b.rootAttacker ||
      a.attackerGoal !== b.attackerGoal ||
      a.crucialStoneOp !== b.crucialStoneOp ||
      a.koRule !== b.koRule ||
      a.attackerAllowKo !== b.attackerAllowKo ||
      a.defenderAllowKo !== b.defenderAllowKo ||
      a.initialTokens.length !== b.initialTokens.length
    ) {
      return false;
    }
    for (let i = 0; i < a.initialTokens.length; i++) {
      const ta = a.initialTokens[i];
      const tb = b.initialTokens[i];
      if (
        ta.tokenId !== tb.tokenId ||
        ta.initialCoord !== tb.initialCoord ||
        ta.groupIndex !== tb.groupIndex ||
        ta.stoneColor !== tb.stoneColor
      ) {
        return false;
      }
    }
    return true;
  }

  private static sameRegionCoords(
    a: number[] | null,
    b: number[] | null
  ): boolean {
    if (a === null || b === null) return a === b;
    const setA = new Set<number>(a);
    const setB = new Set<number>(b);
    if (setA.size !== setB.size) return false;
    for (const c of setA) {
      if (!setB.has(c)) return false;
    }
    return true;
  }

  /**
   * Read-only diagnostic entry to evaluate whether `src` can replay on `queryMove`
   * against a source DAG already stored on this solver instance without mutating
   * `stateTable`, `historyTable`, `proofDagNodes`, `dagHasCapture`, `revalCache`, or `residualDiag`.
   *
   * Binds to the `ProofContext` and `regionCoords` that produced the stored DAG by default
   * (`regionPolicy = 'bound'`) and always evaluates inside an isolated temporary cache so
   * warm and cold instances cannot leak stale cross-region entries.
   */
  public evaluateSiblingReplayCandidate(params: {
    parentPos: GoPosition;
    sourceMove: number;
    sourceDagId: number;
    sourceRz: ProofCertificateRZ;
    queryMove: number;
    mode: ResidualSiblingReplayMode;
    context: ProofContext;
    regionCoords: number[] | null;
    regionPolicy?: 'bound' | 'counterfactual';
  }): 'closed' | 'failed' | 'prefilter_skip' | 'already_tried' {
    if (
      params.queryMove !== PASS_MOVE &&
      params.regionCoords !== null &&
      !params.regionCoords.includes(params.queryMove)
    ) {
      return 'failed';
    }
    if (!DfpnSolver.sameProofContext(params.parentPos.context, params.context)) {
      return 'failed';
    }
    if (
      this.lastSolveContext !== null &&
      (!DfpnSolver.sameProofContext(params.context, this.lastSolveContext) ||
        !DfpnSolver.sameProofContext(params.parentPos.context, this.lastSolveContext))
    ) {
      return 'failed';
    }
    const policy = params.regionPolicy ?? 'bound';
    if (
      policy === 'bound' &&
      this.lastSolveContext !== null &&
      !DfpnSolver.sameRegionCoords(params.regionCoords, this.lastSolveRegionCoords)
    ) {
      return 'failed';
    }

    const qPos = params.parentPos.clone();
    const qPlay = qPos.playMove(params.queryMove);
    const restrictedSide =
      (params.parentPos.toPlay === params.context.rootAttacker &&
        !params.context.attackerAllowKo) ||
      (params.parentPos.toPlay !== params.context.rootAttacker &&
        !params.context.defenderAllowKo);
    if (!qPlay.legal || (qPlay.isKoCapture && restrictedSide)) {
      return 'failed';
    }

    const isolatedRevalCache = new Map<string, boolean>();
    return this.assessSiblingReplayCandidate(
      params.queryMove,
      qPos,
      { move: params.sourceMove, dagId: params.sourceDagId, rz: params.sourceRz },
      params.mode,
      params.context,
      params.regionCoords,
      undefined,
      true,
      isolatedRevalCache
    ).status;
  }

  private hasInteriorEmptyTriangle(
    pos: GoPosition,
    move: number,
    color: Color
  ): boolean {
    const bs = pos.boardSize;
    const r = Math.floor(move / bs);
    const c = move % bs;
    for (let dr = -1; dr <= 0; dr++) {
      for (let dc = -1; dc <= 0; dc++) {
        if (r + dr < 0 || r + dr + 1 >= bs || c + dc < 0 || c + dc + 1 >= bs) {
          continue;
        }
        const pts = [
          (r + dr) * bs + (c + dc),
          (r + dr) * bs + (c + dc + 1),
          (r + dr + 1) * bs + (c + dc),
          (r + dr + 1) * bs + (c + dc + 1),
        ];
        let friendly = 0;
        let emptyCoord = -1;
        let emptyCount = 0;
        for (let i = 0; i < 4; i++) {
          const st = pos.grid[pts[i]];
          if (st === color) friendly++;
          else if (st === Color.Empty) {
            emptyCount++;
            emptyCoord = pts[i];
          }
        }
        if (friendly === 3 && emptyCount === 1 && emptyCoord >= 0) {
          const oNbs = pos.orthogonalNeighbors(emptyCoord);
          if (oNbs.length === 4) {
            let fWalls = 0;
            for (let k = 0; k < 4; k++) {
              if (pos.grid[oNbs[k]] === color) fWalls++;
            }
            if (fWalls === 2) return true;
          }
        }
      }
    }
    return false;
  }

  private evaluateGroupBaseAndEyeSectors(
    pos: GoPosition,
    context: ProofContext,
    targetColor: Color
  ): {
    crucialAlive: boolean;
    minCrucialLibs: number;
    enclosedCount: number;
    tigerCount: number;
    distinctSectors: number;
    edgeBaseSpan: number;
  } {
    let crucialAlive = true;
    let minCrucialLibs = 99;
    const seen = new Set<number>();
    for (let idx = 0; idx < context.initialTokens.length; idx++) {
      if ((pos.survivingTargetTokensMask & (1 << idx)) === 0) {
        if (context.crucialStoneOp === LogicalOp.Conjunction) crucialAlive = false;
        continue;
      }
      const coord = context.initialTokens[idx].initialCoord;
      if (seen.has(coord) || pos.grid[coord] !== targetColor) continue;
      const ch = pos.floodFillChain(coord);
      for (const s of ch.stones) seen.add(s);
      if (ch.liberties.size < minCrucialLibs) minCrucialLibs = ch.liberties.size;
    }
    if (context.crucialStoneOp !== LogicalOp.Conjunction) {
      crucialAlive = pos.survivingTargetTokensMask !== 0;
    }
    if (!crucialAlive) {
      return {
        crucialAlive: false,
        minCrucialLibs: 0,
        enclosedCount: 0,
        tigerCount: 0,
        distinctSectors: 0,
        edgeBaseSpan: 0,
      };
    }

    const bs = pos.boardSize;
    const oppColor = oppositeColor(targetColor);
    let enclosedCount = 0;
    let tigerCount = 0;
    const pocketCoords: number[] = [];
    let minR = bs;
    let maxR = -1;
    let minC = bs;
    let maxC = -1;
    for (let p = 0; p < bs * bs; p++) {
      if (pos.grid[p] === targetColor && !pos.immortalWallSet.has(p)) {
        const pr = Math.floor(p / bs);
        const pc = p % bs;
        if (Math.min(Math.min(pr, bs - 1 - pr), Math.min(pc, bs - 1 - pc)) <= 2) {
          if (pr < minR) minR = pr;
          if (pr > maxR) maxR = pr;
          if (pc < minC) minC = pc;
          if (pc > maxC) maxC = pc;
        }
        continue;
      }
      if (pos.grid[p] !== Color.Empty || pos.immortalWallSet.has(p)) continue;
      const oNbs = pos.orthogonalNeighbors(p);
      let fO = 0;
      let eO = 0;
      let tacF = 0;
      for (let k = 0; k < oNbs.length; k++) {
        const nb = oNbs[k];
        if (pos.grid[nb] === targetColor) {
          fO++;
          if (!pos.immortalWallSet.has(nb)) tacF++;
        } else if (pos.grid[nb] === oppColor) {
          eO++;
        }
      }
      if (tacF === 0 || eO > 0) continue;
      if (fO >= oNbs.length - 1) {
        enclosedCount++;
        pocketCoords.push(p);
      } else if (fO >= 2) {
        tigerCount++;
        pocketCoords.push(p);
      }
    }
    let distinctSectors = 0;
    const used = new Uint8Array(pocketCoords.length);
    for (let i = 0; i < pocketCoords.length; i++) {
      if (used[i]) continue;
      distinctSectors++;
      used[i] = 1;
      const q = [pocketCoords[i]];
      while (q.length > 0) {
        const cur = q.pop()!;
        const cr = Math.floor(cur / bs);
        const cc = cur % bs;
        for (let j = 0; j < pocketCoords.length; j++) {
          if (used[j]) continue;
          const jr = Math.floor(pocketCoords[j] / bs);
          const jc = pocketCoords[j] % bs;
          if (Math.abs(cr - jr) + Math.abs(cc - jc) <= 2) {
            used[j] = 1;
            q.push(pocketCoords[j]);
          }
        }
      }
    }
    return {
      crucialAlive,
      minCrucialLibs,
      enclosedCount,
      tigerCount,
      distinctSectors,
      edgeBaseSpan: maxR >= minR ? maxR - minR + (maxC - minC) : 0,
    };
  }

  private runShortTacticalProbeOnOrFrontier(
    pos: GoPosition,
    context: ProofContext,
    regionCoords: number[] | null,
    tacCtx: NodeTacticalContext,
    scored: Array<{
      mv: number;
      meta: {
        score: number;
        immediateWin: boolean;
        immediateLoss: boolean;
        inAttention: boolean;
      };
    }>
  ): void {
    const cfg = this.resolveShortProbeConfig();
    if (!cfg.enabled || scored.length <= 3) return;
    if (
      this.shortProbeDiag.probeNodesUsed >= cfg.maxTotalProbeNodes ||
      this.numNodes >= this.config.maxNodes - 1
    ) {
      return;
    }
    if (scored.some((x) => x.meta.immediateWin)) return;
    if (scored[0].meta.score >= 3800) return;

    const toLive = context.attackerGoal === SearchGoal.ToLive;
    const basePot = this.evaluateGroupBaseAndEyeSectors(
      pos,
      context,
      tacCtx.targetColor
    );
    if (toLive && basePot.distinctSectors >= 2 && basePot.enclosedCount >= 2) {
      return;
    }

    const t0 = performance.now();
    const bs = pos.boardSize;
    const ourColor = pos.toPlay;
    const enemyColor = oppositeColor(ourColor);
    const legalRegion = regionCoords ? new Set<number>(regionCoords) : null;

    const fightZone: number[] = [];
    for (let p = 0; p < bs * bs; p++) {
      if (pos.grid[p] !== Color.Empty || pos.immortalWallSet.has(p)) continue;
      if (legalRegion && !legalRegion.has(p)) continue;
      const r = Math.floor(p / bs);
      const c = p % bs;
      let near = false;
      for (let dr = -2; dr <= 2 && !near; dr++) {
        for (let dc = -2; dc <= 2 && !near; dc++) {
          const nr = r + dr;
          const nc = c + dc;
          if (nr < 0 || nr >= bs || nc < 0 || nc >= bs) continue;
          const q = nr * bs + nc;
          if (pos.grid[q] !== Color.Empty && !pos.immortalWallSet.has(q)) {
            near = true;
          }
        }
      }
      if (near) fightZone.push(p);
    }

    const candIndices: number[] = [];
    for (
      let i = 2;
      i < Math.min(scored.length, 11) && candIndices.length < cfg.maxCandidatesPerFrontier;
      i++
    ) {
      const it = scored[i];
      if (it.mv === PASS_MOVE || !it.meta.inAttention || it.meta.immediateLoss) {
        continue;
      }
      const r = Math.floor(it.mv / bs);
      const c = it.mv % bs;
      const distR = Math.min(r, bs - 1 - r);
      const distC = Math.min(c, bs - 1 - c);
      const distEdge = Math.min(distR, distC);
      const oNbs = pos.orthogonalNeighbors(it.mv);
      let fOrtho = 0;
      let eOrtho = 0;
      let emptyOrtho = 0;
      for (let k = 0; k < oNbs.length; k++) {
        const st = pos.grid[oNbs[k]];
        if (st === ourColor) fOrtho++;
        else if (st === enemyColor) eOrtho++;
        else emptyOrtho++;
      }
      if (fOrtho > 0) continue;
      if (distR === 0 && distC === 0 && emptyOrtho === 2) continue;
      const dNbs = pos.diagonalNeighbors(it.mv);
      let ourTacDiag = 0;
      let enemyTacDiag = 0;
      for (let k = 0; k < dNbs.length; k++) {
        const st = pos.grid[dNbs[k]];
        if (st === ourColor && !pos.immortalWallSet.has(dNbs[k])) ourTacDiag++;
        else if (st === enemyColor && !pos.immortalWallSet.has(dNbs[k])) {
          enemyTacDiag++;
        }
      }
      if (
        toLive
          ? ourTacDiag >= 1 && distEdge <= 2
          : enemyTacDiag >= 2 && eOrtho >= 1 && distEdge <= 2
      ) {
        candIndices.push(i);
      }
    }

    if (candIndices.length === 0) {
      this.shortProbeDiag.probeTimeMs += performance.now() - t0;
      return;
    }

    this.shortProbeDiag.probesTriggered++;
    let bestIdxToPromote = -1;
    let bestMinimaxVal = -999999;

    for (let ci = 0; ci < candIndices.length; ci++) {
      if (
        this.shortProbeDiag.probeNodesUsed >= cfg.maxTotalProbeNodes ||
        this.numNodes >= this.config.maxNodes - 1
      ) {
        break;
      }
      const origIdx = candIndices[ci];
      const item = scored[origIdx];
      const p1 = pos.clone();
      const r1 = p1.playMove(item.mv);
      if (!r1.legal) continue;
      if (
        toLive &&
        r1.capturedCoords.length === 0 &&
        this.hasInteriorEmptyTriangle(p1, item.mv, ourColor)
      ) {
        continue;
      }
      const b1Ch = p1.floodFillChain(item.mv);
      if (b1Ch.liberties.size <= 1 && r1.capturedCoords.length === 0) continue;
      this.shortProbeDiag.candidatesProbed++;

      const defMoves: Array<{ w: number; s: number; pw: GoPosition }> = [];
      for (let j = 0; j < fightZone.length; j++) {
        const w = fightZone[j];
        if (p1.grid[w] !== Color.Empty) continue;
        const pw = p1.clone();
        const rw = pw.playMove(w);
        if (!rw.legal) continue;
        let ws = rw.capturedCoords.length * 1400;
        const oNbs = p1.orthogonalNeighbors(w);
        for (let k = 0; k < oNbs.length; k++) {
          const nb = oNbs[k];
          if (nb === item.mv) ws += 520;
          if (pw.grid[nb] === ourColor && !pw.immortalWallSet.has(nb)) {
            const ch = pw.floodFillChain(nb);
            if (ch.liberties.size === 1) ws += 950;
            else if (ch.liberties.size === 2) ws += 420;
            if (tacCtx.crucialStoneMask[nb]) ws += 380;
          }
        }
        const wr = Math.floor(w / bs);
        const wc = w % bs;
        if (Math.min(Math.min(wr, bs - 1 - wr), Math.min(wc, bs - 1 - wc)) <= 1) {
          ws += 220;
        }
        defMoves.push({ w, s: ws, pw });
      }
      defMoves.sort((a, b) => b.s - a.s);
      const kDef = Math.min(cfg.defenderBranchFactor, defMoves.length);
      if (kDef === 0) continue;

      let worstVal = 999999;
      let validAll = true;
      for (let d = 0; d < kDef; d++) {
        if (
          this.shortProbeDiag.probeNodesUsed >= cfg.maxTotalProbeNodes ||
          this.numNodes >= this.config.maxNodes - 1
        ) {
          validAll = false;
          break;
        }
        this.numNodes++;
        this.shortProbeDiag.probeNodesUsed++;
        const pw = defMoves[d].pw;
        if (pw.grid[item.mv] !== ourColor) {
          worstVal = -2000;
          break;
        }

        let topB2a: { p2: GoPosition; cap: number } | null = null;
        let topB2b: { p2: GoPosition; cap: number } | null = null;
        let sa = -999999;
        let sb = -999999;
        for (let j = 0; j < fightZone.length; j++) {
          const b2 = fightZone[j];
          if (pw.grid[b2] !== Color.Empty) continue;
          const p2 = pw.clone();
          const r2 = p2.playMove(b2);
          if (!r2.legal || p2.grid[item.mv] !== ourColor) continue;
          if (
            toLive &&
            r2.capturedCoords.length === 0 &&
            this.hasInteriorEmptyTriangle(p2, b2, ourColor)
          ) {
            continue;
          }
          let qs2 = r2.capturedCoords.length * 1000;
          const oNbs = pw.orthogonalNeighbors(b2);
          for (let k = 0; k < oNbs.length; k++) {
            const nb = oNbs[k];
            if (pw.grid[nb] === ourColor && !pw.immortalWallSet.has(nb)) qs2 += 280;
            else if (pw.grid[nb] !== Color.Empty && !pw.immortalWallSet.has(nb)) {
              qs2 += 200;
            }
          }
          const br = Math.floor(b2 / bs);
          const bc = b2 % bs;
          if (
            Math.min(Math.min(br, bs - 1 - br), Math.min(bc, bs - 1 - bc)) <= 1
          ) {
            qs2 += 260;
          }
          if (qs2 > sa) {
            sb = sa;
            topB2b = topB2a;
            sa = qs2;
            topB2a = { p2, cap: r2.capturedCoords.length };
          } else if (qs2 > sb) {
            sb = qs2;
            topB2b = { p2, cap: r2.capturedCoords.length };
          }
        }

        let bestReplyVal = -999999;
        for (const cand of [topB2a, topB2b]) {
          if (!cand) continue;
          const chAfter = cand.p2.floodFillChain(item.mv);
          if (chAfter.liberties.size <= 1 && cand.cap === 0) continue;
          const ev = this.evaluateGroupBaseAndEyeSectors(
            cand.p2,
            context,
            tacCtx.targetColor
          );
          const val = toLive
            ? !ev.crucialAlive
              ? -2000
              : ev.distinctSectors * 650 +
                ev.enclosedCount * 360 +
                ev.tigerCount * 220 +
                Math.min(ev.edgeBaseSpan, 8) * 140 +
                Math.min(ev.minCrucialLibs, 5) * 110 +
                cand.cap * 400
            : !ev.crucialAlive
            ? 2400
            : -ev.distinctSectors * 600 -
              ev.enclosedCount * 360 -
              Math.min(ev.minCrucialLibs, 5) * 150 +
              cand.cap * 450;
          if (val > bestReplyVal) bestReplyVal = val;
        }
        if (bestReplyVal < worstVal) worstVal = bestReplyVal;
      }

      if (validAll && worstVal > bestMinimaxVal) {
        bestMinimaxVal = worstVal;
        bestIdxToPromote = origIdx;
      }
    }

    const threshold = toLive ? 1400 : 200;
    if (bestIdxToPromote > 2 && bestMinimaxVal >= threshold) {
      const promoted = scored.splice(bestIdxToPromote, 1)[0];
      promoted.meta.score = Math.max(
        promoted.meta.score,
        scored[2].meta.score + 1
      );
      if (promoted.meta.score >= scored[1].meta.score) {
        promoted.meta.score = scored[1].meta.score - 1;
      }
      scored.splice(2, 0, promoted);
      this.shortProbeDiag.rankPromotions++;
    }
    this.shortProbeDiag.probeTimeMs += performance.now() - t0;
  }

  private computeEstimatedBytes(): number {
    // Conservative byte estimate across stateTable, historyTable, DAG nodes, frontier cache, revalCache, and TT
    return (
      this.stateTable.length * 1024 +
      this.historyTable.length * 2048 +
      this.proofDagNodes.length * 768 +
      this.nodeFrontierCache.size * 4096 +
      this.revalCache.size * 128 +
      this.ttStore.size * 1024
    );
  }

  private isMemoryBudgetExceeded(): boolean {
    if (
      !Number.isFinite(this.config.memoryBudgetMb) ||
      this.config.memoryBudgetMb <= 0
    ) {
      return false;
    }
    const budgetBytes = this.config.memoryBudgetMb * 1024 * 1024;
    return this.computeEstimatedBytes() > budgetBytes;
  }

  /**
   * Read-only memory & slot accounting over resident frontier cache and solver tables.
   */
  public getFrontierMemoryDiagnostics(): FrontierMemoryDiagnostics {
    let frontiers = 0;
    let candidateSlots = 0;
    let expandedSlots = 0;
    let emptyRzRefs = 0;
    let nonEmptyRzRefs = 0;
    const uniqueEmptyRzs = new Set<ProofCertificateRZ>();

    for (const fr of this.nodeFrontierCache.values()) {
      frontiers++;
      for (const ch of fr.children) {
        candidateSlots++;
        if (ch.expanded) expandedSlots++;
        for (const rz of [ch.proofRz, ch.disproofRz]) {
          if (rz.size === 0) {
            emptyRzRefs++;
            uniqueEmptyRzs.add(rz);
          } else {
            nonEmptyRzRefs++;
          }
        }
      }
    }

    return {
      frontiers,
      candidateSlots,
      expandedSlots,
      emptyRzRefs,
      nonEmptyRzRefs,
      uniqueEmptyRzInstances: uniqueEmptyRzs.size,
      engineEstimatedBytes: this.computeEstimatedBytes(),
      stateTableEntries: this.stateTable.length,
      historyTableEntries: this.historyTable.length,
      dagNodes: this.proofDagNodes.length,
      revalCacheEntries: this.revalCache.size,
      ttEntries: this.ttStore.size,
    };
  }

  private midSearch(
    pos: GoPosition,
    context: ProofContext,
    regionCoords: number[] | null,
    thPn: number,
    thDn: number,
    depth: number,
    currentStateId: number,
    incomingMove: number,
    inPathHashes: Set<string>,
    currentPath = ''
  ): {
    pn: number;
    dn: number;
    outcome: ProofOutcome;
    koDependent: boolean;
    proofRz: ProofCertificateRZ;
    disproofRz: ProofCertificateRZ;
    dagNodeId: number;
    exitReason: string;
  } {
    this.numNodes++;
    const entryCallIndex = this.numNodes;
    const isOrNode = pos.toPlay === context.rootAttacker;
    const residualMode = this.getResidualReplayMode();
    const residualActiveHere = residualMode !== 'off' && !isOrNode && depth <= 1;
    const traceThisNode =
      this.tracePathFilterSet !== null &&
      this.tracePathFilterSet.has(currentPath);
    const emitTrace = (
      ev: Omit<
        SearchPathTraceEvent,
        'invocationId' | 'entryCallIndex' | 'callIndex' | 'path' | 'depth' | 'isOrNode'
      >
    ): void => {
      if (traceThisNode && this.config.onPathTrace) {
        this.config.onPathTrace({
          ...ev,
          invocationId: entryCallIndex,
          entryCallIndex,
          callIndex: this.numNodes,
          path: currentPath,
          depth,
          isOrNode,
        });
      }
    };
    const emitEarlyEnterAndReturn = (
      ret: Omit<
        SearchPathTraceEvent,
        'kind' | 'invocationId' | 'entryCallIndex' | 'callIndex' | 'path' | 'depth' | 'isOrNode'
      >
    ): void => {
      if (!traceThisNode) return;
      emitTrace({
        kind: 'enter',
        thPn,
        thDn,
      });
      emitTrace({
        kind: 'return',
        ...ret,
        thPn,
        thDn,
      });
    };

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
        : ProofCertificateRZ.EMPTY;
      const disproofRz = !isWin
        ? new ProofCertificateRZ(term.leafCertificateRz)
        : ProofCertificateRZ.EMPTY;

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

      emitEarlyEnterAndReturn({
        pn,
        dn,
        outcome,
        exitReason: 'terminal',
        terminalEvidence: term.evidenceKind,
        dagNodeId,
      });

      return {
        pn,
        dn,
        outcome,
        koDependent: false,
        proofRz,
        disproofRz,
        dagNodeId,
        exitReason: 'terminal',
      };
    }

    // Step 2 (FR-4.5): Conservative InPath cycle guard
    const zHex = pos.computeZobristHex();
    if (inPathHashes.has(zHex)) {
      this.cycleDetections++;
      if (this.unknownReason === UnknownReason.None) {
        this.unknownReason = UnknownReason.Cycle;
      }
      emitEarlyEnterAndReturn({
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        exitReason: 'cycle',
      });
      return {
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        koDependent: false,
        proofRz: ProofCertificateRZ.EMPTY,
        disproofRz: ProofCertificateRZ.EMPTY,
        dagNodeId: -1,
        exitReason: 'cycle',
      };
    }

    // Step 3 (FR-4.7): Resource & depth guardrails
    if (depth >= this.config.maxDepth) {
      this.resourceExhausted = true;
      this.unknownReason = UnknownReason.DepthLimit;
      emitEarlyEnterAndReturn({
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        exitReason: 'depth_limit',
      });
      return {
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        koDependent: false,
        proofRz: ProofCertificateRZ.EMPTY,
        disproofRz: ProofCertificateRZ.EMPTY,
        dagNodeId: -1,
        exitReason: 'depth_limit',
      };
    }
    if (this.numNodes >= this.config.maxNodes) {
      this.resourceExhausted = true;
      this.unknownReason = UnknownReason.NodeLimit;
      emitEarlyEnterAndReturn({
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        exitReason: 'node_limit',
      });
      return {
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        koDependent: false,
        proofRz: ProofCertificateRZ.EMPTY,
        disproofRz: ProofCertificateRZ.EMPTY,
        dagNodeId: -1,
        exitReason: 'node_limit',
      };
    }
    if (this.isMemoryBudgetExceeded()) {
      this.resourceExhausted = true;
      this.unknownReason = UnknownReason.MemoryBudget;
      emitEarlyEnterAndReturn({
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        exitReason: 'memory_limit',
      });
      return {
        pn: 1,
        dn: 1,
        outcome: ProofOutcome.Unknown,
        koDependent: false,
        proofRz: ProofCertificateRZ.EMPTY,
        disproofRz: ProofCertificateRZ.EMPTY,
        dagNodeId: -1,
        exitReason: 'memory_limit',
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
      emitEarlyEnterAndReturn({
        pn: boardHit.pn,
        dn: boardHit.dn,
        outcome: boardHit.outcome,
        exitReason: 'board_tt_hit',
        terminalEvidence: 'TT_REVALIDATED_REUSE',
        dagNodeId: ttNodeId,
        sourceDagNodeId: boardHit.proofDagNodeId,
      });
      return {
        pn: boardHit.pn,
        dn: boardHit.dn,
        outcome: boardHit.outcome,
        koDependent: false,
        proofRz: boardHit.proofRz,
        disproofRz: boardHit.disproofRz,
        dagNodeId: ttNodeId,
        exitReason: 'board_tt_hit',
      };
    }

    if (this.config.ttMode === 'pattern-tt') {
      const patHit = this.ttStore.lookupPatternTT(
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
        emitEarlyEnterAndReturn({
          pn: patHit.record.pn,
          dn: patHit.record.dn,
          outcome: patHit.record.outcome,
          exitReason: 'pattern_tt_hit',
          terminalEvidence: 'TT_REVALIDATED_REUSE',
          dagNodeId: ttNodeId,
          sourceDagNodeId: patHit.record.proofDagNodeId,
        });
        return {
          pn: patHit.record.pn,
          dn: patHit.record.dn,
          outcome: patHit.record.outcome,
          koDependent: false,
          proofRz: patHit.record.storedRz,
          disproofRz: patHit.record.storedRz,
          dagNodeId: ttNodeId,
          exitReason: 'pattern_tt_hit',
        };
      }
    }

    // Step 5: Lookup or initialize cached frontier keyed by exact path-unique `currentStateId`
    // (O(1) lookup, zero string serialization, 100% guarantees childState.parentStateId === node.stateId).
    let frontier = this.nodeFrontierCache.get(currentStateId);
    if (!frontier) {
      const parentShape =
        !isOrNode && pos.consecutivePasses === 0 && this.config.enableFastCaptureOrdering
          ? this.terminalEval.estimateHeuristicShapePotential(
              pos,
              context.initialTokens
            )
          : { eyeLikeCount: 0, minCrucialLiberties: 0, minAdjacentEnemyLiberties: 99 };
      const tacCtx = this.config.enableFastCaptureOrdering
        ? this.buildNodeTacticalContext(pos, context)
        : null;
      const legalMoves = pos.generateLegalMoves(regionCoords);
      const scored = legalMoves.map((mv) => {
        const meta =
          this.config.enableFastCaptureOrdering && tacCtx
            ? this.evaluateCandidateMove(
                pos,
                context,
                mv,
                isOrNode,
                parentShape.eyeLikeCount,
                tacCtx
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
        const probeCfg = this.resolveShortProbeConfig();
        if (probeCfg.enabled && isOrNode && depth <= probeCfg.maxProbeSearchDepth) {
          this.runShortTacticalProbeOnOrFrontier(
            pos,
            context,
            regionCoords,
            tacCtx!,
            scored
          );
        }
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
          proofRz: ProofCertificateRZ.EMPTY,
          disproofRz: ProofCertificateRZ.EMPTY,
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
        lastPn: 1,
        lastDn: 1,
        lastThPn: PN_DN_SATURATION,
        lastThDn: PN_DN_SATURATION,
        lastExitReason: 'unknown',
        lastWindowSize: children.length,
        nodeDagNodeId: -1,
        nodeOutcome: ProofOutcome.Unknown,
      };
      this.nodeFrontierCache.set(currentStateId, frontier);
    }

    const children = frontier.children;
    inPathHashes.add(zHex);

    let finalPn = 1;
    let finalDn = 1;
    let finalOutcome = ProofOutcome.Unknown;
    let finalProofRz = ProofCertificateRZ.EMPTY;
    let finalDisproofRz = ProofCertificateRZ.EMPTY;
    let finalDagNodeId = -1;
    let traceExitReason = 'unknown';
    let lastWindowSize = children.length;

    if (traceThisNode) {
      let initWindow = children.length;
      if (this.config.enableProgressiveWidening && frontier.wideningLevel < 6) {
        const baseK = isOrNode
          ? Math.min(this.config.wideningBaseK, depth === 0 ? 4 : 3)
          : Math.min(Math.max(2, Math.floor(this.config.wideningBaseK / 2)), 3);
        const cap = baseK * Math.pow(2, frontier.wideningLevel);
        if (cap < children.length) initWindow = cap;
      }
      emitTrace({
        kind: 'enter',
        thPn,
        thDn,
        wideningLevel: frontier.wideningLevel,
        windowSize: initWindow,
        totalLegal: children.length,
        topCandidates: children.slice(0, 12).map((c, idx) => ({
          moveSgf: coordToSgf(c.move, pos.boardSize),
          rank: idx,
          tacticalScore: c.tacticalScore,
          pn: c.pn,
          dn: c.dn,
          expanded: c.expanded,
          prunedOutsideRz: c.prunedOutsideRz,
          outcome: c.outcome,
        })),
      });
    }

    while (true) {
      const totalLegal = children.length;
      let windowSize = totalLegal;
      if (this.config.enableProgressiveWidening && frontier.wideningLevel < 6) {
        const baseK = isOrNode
          ? Math.min(this.config.wideningBaseK, depth === 0 ? 4 : 3)
          : Math.min(Math.max(2, Math.floor(this.config.wideningBaseK / 2)), 3);
        const cap = baseK * Math.pow(2, frontier.wideningLevel);
        if (cap < totalLegal) windowSize = cap;
      }

      const hasActiveRz =
        this.config.enableRzPruning &&
        frontier.activeNullMoveRz !== null &&
        frontier.representativeDagId >= 0;

      // Helper to run zero-trust OutsideRZRevalidated revalidation on a single candidate child.
      const tryPruneChildOutsideRz = (
        ch: SearchChildSlot,
        restrictedSide: boolean
      ): boolean => {
        if (
          !frontier.activeNullMoveRz ||
          ch.expanded ||
          ch.outcome !== ProofOutcome.Unknown ||
          ch.checkedNullMoveDagId === frontier.representativeDagId
        ) {
          return false;
        }
        ch.checkedNullMoveDagId = frontier.representativeDagId;
        if (!this.rzEngine.isOutsideRZCandidate(ch.move, frontier.activeNullMoveRz)) {
          return false;
        }
        const nextPos = pos.clone();
        const playRes = nextPos.playMove(ch.move);
        if (
          !playRes.legal ||
          (playRes.isKoCapture && restrictedSide) ||
          !this.revalidateSourceProofOnQueryState(
            nextPos,
            context,
            regionCoords,
            frontier.representativeDagId,
            frontier.representativeOutcome
          )
        ) {
          if (traceThisNode && playRes.legal) {
            emitTrace({
              kind: 'rz_reval_fail',
              selectedMoveSgf: coordToSgf(ch.move, pos.boardSize),
              sourceDagNodeId: frontier.representativeDagId,
              representativeMoveSgf: coordToSgf(
                frontier.representativeMove,
                pos.boardSize
              ),
              queryZobristHex: nextPos.computeZobristHex(),
              queryHistoryLength: nextPos.historySnapshots.length,
            });
          }
          return false;
        }
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
          ch.hasCapture || Boolean(this.dagHasCapture[frontier.representativeDagId])
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
        if (traceThisNode) {
          emitTrace({
            kind: 'rz_prune',
            selectedMoveSgf: coordToSgf(ch.move, pos.boardSize),
            sourceDagNodeId: frontier.representativeDagId,
            representativeMoveSgf: coordToSgf(
              frontier.representativeMove,
              pos.boardSize
            ),
            queryZobristHex: nextPos.computeZobristHex(),
            queryHistoryLength: nextPos.historySnapshots.length,
          });
        }
        return true;
      };

      const restrictedSide =
        (pos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
        (pos.toPlay !== context.rootAttacker && !context.defenderAllowKo);

      // O(1) lazy outside-RZ predicate: an unexpanded Unknown move strictly outside
      // `activeNullMoveRz` that has not failed revalidation is deferred until all in-RZ
      // moves are proven (avoiding both 130+ wasted DAG pushes on refuted internal nodes
      // and artificial `widenTrigger` throttling from irrelevant outer-moat moves!).
      const isLazyOutsideRz = (ch: SearchChildSlot): boolean =>
        hasActiveRz &&
        !ch.expanded &&
        ch.outcome === ProofOutcome.Unknown &&
        ch.checkedNullMoveDagId !== frontier.representativeDagId &&
        this.rzEngine.isOutsideRZCandidate(ch.move, frontier.activeNullMoveRz!);

      // FR-5.5: When `activeNullMoveRz` is present, focus the active frontier exclusively on
      // non-lazy moves (all moves inside RZ plus any already-expanded or reval-failed moves)
      // across the entire legal set, deferring outer-moat revalidation until in-RZ closure.
      const activeIndices: number[] = [];
      let lazyOutsideCount = 0;
      let unexpandedU = 0;
      let firstUnexpandedIdx = -1;
      let outsideWitnessMetric = PN_DN_SATURATION;

      if (hasActiveRz) {
        for (let i = 0; i < totalLegal; i++) {
          const ch = children[i];
          if (isLazyOutsideRz(ch)) {
            lazyOutsideCount++;
          } else {
            activeIndices.push(i);
          }
        }
      } else {
        for (let i = 0; i < windowSize; i++) {
          activeIndices.push(i);
        }
        for (let i = windowSize; i < totalLegal; i++) {
          const ch = children[i];
          if (isOrNode) {
            if (ch.pn === 0 && ch.outcome === ProofOutcome.ProvenWin && !ch.koDependent) {
              outsideWitnessMetric = 0;
            }
            if (ch.dn > 0 || ch.outcome !== ProofOutcome.ProvenLoss || ch.dagNodeId < 0) {
              unexpandedU++;
              if (firstUnexpandedIdx < 0) firstUnexpandedIdx = i;
            }
          } else {
            if (ch.dn === 0 && ch.outcome === ProofOutcome.ProvenLoss && !ch.koDependent) {
              outsideWitnessMetric = 0;
            }
            if (ch.pn > 0 || ch.outcome !== ProofOutcome.ProvenWin || ch.dagNodeId < 0) {
              unexpandedU++;
              if (firstUnexpandedIdx < 0) firstUnexpandedIdx = i;
            }
          }
        }
        if (unexpandedU === 0 && windowSize < totalLegal) {
          for (let i = windowSize; i < totalLegal; i++) activeIndices.push(i);
          windowSize = totalLegal;
        }
      }

      const widenTrigger =
        unexpandedU > 0 && firstUnexpandedIdx >= 0
          ? Math.max(
              isOrNode
                ? children[firstUnexpandedIdx].pn
                : children[firstUnexpandedIdx].dn,
              (isOrNode ? 20 : 16) * (frontier.wideningLevel + 1)
            )
          : PN_DN_SATURATION;
      let curPn = 1;
      let curDn = 1;

      let forceExpandPassIdx = -1;
      if (isOrNode) {
        let minPn = outsideWitnessMetric;
        let windowSumDn = 0;
        for (let k = 0; k < activeIndices.length; k++) {
          const ch = children[activeIndices[k]];
          minPn = Math.min(minPn, ch.pn);
          windowSumDn = clampSat(windowSumDn + ch.dn);
        }
        if (hasActiveRz && minPn >= 48 && minPn < PN_DN_SATURATION) {
          // High-cost unexpanded in-RZ JIT relaxation: once all sharp (< 48) in-RZ
          // candidates have closed or exceeded 48, relax remaining unexpanded high-cost
          // in-RZ moves (both !inAttention and low-ranked in-attention candidates) to pn=8
          // so stale initial bounds do not stall closure of a nearly proven RZ.
          let relaxed = false;
          for (let k = 0; k < activeIndices.length; k++) {
            const ch = children[activeIndices[k]];
            if (!ch.expanded && ch.outcome === ProofOutcome.Unknown && !ch.koDependent && ch.pn >= 48) {
              ch.pn = 8;
              relaxed = true;
            }
          }
          if (relaxed) continue;
        }
        if (unexpandedU > 0) {
          minPn = Math.min(minPn, widenTrigger);
        }
        if (minPn > 0 && windowSumDn === 0 && lazyOutsideCount > 0) {
          // All in-RZ moves disproven -> batch-revalidate lazy outside-RZ candidates now!
          for (let i = 0; i < totalLegal; i++) {
            if (isLazyOutsideRz(children[i])) {
              tryPruneChildOutsideRz(children[i], restrictedSide);
            }
          }
          continue;
        }
        if (minPn > 0 && windowSumDn === 0 && unexpandedU > 0) {
          frontier.wideningLevel++;
          this.wideningUpgrades++;
          if (traceThisNode) {
            emitTrace({
              kind: 'widen',
              wideningLevel: frontier.wideningLevel,
              windowSize,
              totalLegal,
              pn: minPn,
              dn: windowSumDn,
            });
          }
          continue;
        }
        curPn = minPn;
        curDn = clampSat(windowSumDn + (unexpandedU > 0 || lazyOutsideCount > 0 ? 1 : 0));
      } else {
        let windowSumPn = 0;
        let minDn = outsideWitnessMetric;
        for (let k = 0; k < activeIndices.length; k++) {
          const ch = children[activeIndices[k]];
          windowSumPn = clampSat(windowSumPn + ch.pn);
          minDn = Math.min(minDn, ch.dn);
        }
        if (hasActiveRz && minDn >= 48 && minDn < PN_DN_SATURATION) {
          // High-cost unexpanded in-RZ JIT relaxation: once all sharp (< 48) in-RZ
          // defenses have closed or exceeded 48, relax remaining unexpanded high-cost
          // in-RZ defenses (both !inAttention and low-ranked in-attention candidates) to dn=4
          // so stale initial bounds do not spike ancestor dn and bounce out of the subtree.
          let relaxed = false;
          for (let k = 0; k < activeIndices.length; k++) {
            const ch = children[activeIndices[k]];
            if (!ch.expanded && ch.outcome === ProofOutcome.Unknown && !ch.koDependent && ch.dn >= 48) {
              ch.dn = 4;
              relaxed = true;
            }
          }
          if (relaxed) continue;
        }
        if (unexpandedU > 0) {
          minDn = Math.min(minDn, widenTrigger);
        }
        if (minDn > 0 && windowSumPn === 0 && lazyOutsideCount > 0) {
          // All in-RZ defenses proven -> batch-revalidate lazy outside-RZ moves in one shot!
          for (let i = 0; i < totalLegal; i++) {
            if (isLazyOutsideRz(children[i])) {
              tryPruneChildOutsideRz(children[i], restrictedSide);
            }
          }
          continue;
        }
        if (minDn > 0 && windowSumPn === 0 && unexpandedU > 0) {
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
            frontier.wideningLevel++;
            this.wideningUpgrades++;
            if (traceThisNode) {
              emitTrace({
                kind: 'widen',
                wideningLevel: frontier.wideningLevel,
                windowSize,
                totalLegal,
                pn: windowSumPn,
                dn: minDn,
              });
            }
            continue;
          }
        } else {
          curPn = clampSat(windowSumPn + (unexpandedU > 0 || lazyOutsideCount > 0 ? 1 : 0));
          curDn = minDn;
        }
      }

      // Check asymmetric decisive completion conditions (FR-4.2)
      if (curPn === 0 || curDn === 0) {
        if (
          ((isOrNode && curDn === 0) || (!isOrNode && curPn === 0)) &&
          (unexpandedU > 0 || lazyOutsideCount > 0)
        ) {
          if (lazyOutsideCount > 0) {
            for (let i = 0; i < totalLegal; i++) {
              if (isLazyOutsideRz(children[i])) {
                tryPruneChildOutsideRz(children[i], restrictedSide);
              }
            }
          } else {
            frontier.wideningLevel++;
            this.wideningUpgrades++;
            if (traceThisNode) {
              emitTrace({
                kind: 'widen',
                wideningLevel: frontier.wideningLevel,
                windowSize,
                totalLegal,
                pn: curPn,
                dn: curDn,
              });
            }
          }
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
        if (
          depth === 0 &&
          ((isOrNode && curDn === 0) || (!isOrNode && curPn === 0))
        ) {
          // Universal root: ensure rootBestMove is a valid verified child move (or PASS_MOVE)
          const hasCur = recordedChildren.some(
            (c) => c.move === this.rootBestMove
          );
          if (!hasCur) {
            this.rootBestMove =
              recordedChildren.length > 0
                ? recordedChildren[0].move
                : PASS_MOVE;
          }
        }

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
        traceExitReason = curPn === 0 ? 'proven_win' : 'proven_loss';
        break;
      }

      lastWindowSize = windowSize;

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
          traceExitReason = 'memory_limit';
        } else if (this.numNodes >= this.config.maxNodes) {
          traceExitReason = 'node_limit';
        } else if (curPn >= thPn && curDn >= thDn) {
          traceExitReason = 'threshold_pn_dn';
        } else if (curPn >= thPn) {
          traceExitReason = 'threshold_pn';
        } else {
          traceExitReason = 'threshold_dn';
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
        let divGroupSizes: Map<ResidualDivergenceKind, number> | null = null;
        if (residualActiveHere && hasActiveRz) {
          for (let k = 0; k < activeIndices.length; k++) {
            const ch = children[activeIndices[k]];
            if (
              ch.outcome === ProofOutcome.Unknown &&
              !ch.koDependent &&
              ch.firstDivergence
            ) {
              if (!divGroupSizes) divGroupSizes = new Map();
              divGroupSizes.set(
                ch.firstDivergence,
                (divGroupSizes.get(ch.firstDivergence) ?? 0) + 1
              );
            }
          }
        }
        const getTieRank = (ch: SearchChildSlot): [number, number] => [
          ch.firstDivergence && divGroupSizes
            ? divGroupSizes.get(ch.firstDivergence) ?? 0
            : 0,
          (ch.subtreeWorkNodes ?? 0) > 0 ? 1 : 0,
        ];

        for (let k = 0; k < activeIndices.length; k++) {
          const i = activeIndices[k];
          if (children[i].koDependent) continue;
          const m = isOrNode ? children[i].pn : children[i].dn;
          if (m < bestMetric) {
            secondBestMetric = bestMetric;
            bestMetric = m;
            bestIdx = i;
          } else if (m === bestMetric) {
            secondBestMetric = m;
            if (divGroupSizes && bestIdx >= 0) {
              const [candGrp, candWork] = getTieRank(children[i]);
              const [bestGrp, bestWork] = getTieRank(children[bestIdx]);
              if (
                candGrp > bestGrp ||
                (candGrp === bestGrp && candWork > bestWork)
              ) {
                bestIdx = i;
              }
            }
          } else if (m < secondBestMetric) {
            secondBestMetric = m;
          }
        }

        // Progressive Widening upgrade condition: widen as soon as active window reaches widenTrigger
        if (unexpandedU > 0) {
          if (bestIdx < 0 || bestMetric >= widenTrigger) {
            frontier.wideningLevel++;
            this.wideningUpgrades++;
            if (traceThisNode) {
              emitTrace({
                kind: 'widen',
                wideningLevel: frontier.wideningLevel,
                windowSize,
                totalLegal,
                pn: curPn,
                dn: curDn,
              });
            }
            continue;
          }
          secondBestMetric = Math.min(secondBestMetric, widenTrigger);
        }
      }

      if (bestIdx < 0 || bestMetric >= PN_DN_SATURATION) {
        finalPn = curPn;
        finalDn = curDn;
        finalOutcome = ProofOutcome.Unknown;
        traceExitReason = 'saturated';
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
      // 1+epsilon df-pn (Pawlewicz & Lew / Kishimoto & Mueller) with >= +4 & 1.65x margin so
      // child thresholds sustain deep tactical reading without bouncing at depths 2..4.
      const epsMetricBound = clampSat(
        Math.max(secondBestMetric + 4, Math.ceil(secondBestMetric * 1.65) + 4)
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

      if (traceThisNode) {
        emitTrace({
          kind: 'select',
          selectedMoveSgf: coordToSgf(mpc.move, pos.boardSize),
          selectedRank: bestIdx,
          pn: mpc.pn,
          dn: mpc.dn,
          childThPn,
          childThDn,
          wideningLevel: frontier.wideningLevel,
          windowSize,
          totalLegal,
          activeCount: activeIndices.length,
        });
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

      // Just-In-Time (JIT) sibling proof replay before descending into unresolved AND child
      if (
        residualActiveHere &&
        mpc.outcome === ProofOutcome.Unknown &&
        frontier.provenSources &&
        frontier.provenSources.length > 0
      ) {
        let jitClosed = false;
        const mpcSgf = coordToSgf(mpc.move, pos.boardSize);
        for (let si = 0; si < frontier.provenSources.length; si++) {
          const src = frontier.provenSources[si];
          const res = this.tryReplaySourceOnSiblingSlot(
            mpc,
            nextPos,
            mpc.hasCapture,
            pos,
            currentStateId,
            isOrNode,
            src,
            residualMode,
            context,
            regionCoords
          );
          if (res === 'closed') {
            this.residualDiag.sourceClosureEvents.push({
              parentPath: this.derivePathFromStateTable(
                currentStateId,
                pos.boardSize
              ),
              sourceMoveSgf: coordToSgf(src.move, pos.boardSize),
              sourceDagId: src.dagId,
              closedMovesSgf: [mpcSgf],
              failedMovesSgf: [],
              prefilterSkippedMovesSgf: [],
            });
            jitClosed = true;
            break;
          }
        }
        if (jitClosed) continue;
      }

      const childPath =
        this.tracePathFilterSet !== null
          ? currentPath
            ? `${currentPath}/${coordToSgf(mpc.move, pos.boardSize)}`
            : coordToSgf(mpc.move, pos.boardSize)
          : '';

      const nodesBeforeChild = residualActiveHere ? this.numNodes : 0;
      const subRes = this.midSearch(
        nextPos,
        context,
        regionCoords,
        childThPn,
        childThDn,
        depth + 1,
        mpc.stateId,
        mpc.move,
        inPathHashes,
        childPath
      );
      if (residualActiveHere) {
        mpc.subtreeWorkNodes =
          (mpc.subtreeWorkNodes ?? 0) + (this.numNodes - nodesBeforeChild);
      }

      mpc.pn = subRes.pn;
      mpc.dn = subRes.dn;
      mpc.outcome = subRes.outcome;
      mpc.proofRz = subRes.proofRz;
      mpc.disproofRz = subRes.disproofRz;
      mpc.dagNodeId = subRes.dagNodeId;
      mpc.expanded = true;
      mpc.lastThPn = childThPn;
      mpc.lastThDn = childThDn;
      mpc.lastExitReason = subRes.exitReason;

      // FR-5.7: KoDependent witness barrier check (reuses loop-scoped `restrictedSide`)
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

      if (
        this.shortProbeDiag.firstParentUsableSubproof === null &&
        !mpc.koDependent &&
        mpc.dagNodeId >= 0 &&
        (mpc.outcome === ProofOutcome.ProvenWin ||
          mpc.outcome === ProofOutcome.ProvenLoss)
      ) {
        const usableEv: ParentUsableSubproofEvent = {
          callIndex: this.numNodes,
          parentPath: this.derivePathFromStateTable(
            currentStateId,
            pos.boardSize
          ),
          closedMoveSgf: coordToSgf(mpc.move, pos.boardSize),
          outcome: mpc.outcome,
          dagNodeId: mpc.dagNodeId,
        };
        this.shortProbeDiag.firstParentUsableSubproof = usableEv;
      }

      // Residual defense divergence classification & sibling replay hook (default OFF)
      if (
        residualActiveHere &&
        !mpc.koDependent &&
        mpc.pn === 0 &&
        mpc.outcome === ProofOutcome.ProvenWin &&
        mpc.dagNodeId >= 0
      ) {
        if (depth <= 1 && this.residualDiag.rootFirstSourceCallIndex === null) {
          this.residualDiag.rootFirstSourceCallIndex = this.numNodes;
        }
        if (!frontier.provenSources) frontier.provenSources = [];
        const alreadyRecorded = frontier.provenSources.some(
          (s) => s.dagId === mpc.dagNodeId
        );
        if (!alreadyRecorded) {
          const srcObj = {
            move: mpc.move,
            dagId: mpc.dagNodeId,
            rz: mpc.proofRz,
          };
          if (mpc.move === PASS_MOVE) {
            frontier.provenSources.unshift(srcObj);
          } else {
            frontier.provenSources.push(srcObj);
          }
          this.residualDiag.sourcesRecorded++;

          if (frontier.provenSources.length === 1 || mpc.move === PASS_MOVE) {
            const tDiv0 = performance.now();
            for (let si = 0; si < children.length; si++) {
              const sib = children[si];
              if (
                sib === mpc ||
                sib.outcome !== ProofOutcome.Unknown ||
                sib.koDependent ||
                sib.firstDivergence !== undefined ||
                this.rzEngine.isOutsideRZCandidate(sib.move, mpc.proofRz)
              ) {
                continue;
              }
              const qPos = pos.clone();
              const qPlay = qPos.playMove(sib.move);
              if (!qPlay.legal || (qPlay.isKoCapture && restrictedSide)) continue;
              const div = this.diagnoseFirstDivergence(
                qPos,
                context,
                regionCoords,
                mpc.dagNodeId,
                ProofOutcome.ProvenWin
              );
              if (div !== null) {
                sib.firstDivergence = div;
                this.residualDiag.divergenceCounts[div]++;
              }
            }
            this.residualDiag.divergenceClassifyTimeMs +=
              performance.now() - tDiv0;
          }

          const expandedUnresolved = children.filter(
            (s) =>
              s !== mpc &&
              s.expanded &&
              s.outcome === ProofOutcome.Unknown &&
              !s.koDependent
          );
          if (expandedUnresolved.length > 0) {
            const mpcDiv = mpc.firstDivergence;
            expandedUnresolved.sort((a, b) => {
              const pa = mpcDiv !== undefined && a.firstDivergence === mpcDiv ? 0 : 1;
              const pb = mpcDiv !== undefined && b.firstDivergence === mpcDiv ? 0 : 1;
              return pa - pb;
            });
            const closedMovesSgf: string[] = [];
            const failedMovesSgf: string[] = [];
            const prefilterSkippedMovesSgf: string[] = [];

            for (let si = 0; si < expandedUnresolved.length; si++) {
              const sib = expandedUnresolved[si];
              const qPos = pos.clone();
              const qPlay = qPos.playMove(sib.move);
              if (!qPlay.legal || (qPlay.isKoCapture && restrictedSide)) continue;
              const sibSgf = coordToSgf(sib.move, pos.boardSize);
              const res = this.tryReplaySourceOnSiblingSlot(
                sib,
                qPos,
                qPlay.capturedCoords.length > 0,
                pos,
                currentStateId,
                isOrNode,
                srcObj,
                residualMode,
                context,
                regionCoords
              );
              if (res === 'closed') closedMovesSgf.push(sibSgf);
              else if (res === 'failed') failedMovesSgf.push(sibSgf);
              else if (res === 'prefilter_skip') {
                prefilterSkippedMovesSgf.push(sibSgf);
              }
            }

            if (
              depth <= 1 ||
              closedMovesSgf.length > 0 ||
              failedMovesSgf.length > 0
            ) {
              this.residualDiag.sourceClosureEvents.push({
                parentPath: this.derivePathFromStateTable(
                  currentStateId,
                  pos.boardSize
                ),
                sourceMoveSgf: coordToSgf(mpc.move, pos.boardSize),
                sourceDagId: mpc.dagNodeId,
                closedMovesSgf,
                failedMovesSgf,
                prefilterSkippedMovesSgf,
              });
            }
          }
        }
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
        if (traceThisNode) {
          emitTrace({
            kind: 'rep_proof',
            representativeMoveSgf: coordToSgf(mpc.move, pos.boardSize),
            sourceDagNodeId: mpc.dagNodeId,
            rzSize: mpc.proofRz.size,
            outcome: ProofOutcome.ProvenWin,
          });
        }
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
        if (traceThisNode) {
          emitTrace({
            kind: 'rep_proof',
            representativeMoveSgf: coordToSgf(mpc.move, pos.boardSize),
            sourceDagNodeId: mpc.dagNodeId,
            rzSize: mpc.disproofRz.size,
            outcome: ProofOutcome.ProvenLoss,
          });
        }
      }
    }

    inPathHashes.delete(zHex);

    frontier.lastPn = finalPn;
    frontier.lastDn = finalDn;
    frontier.lastThPn = thPn;
    frontier.lastThDn = thDn;
    frontier.lastExitReason = traceExitReason;
    frontier.lastWindowSize = lastWindowSize;
    frontier.nodeDagNodeId = finalDagNodeId;
    frontier.nodeOutcome = finalOutcome;

    if (traceThisNode) {
      emitTrace({
        kind: 'return',
        pn: finalPn,
        dn: finalDn,
        outcome: finalOutcome,
        thPn,
        thDn,
        exitReason: traceExitReason,
        terminalEvidence:
          finalDagNodeId >= 0
            ? this.proofDagNodes[finalDagNodeId]?.terminalEvidence
            : undefined,
        dagNodeId: finalDagNodeId >= 0 ? finalDagNodeId : undefined,
        wideningLevel: frontier.wideningLevel,
        windowSize: lastWindowSize,
        totalLegal: children.length,
        sourceDagNodeId:
          frontier.representativeDagId >= 0
            ? frontier.representativeDagId
            : undefined,
        representativeMoveSgf:
          frontier.representativeDagId >= 0
            ? coordToSgf(frontier.representativeMove, pos.boardSize)
            : undefined,
      });
    }

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
      exitReason: traceExitReason,
    };
  }

  private buildBranchCoverageSnapshots(
    rootPos: GoPosition,
    context: ProofContext,
    rootStateId: number,
    rootResult: {
      pn: number;
      dn: number;
      outcome: ProofOutcome;
      dagNodeId: number;
      exitReason: string;
    },
    runSource: 'original_root' | 'standalone_subposition'
  ): BranchCoverageSnapshot[] {
    const snapshots: BranchCoverageSnapshot[] = [];
    const seenPaths = new Set<string>();
    const boardSize = rootPos.boardSize;

    const buildSnapshotForNode = (
      path: string,
      movesFromRoot: number[],
      movesFromRootSgf: string[],
      toPlay: Color,
      stateId: number,
      slotFallback?: {
        pn: number;
        dn: number;
        outcome: ProofOutcome;
        dagNodeId: number;
        lastThPn?: number;
        lastThDn?: number;
        lastExitReason?: string;
      }
    ): BranchCoverageSnapshot | null => {
      if (seenPaths.has(path)) return null;
      seenPaths.add(path);

      const depth = movesFromRoot.length;
      const isOrNode = toPlay === context.rootAttacker;
      const nodeRole: 'OR_ATTACKER' | 'AND_DEFENDER' = isOrNode
        ? 'OR_ATTACKER'
        : 'AND_DEFENDER';
      const obligation: 'EXISTENTIAL_OR' | 'UNIVERSAL_AND' = isOrNode
        ? 'EXISTENTIAL_OR'
        : 'UNIVERSAL_AND';
      const computeCoverageObligation = (
        outcome: ProofOutcome
      ): BranchCoverageObligation => {
        if (outcome === ProofOutcome.ProvenWin) {
          return isOrNode ? 'SINGLE_WITNESS' : 'FULL_COVERAGE';
        }
        if (outcome === ProofOutcome.ProvenLoss) {
          return isOrNode ? 'FULL_COVERAGE' : 'SINGLE_WITNESS';
        }
        return isOrNode
          ? 'UNDECIDED_OR_WIN_SINGLE_LOSS_ALL'
          : 'UNDECIDED_AND_WIN_ALL_LOSS_SINGLE';
      };
      const frontier = stateId >= 0 ? this.nodeFrontierCache.get(stateId) : undefined;

      if (!frontier) {
        const dagId = slotFallback?.dagNodeId ?? -1;
        const dagNode =
          dagId >= 0 && dagId < this.proofDagNodes.length
            ? this.proofDagNodes[dagId]
            : undefined;
        const leafOutcome = slotFallback?.outcome ?? ProofOutcome.Unknown;
        return {
          path,
          movesFromRoot: movesFromRoot.slice(),
          movesFromRootSgf: movesFromRootSgf.slice(),
          depth,
          isOrNode,
          nodeRole,
          coverageObligation: computeCoverageObligation(leafOutcome),
          obligation,
          toPlay,
          runSource,
          rootOutcome: rootResult.outcome,
          nodeOutcome: leafOutcome,
          nodeDagNodeId: dagId,
          terminalEvidence: dagNode?.terminalEvidence ?? 'UNEXPANDED_OR_TERMINAL',
          lastPn: slotFallback?.pn ?? 1,
          lastDn: slotFallback?.dn ?? 1,
          lastThPn: slotFallback?.lastThPn ?? PN_DN_SATURATION,
          lastThDn: slotFallback?.lastThDn ?? PN_DN_SATURATION,
          lastExitReason: slotFallback?.lastExitReason ?? 'terminal',
          wideningLevel: 0,
          windowSize: 0,
          totalLegalMoves: 0,
          closedCount: 0,
          provenSourceCount: 0,
          ttReplayedCount: 0,
          rzRevalidatedCount: 0,
          deferredOutsideRzCount: 0,
          expandedUnresolvedCount: 0,
          unexpandedCount: 0,
          koBarrierCount: 0,
          representativeMoveSgf: null,
          representativeDagNodeId: null,
          representativeRzSize: 0,
          moves: [],
        };
      }

      const hasActiveRz =
        this.config.enableRzPruning &&
        frontier.activeNullMoveRz !== null &&
        frontier.representativeDagId >= 0;

      let provenSourceCount = 0;
      let ttReplayedCount = 0;
      let rzRevalidatedCount = 0;
      let deferredOutsideRzCount = 0;
      let expandedUnresolvedCount = 0;
      let unexpandedCount = 0;
      let koBarrierCount = 0;

      const moves: BranchMoveCoverageEntry[] = frontier.children.map((ch, idx) => {
        const chDagNode =
          ch.dagNodeId >= 0 && ch.dagNodeId < this.proofDagNodes.length
            ? this.proofDagNodes[ch.dagNodeId]
            : undefined;
        let status: BranchMoveCoverageStatus;
        if (ch.koDependent) {
          status = 'KO_BARRIER';
          koBarrierCount++;
        } else if (ch.prunedOutsideRz && ch.dagNodeId >= 0) {
          status = 'RZ_REVALIDATED';
          rzRevalidatedCount++;
        } else if (ch.outcome !== ProofOutcome.Unknown && ch.dagNodeId >= 0) {
          if (chDagNode?.isTtHit) {
            status = 'TT_REPLAYED';
            ttReplayedCount++;
          } else {
            status = 'PROVEN_SOURCE';
            provenSourceCount++;
          }
        } else if (
          hasActiveRz &&
          !ch.expanded &&
          ch.outcome === ProofOutcome.Unknown &&
          ch.checkedNullMoveDagId !== frontier.representativeDagId &&
          this.rzEngine.isOutsideRZCandidate(ch.move, frontier.activeNullMoveRz!)
        ) {
          status = 'DEFERRED_OUTSIDE_RZ';
          deferredOutsideRzCount++;
        } else if (ch.expanded) {
          status = 'EXPANDED_UNRESOLVED';
          expandedUnresolvedCount++;
        } else {
          status = 'UNEXPANDED';
          unexpandedCount++;
        }

        return {
          rank: idx,
          move: ch.move,
          moveSgf: coordToSgf(ch.move, boardSize),
          tacticalScore: ch.tacticalScore,
          pn: ch.pn,
          dn: ch.dn,
          outcome: ch.outcome,
          status,
          dagNodeId: ch.dagNodeId,
          sourceProofNodeId: chDagNode?.sourceProofNodeId ?? null,
          terminalEvidence: chDagNode?.terminalEvidence,
          lastThPn: ch.lastThPn,
          lastThDn: ch.lastThDn,
          lastExitReason: ch.lastExitReason,
        };
      });

      const nodeDagId = frontier.nodeDagNodeId;
      const nodeDag =
        nodeDagId >= 0 && nodeDagId < this.proofDagNodes.length
          ? this.proofDagNodes[nodeDagId]
          : undefined;

      return {
        path,
        movesFromRoot: movesFromRoot.slice(),
        movesFromRootSgf: movesFromRootSgf.slice(),
        depth,
        isOrNode,
        nodeRole,
        coverageObligation: computeCoverageObligation(frontier.nodeOutcome),
        obligation,
        toPlay,
        runSource,
        rootOutcome: rootResult.outcome,
        nodeOutcome: frontier.nodeOutcome,
        nodeDagNodeId: nodeDagId,
        terminalEvidence: nodeDag?.terminalEvidence ?? 'NONE',
        lastPn: frontier.lastPn,
        lastDn: frontier.lastDn,
        lastThPn: frontier.lastThPn,
        lastThDn: frontier.lastThDn,
        lastExitReason: frontier.lastExitReason,
        wideningLevel: frontier.wideningLevel,
        windowSize: frontier.lastWindowSize,
        totalLegalMoves: frontier.children.length,
        closedCount: provenSourceCount + ttReplayedCount + rzRevalidatedCount,
        provenSourceCount,
        ttReplayedCount,
        rzRevalidatedCount,
        deferredOutsideRzCount,
        expandedUnresolvedCount,
        unexpandedCount,
        koBarrierCount,
        representativeMoveSgf:
          frontier.representativeDagId >= 0
            ? coordToSgf(frontier.representativeMove, boardSize)
            : null,
        representativeDagNodeId:
          frontier.representativeDagId >= 0 ? frontier.representativeDagId : null,
        representativeRzSize: frontier.activeNullMoveRz?.size ?? 0,
        moves,
      };
    };

    // 1. Always capture root snapshot
    const rootSnap = buildSnapshotForNode('', [], [], rootPos.toPlay, rootStateId, {
      pn: rootResult.pn,
      dn: rootResult.dn,
      outcome: rootResult.outcome,
      dagNodeId: rootResult.dagNodeId,
      lastThPn: PN_DN_SATURATION,
      lastThDn: PN_DN_SATURATION,
      lastExitReason: rootResult.exitReason,
    });
    if (rootSnap) snapshots.push(rootSnap);

    // 2. Capture all expanded depth-1 children (including direct terminal/TT leaves like p001/ba)
    const rootFrontier = this.nodeFrontierCache.get(rootStateId);
    if (rootFrontier) {
      for (const ch of rootFrontier.children) {
        if (!ch.expanded && ch.dagNodeId < 0) continue;
        const moveSgf = coordToSgf(ch.move, boardSize);
        const childSnap = buildSnapshotForNode(
          moveSgf,
          [ch.move],
          [moveSgf],
          oppositeColor(rootPos.toPlay),
          ch.stateId,
          {
            pn: ch.pn,
            dn: ch.dn,
            outcome: ch.outcome,
            dagNodeId: ch.dagNodeId,
            lastThPn: ch.lastThPn,
            lastThDn: ch.lastThDn,
            lastExitReason: ch.lastExitReason,
          }
        );
        if (childSnap) snapshots.push(childSnap);
      }
    }

    // 3. Capture any extra requested coveragePathFilters / tracePathFilters paths
    const extraPaths = new Set<string>();
    for (const p of this.config.coveragePathFilters ?? []) {
      if (p) extraPaths.add(p);
    }
    for (const p of this.config.tracePathFilters ?? []) {
      if (p) extraPaths.add(p);
    }

    for (const rawPath of extraPaths) {
      const normalized = rawPath.trim().replace(/^\/+|\/+$/g, '');
      if (!normalized || seenPaths.has(normalized)) continue;
      const segments = normalized.split('/').filter(Boolean);
      let curStateId = rootStateId;
      let curToPlay = rootPos.toPlay;
      const movesFromRoot: number[] = [];
      const movesFromRootSgf: string[] = [];
      let matchedSlot: SearchChildSlot | undefined;
      let valid = true;

      for (const seg of segments) {
        const curFrontier =
          curStateId >= 0 ? this.nodeFrontierCache.get(curStateId) : undefined;
        if (!curFrontier) {
          valid = false;
          break;
        }
        const slot = curFrontier.children.find(
          (c) => coordToSgf(c.move, boardSize) === seg
        );
        if (!slot || (!slot.expanded && slot.dagNodeId < 0)) {
          valid = false;
          break;
        }
        movesFromRoot.push(slot.move);
        movesFromRootSgf.push(seg);
        curStateId = slot.stateId;
        curToPlay = oppositeColor(curToPlay);
        matchedSlot = slot;
      }

      if (valid && matchedSlot) {
        const snap = buildSnapshotForNode(
          normalized,
          movesFromRoot,
          movesFromRootSgf,
          curToPlay,
          curStateId,
          {
            pn: matchedSlot.pn,
            dn: matchedSlot.dn,
            outcome: matchedSlot.outcome,
            dagNodeId: matchedSlot.dagNodeId,
            lastThPn: matchedSlot.lastThPn,
            lastThDn: matchedSlot.lastThDn,
            lastExitReason: matchedSlot.lastExitReason,
          }
        );
        if (snap) snapshots.push(snap);
      }
    }

    return snapshots;
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
