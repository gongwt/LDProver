// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// TypeScript 1:1 execution mirror of include/ldprover/core/types.h

export const DEFAULT_BOARD_SIZE = 19;
export const PASS_MOVE = -1;
export const NULL_MOVE = -2;
export const PN_DN_SATURATION = 1073741823; // §4.1 SAT constant

export enum Color {
  Empty = 0,
  Black = 1,
  White = 2,
}

export function oppositeColor(color: Color): Color {
  if (color === Color.Black) return Color.White;
  if (color === Color.White) return Color.Black;
  return Color.Empty;
}

export function colorToString(color: Color): string {
  if (color === Color.Black) return 'B';
  if (color === Color.White) return 'W';
  return 'E';
}

export enum KoRule {
  SituationalSuperko = 'SSK', // Default C-2, FR-2.2
  PositionalSuperko = 'PSK',  // Internal experiment switch
  SimpleKoOnly = 'SIMPLE',    // Internal experiment switch
}

export enum SearchGoal {
  ToLive = 'TOLIVE',
  ToKill = 'TOKILL',
}

export enum LogicalOp {
  Single = 'SINGLE',
  Conjunction = 'AND', // '&'
  Disjunction = 'OR',  // '|'
}

export enum TerminalStatus {
  Win = 'Win',
  Loss = 'Loss',
  NonTerminal = 'NonTerminal',
  Unsupported = 'Unsupported',
}

export enum ProofOutcome {
  ProvenWin = 'PROVEN_WIN',
  ProvenLoss = 'PROVEN_LOSS',
  Unknown = 'UNKNOWN',
}

export enum UnknownReason {
  None = 'none',
  Timeout = 'timeout',
  NodeLimit = 'node_limit',
  MemoryBudget = 'memory_budget',
  DepthLimit = 'depth_limit',
  Cycle = 'cycle',
  KoDependent = 'ko_dependent',
  WideningStalled = 'widening_stalled',
  InternalError = 'internal_error',
}

export enum EyeTopologyType {
  FalseEye = 'FALSE_EYE',
  HalfEye = 'HALF_EYE',
  TrueEye = 'TRUE_EYE',
  SemeaiDame = 'SEMEAI_DAME',
}

export interface TargetToken {
  tokenId: number;
  initialCoord: number;
  groupIndex: number;
  stoneColor: Color;
}

export interface ProofContext {
  contextId: string;
  rootAttacker: Color;
  attackerGoal: SearchGoal;
  crucialStoneOp: LogicalOp;
  koRule: KoRule;
  attackerAllowKo: boolean;
  defenderAllowKo: boolean;
  initialTokens: TargetToken[];
}

export interface CanonicalSnapshot {
  blackCoords: number[];
  whiteCoords: number[];
  toPlay: Color;
  zobristHex: string;
}

export interface SearchTraceCandidateSummary {
  moveSgf: string;
  rank: number;
  tacticalScore: number;
  pn: number;
  dn: number;
  expanded: boolean;
  prunedOutsideRz: boolean;
  outcome: ProofOutcome;
}

export interface SearchPathTraceEvent {
  kind:
    | 'enter'
    | 'select'
    | 'widen'
    | 'return'
    | 'rep_proof'
    | 'rz_prune'
    | 'rz_reval_fail';
  invocationId: number;
  entryCallIndex: number;
  callIndex: number;
  path: string;
  depth: number;
  isOrNode: boolean;
  thPn?: number;
  thDn?: number;
  pn?: number;
  dn?: number;
  outcome?: ProofOutcome;
  exitReason?: string;
  terminalEvidence?: string;
  dagNodeId?: number;
  wideningLevel?: number;
  windowSize?: number;
  totalLegal?: number;
  activeCount?: number;
  selectedMoveSgf?: string;
  selectedRank?: number;
  childThPn?: number;
  childThDn?: number;
  sourceDagNodeId?: number;
  representativeMoveSgf?: string;
  rzSize?: number;
  queryZobristHex?: string;
  queryHistoryLength?: number;
  topCandidates?: SearchTraceCandidateSummary[];
}

export type BranchMoveCoverageStatus =
  | 'PROVEN_SOURCE'
  | 'TT_REPLAYED'
  | 'RZ_REVALIDATED'
  | 'DEFERRED_OUTSIDE_RZ'
  | 'EXPANDED_UNRESOLVED'
  | 'UNEXPANDED'
  | 'KO_BARRIER';

export interface BranchMoveCoverageEntry {
  rank: number;
  move: number;
  moveSgf: string;
  tacticalScore: number;
  pn: number;
  dn: number;
  outcome: ProofOutcome;
  status: BranchMoveCoverageStatus;
  dagNodeId: number;
  sourceProofNodeId: number | null;
  terminalEvidence?: string;
  lastThPn?: number;
  lastThDn?: number;
  lastExitReason?: string;
}

export type BranchCoverageObligation =
  | 'SINGLE_WITNESS'
  | 'FULL_COVERAGE'
  | 'UNDECIDED_OR_WIN_SINGLE_LOSS_ALL'
  | 'UNDECIDED_AND_WIN_ALL_LOSS_SINGLE';

export interface BranchCoverageSnapshot {
  path: string;
  movesFromRoot: number[];
  movesFromRootSgf: string[];
  depth: number;
  isOrNode: boolean;
  nodeRole: 'OR_ATTACKER' | 'AND_DEFENDER';
  coverageObligation: BranchCoverageObligation;
  obligation: 'EXISTENTIAL_OR' | 'UNIVERSAL_AND';
  toPlay: Color;
  runSource: 'original_root' | 'standalone_subposition';
  rootOutcome: ProofOutcome;
  nodeOutcome: ProofOutcome;
  nodeDagNodeId: number;
  terminalEvidence: string;
  lastPn: number;
  lastDn: number;
  lastThPn: number;
  lastThDn: number;
  lastExitReason: string;
  wideningLevel: number;
  windowSize: number;
  totalLegalMoves: number;
  closedCount: number;
  provenSourceCount: number;
  ttReplayedCount: number;
  rzRevalidatedCount: number;
  deferredOutsideRzCount: number;
  expandedUnresolvedCount: number;
  unexpandedCount: number;
  koBarrierCount: number;
  representativeMoveSgf: string | null;
  representativeDagNodeId: number | null;
  representativeRzSize: number;
  moves: BranchMoveCoverageEntry[];
}

export interface SubproofSourceReceipt {
  status: 'SOURCE_VERIFIED' | 'UNCLOSED' | 'VERIFICATION_FAILED';
  passed: boolean;
  errorCode: string;
  message: string;
  scope: 'subproof_fragment';
  verificationMode: LProofEncodingMode;
  targetPathSgf: string[];
  targetDagNodeId: number;
  outcome: ProofOutcome;
  verifiedNodes: number;
  verifiedLeaves: number;
  verifiedUniversals: number;
  replayedPruned: number;
  replayedTt: number;
  failedNodeId: number | null;
}

export interface SubproofQueryReplayReceipt {
  status: 'QUERY_REPLAY_VERIFIED' | 'QUERY_REPLAY_FAILED' | 'NOT_REQUESTED';
  passed: boolean;
  errorCode: string;
  message: string;
  sourceDagNodeId: number;
  queryPathSgf: string[];
  queryHistoryLength: number;
}

export interface SubproofFragmentVerificationResult {
  runSource: 'original_root' | 'standalone_subposition';
  runStartPathSgf: string[];
  runRootOutcome: ProofOutcome;
  originalRootOutcome: ProofOutcome | null;
  sourceReceipt: SubproofSourceReceipt;
  queryReplayReceipt: SubproofQueryReplayReceipt;
}

export interface SolverConfig {
  maxNodes: number;
  maxDepth: number;
  memoryBudgetMb: number;
  ttMode: 'board-tt' | 'pattern-tt';
  enableRzPruning: boolean;
  enableFastCaptureOrdering: boolean;
  enableProgressiveWidening: boolean;
  wideningBaseK: number;
  deterministicMode: boolean; // FR-7.8, NFR-4
  koRule: KoRule;
  attackerAllowKo: boolean;
  defenderAllowKo: boolean;
  useProblemDefaultKo?: boolean;
  /** Default-off generic path observer filters (e.g. ["", "rr", "rr/rp"]). */
  tracePathFilters?: string[];
  /** Default-off read-only callback receiving path trace events when tracePathFilters matches. */
  onPathTrace?: (event: SearchPathTraceEvent) => void;
  /** Optional extra paths (e.g. ["sr/pass", "rr/rp"]) to include in branchCoverageSnapshots. */
  coveragePathFilters?: string[];
}

export interface PrunedCertificateRecord {
  queryStateId: number;
  queryHistoryId: number;
  sourceStateId: number;
  sourceHistoryId: number;
  sourceProofNodeId: number;
  contextId: string;
  prunedMove: number;
  representativeMove: number;
  certificateRzCoords: number[];
  reason: 'OutsideRZRevalidated';
}

export interface ProofDagNode {
  nodeId: number;
  stateId: number;
  historyId: number;
  parentStateId: number;
  isOrNode: boolean;
  toPlay: Color;
  incomingMove: number;
  incomingMoveSgf: string;
  pn: number;
  dn: number;
  outcome: ProofOutcome;
  terminalEvidence: string;
  isPrunedOutsideRz: boolean;
  isTtHit: boolean;
  isKoDependentBarrier: boolean;
  sourceProofNodeId: number | null;
  proofRzCoords: number[];
  disproofRzCoords: number[];
  childNodeIds: number[];
  childMoves: number[];
  prunedCertificate?: PrunedCertificateRecord;
}

export interface StateTableEntry {
  stateId: number;
  parentStateId: number;
  moveFromParent: number;
  toPlay: Color;
  koPoint: number;
  consecutivePasses: number;
  survivingTokensMask: number;
  zobristHex: string;
  blackCoords: number[];
  whiteCoords: number[];
  historyId: number;
}

export interface SolveReport {
  problemId: string;
  problemTitle: string;
  boardSize: number;
  firstToPlay: Color;
  blackInitialCoords: number[];
  whiteInitialCoords: number[];
  immortalWallCoords: number[];
  hasRegionHint?: boolean;
  regionCoords: number[];
  rawRegionPointCount?: number;
  isFullRegionSearch?: boolean;
  inputHash: string;
  configFingerprint: string;
  solverVersion: string;
  rootStatus: ProofOutcome;
  unknownReason: UnknownReason | null;
  rootPn: number;
  rootDn: number;
  bestMove: number;
  bestMoveSgf: string | null;
  numNodes: number;
  timeMs: number;
  boardTtHits: number;
  patternTtHits: number;
  patternProofReusableHits: number;
  ghiRejectedCount: number;
  prunedOutsideRzCount: number;
  wideningUpgrades: number;
  cycleDetections: number;
  koDependentRejections: number;
  rzSizeAtRoot: number;
  resourceExhausted: boolean;
  artifactsComplete: boolean;
  rootProofRzCoords: number[];
  rootDisproofRzCoords: number[];
  bensonAliveCoords: number[];
  branchCoverageSnapshots?: BranchCoverageSnapshot[];
  eyeTopologyRegions: {
    regionId: number;
    coords: number[];
    topology: EyeTopologyType;
    enclosingColor: Color;
    vitalPoints: number[];
  }[];
  principalVariation: {
    move: number;
    sgf: string;
    color: Color;
    comment: string;
  }[];
  proofDagNodes: ProofDagNode[];
  stateTable: StateTableEntry[];
  historyTable: CanonicalSnapshot[][];
  rootDagNodeId: number;
  proofChecksum: string;
  sgfContent: string;
  sgfChecksum: string;
  lproofJson: string;
  resultJson: string;
}

export type VerificationScope =
  | 'original_root'
  | 'traced_within_rules'
  | 'free_exploration';

export type LProofEncodingMode = 'full_state_table' | 'compact_dag';

export interface VerificationReport {
  passed: boolean;
  schemaVersion: string;
  jcsSha256Checksum: string;
  canonicalDagChecksum?: string;
  encodingMode?: LProofEncodingMode;
  verifiedScope?: VerificationScope;
  verifiedRootKind?: 'initial' | 'traced_subposition';
  verifiedGoal?: SearchGoal;
  verifiedAttackerAllowKo?: boolean;
  verifiedDefenderAllowKo?: boolean;
  traceOutsideRegion?: boolean;
  traceHasRestrictedKoCapture?: boolean;
  verifiedNodes: number;
  verifiedStates: number;
  verifiedHistories: number;
  replayedPrunedCertificates: number;
  replayedTtHits: number;
  failedNodeId: number | null;
  errorCode: string;
  message: string;
  auditChecks: {
    checkId: string;
    requirementRef: string;
    title: string;
    passed: boolean;
    detail: string;
  }[];
}

export interface FailureDiagnosisSpec {
  category: string;
  rootCause: string;
  improvementMethod: string;
  targetCppModule: string;
  estimatedSpeedup: string;
}

export interface TsumegoProblemSpec {
  id: string;
  title: string;
  subtitle: string;
  source: string;
  difficulty: string;
  boardSize: number;
  viewportRows: [number, number];
  viewportCols: [number, number];
  maskedSgfStr: string;
  winningColor: 'B' | 'W';
  turnColor: 'B' | 'W';
  blackSearchGoal: SearchGoal;
  whiteSearchGoal: SearchGoal;
  blackCrucialStone: string;
  whiteCrucialStone: string;
  defaultAllowKo: boolean;
  attackerAllowKo?: boolean;
  defenderAllowKo?: boolean;
  hasRegionHint?: boolean;
  regionCoords: number[];
  rawRegionCoords?: number[];
  attentionCoords?: number[];
  blackInitialCoords: number[];
  whiteInitialCoords: number[];
  immortalWallCoords: number[];
  description: string;
  expectedOutcome: ProofOutcome;
  expectedBestMoveSgf: string;
  datasetGroup?: 'study-ld-rz' | 'srs-benchmark';
  rawJsonFilename?: string;
  groundTruthFirstMoves?: string[];
  verifiedGroundTruthFirstMoves?: string[];
  refutationFirstMoves?: string[];
  groundTruthNote?: string;
  d8SymmetryAudit?: {
    d8Index: number;
    matchedStones: number;
    totalRawStones: number;
    missingInMaskedSgf: string[];
    extraInMaskedRegion: string[];
    isExactBijection: boolean;
  };
  referencePv?: {
    move: number;
    sgf: string;
    color: Color;
    comment: string;
  }[];
  failureDiagnosis?: FailureDiagnosisSpec;
}

