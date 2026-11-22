// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// TypeScript 1:1 execution mirror of src/proof/proof_checker.cc (FR-8.1..8.4, FR-9.1..9.3).
// Strict Architectural Invariant: ProofArtifactManager NEVER imports or invokes DfpnSolver.
// Performs zero-trust state reconstruction from `initialPos`, independent Benson UCA / token
// terminal evaluation, complete legal-move coverage verification at universal nodes, and full
// recursive semantic replay of every OutsideRZRevalidated / TT-reuse certificate.

import { BensonTerminalEvaluator } from './bensonUca';
import { coordToSgf, GoPosition, PASS_MOVE } from './position';
import {
  CanonicalSnapshot,
  Color,
  KoRule,
  LogicalOp,
  LProofEncodingMode,
  NULL_MOVE,
  oppositeColor,
  PN_DN_SATURATION,
  ProofContext,
  ProofDagNode,
  ProofOutcome,
  SearchGoal,
  SolveReport,
  StateTableEntry,
  SubproofFragmentVerificationResult,
  SubproofQueryReplayReceipt,
  SubproofSourceReceipt,
  TerminalStatus,
  TsumegoProblemSpec,
  VerificationReport,
  VerificationScope,
} from './types';

// Standard FIPS 180-4 SHA-256 round constants
const SHA256_K = new Uint32Array([
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
  0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
  0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
  0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
  0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
  0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]);

function rotr32(x: number, n: number): number {
  return (x >>> n) | (x << (32 - n));
}

/**
 * Pure synchronous FIPS 180-4 SHA-256 hex digest over UTF-8 bytes.
 */
export function sha256Hex(input: string): string {
  const utf8 = new TextEncoder().encode(input);
  const bitLen = utf8.length * 8;
  const totalBytes = Math.ceil((utf8.length + 9) / 64) * 64;
  const padded = new Uint8Array(totalBytes);
  padded.set(utf8);
  padded[utf8.length] = 0x80;

  const view = new DataView(padded.buffer);
  const hiBits = Math.floor(bitLen / 0x100000000);
  const loBits = bitLen >>> 0;
  view.setUint32(totalBytes - 8, hiBits, false);
  view.setUint32(totalBytes - 4, loBits, false);

  let h0 = 0x6a09e667;
  let h1 = 0xbb67ae85;
  let h2 = 0x3c6ef372;
  let h3 = 0xa54ff53a;
  let h4 = 0x510e527f;
  let h5 = 0x9b05688c;
  let h6 = 0x1f83d9ab;
  let h7 = 0x5be0cd19;

  const w = new Uint32Array(64);
  for (let offset = 0; offset < totalBytes; offset += 64) {
    for (let i = 0; i < 16; i++) {
      w[i] = view.getUint32(offset + i * 4, false);
    }
    for (let i = 16; i < 64; i++) {
      const s0 = rotr32(w[i - 15], 7) ^ rotr32(w[i - 15], 18) ^ (w[i - 15] >>> 3);
      const s1 = rotr32(w[i - 2], 17) ^ rotr32(w[i - 2], 19) ^ (w[i - 2] >>> 10);
      w[i] = (w[i - 16] + s0 + w[i - 7] + s1) >>> 0;
    }

    let a = h0;
    let b = h1;
    let c = h2;
    let d = h3;
    let e = h4;
    let f = h5;
    let g = h6;
    let h = h7;

    for (let i = 0; i < 64; i++) {
      const S1 = rotr32(e, 6) ^ rotr32(e, 11) ^ rotr32(e, 25);
      const ch = (e & f) ^ (~e & g);
      const temp1 = (h + S1 + ch + SHA256_K[i] + w[i]) >>> 0;
      const S0 = rotr32(a, 2) ^ rotr32(a, 13) ^ rotr32(a, 22);
      const maj = (a & b) ^ (a & c) ^ (b & c);
      const temp2 = (S0 + maj) >>> 0;

      h = g;
      g = f;
      f = e;
      e = (d + temp1) >>> 0;
      d = c;
      c = b;
      b = a;
      a = (temp1 + temp2) >>> 0;
    }

    h0 = (h0 + a) >>> 0;
    h1 = (h1 + b) >>> 0;
    h2 = (h2 + c) >>> 0;
    h3 = (h3 + d) >>> 0;
    h4 = (h4 + e) >>> 0;
    h5 = (h5 + f) >>> 0;
    h6 = (h6 + g) >>> 0;
    h7 = (h7 + h) >>> 0;
  }

  return [h0, h1, h2, h3, h4, h5, h6, h7]
    .map((v) => v.toString(16).padStart(8, '0'))
    .join('');
}

/**
 * RFC 8785 JSON Canonicalization Scheme (JCS) deterministic serializer.
 */
export function canonicalizeJsonJcs(value: unknown): string {
  if (value === null) return 'null';
  const t = typeof value;
  if (t === 'number') {
    return Number.isFinite(value as number) ? String(value) : 'null';
  }
  if (t === 'boolean') {
    return (value as boolean) ? 'true' : 'false';
  }
  if (t === 'string') {
    return JSON.stringify(value);
  }
  if (t !== 'object') {
    return 'null';
  }
  if (Array.isArray(value)) {
    const len = value.length;
    if (len === 0) return '[]';
    // Fast path for integer arrays (stone coords, childMoves, childNodeIds)
    if (typeof value[0] === 'number') {
      let allFiniteNumbers = true;
      for (let i = 0; i < len; i++) {
        if (typeof value[i] !== 'number' || !Number.isFinite(value[i])) {
          allFiniteNumbers = false;
          break;
        }
      }
      if (allFiniteNumbers) {
        return `[${(value as number[]).join(',')}]`;
      }
    }
    const parts: string[] = new Array(len);
    for (let i = 0; i < len; i++) {
      const item = value[i];
      parts[i] = item === undefined ? 'null' : canonicalizeJsonJcs(item);
    }
    return `[${parts.join(',')}]`;
  }
  const obj = value as Record<string, unknown>;
  const keys = Object.keys(obj)
    .filter((k) => obj[k] !== undefined)
    .sort();
  const kLen = keys.length;
  if (kLen === 0) return '{}';
  const parts: string[] = new Array(kLen);
  for (let i = 0; i < kLen; i++) {
    const k = keys[i];
    parts[i] = `${JSON.stringify(k)}:${canonicalizeJsonJcs(obj[k])}`;
  }
  return `{${parts.join(',')}}`;
}

function numberArraysEqual(a: number[], b: number[]): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) return false;
  }
  return true;
}

function historyTablesMatch(
  claimed: CanonicalSnapshot[] | undefined,
  rebuilt: CanonicalSnapshot[]
): boolean {
  if (!claimed || claimed.length !== rebuilt.length) return false;
  for (let i = 0; i < rebuilt.length; i++) {
    const c = claimed[i];
    const r = rebuilt[i];
    if (
      c.toPlay !== r.toPlay ||
      c.zobristHex !== r.zobristHex ||
      !numberArraysEqual(c.blackCoords, r.blackCoords) ||
      !numberArraysEqual(c.whiteCoords, r.whiteCoords)
    ) {
      return false;
    }
  }
  return true;
}

function decodeSatNumber(val: unknown): number {
  if (val === 'SAT') return PN_DN_SATURATION;
  if (typeof val === 'number' && Number.isFinite(val)) return val;
  return -1;
}

function encodeColorStr(c: Color): 'B' | 'W' {
  return c === Color.White ? 'W' : 'B';
}

function decodeColor(val: unknown): Color | null {
  if (val === 'B' || val === 'b' || val === Color.Black) return Color.Black;
  if (val === 'W' || val === 'w' || val === Color.White) return Color.White;
  return null;
}

function isIntegerArray(val: unknown): val is number[] {
  if (!Array.isArray(val)) return false;
  for (let i = 0; i < val.length; i++) {
    if (typeof val[i] !== 'number' || !Number.isInteger(val[i])) return false;
  }
  return true;
}

function sortedUniqueNumbers(arr: number[]): number[] {
  return Array.from(new Set(arr)).sort((a, b) => a - b);
}

function moveToCanonicalSgf(mv: number, boardSize: number): string {
  if (mv === PASS_MOVE) return 'pass';
  if (mv < 0 || mv >= boardSize * boardSize) return '';
  return coordToSgf(mv, boardSize);
}

function stringHasLoneSurrogate(s: string): boolean {
  for (let i = 0; i < s.length; i++) {
    const cu = s.charCodeAt(i);
    if (cu >= 0xd800 && cu <= 0xdbff) {
      if (i + 1 >= s.length) return true;
      const next = s.charCodeAt(i + 1);
      if (next < 0xdc00 || next > 0xdfff) return true;
      i++;
    } else if (cu >= 0xdc00 && cu <= 0xdfff) {
      return true;
    }
  }
  return false;
}

function jsonHasLoneSurrogate(val: unknown): boolean {
  if (typeof val === 'string') return stringHasLoneSurrogate(val);
  if (Array.isArray(val)) {
    for (let i = 0; i < val.length; i++) {
      if (jsonHasLoneSurrogate(val[i])) return true;
    }
    return false;
  }
  if (val && typeof val === 'object') {
    const obj = val as Record<string, unknown>;
    for (const k of Object.keys(obj)) {
      if (stringHasLoneSurrogate(k) || jsonHasLoneSurrogate(obj[k])) {
        return true;
      }
    }
  }
  return false;
}

function resolveReportRegion(report: SolveReport): {
  hasRegionHint: boolean;
  regionCoords: number[];
  regionMask: number[] | null;
  regionSet: Set<number> | null;
} {
  const rawCoords = sortedUniqueNumbers(report.regionCoords ?? []);
  const hasRegionHint =
    report.hasRegionHint !== undefined
      ? report.hasRegionHint
      : rawCoords.length > 0;
  const regionCoords = hasRegionHint ? rawCoords : [];
  return {
    hasRegionHint,
    regionCoords,
    regionMask: hasRegionHint ? regionCoords : null,
    regionSet: hasRegionHint ? new Set<number>(regionCoords) : null,
  };
}

function isValidSnapshotShape(s: unknown): s is CanonicalSnapshot {
  if (!s || typeof s !== 'object' || Array.isArray(s)) return false;
  const obj = s as Record<string, unknown>;
  return (
    isIntegerArray(obj.blackCoords) &&
    isIntegerArray(obj.whiteCoords) &&
    decodeColor(obj.toPlay) !== null &&
    typeof obj.zobristHex === 'string'
  );
}

function normalizeSnapshot(s: Record<string, unknown>): CanonicalSnapshot {
  return {
    blackCoords: s.blackCoords as number[],
    whiteCoords: s.whiteCoords as number[],
    toPlay: decodeColor(s.toPlay)!,
    zobristHex: s.zobristHex as string,
  };
}

/**
 * Formats JSON with 2-space object indentation while keeping primitive arrays
 * (e.g. stone coordinate lists and child IDs) on a single line, matching C++ PrettyPrintJson.
 */
function formatCompactPrettyJson(value: unknown, indent = 0): string {
  if (value === null || typeof value !== 'object') {
    return JSON.stringify(value);
  }
  const pad = ' '.repeat(indent);
  const innerPad = ' '.repeat(indent + 2);
  if (Array.isArray(value)) {
    if (value.length === 0) return '[]';
    let allScalar = true;
    for (let i = 0; i < value.length; i++) {
      const item = value[i];
      if (item !== null && typeof item === 'object') {
        allScalar = false;
        break;
      }
    }
    if (allScalar) {
      return `[${value
        .map((item) => (item === undefined ? 'null' : JSON.stringify(item)))
        .join(', ')}]`;
    }
    const lines: string[] = new Array(value.length);
    for (let i = 0; i < value.length; i++) {
      const item = value[i] === undefined ? null : value[i];
      lines[i] = `${innerPad}${formatCompactPrettyJson(item, indent + 2)}`;
    }
    return `[\n${lines.join(',\n')}\n${pad}]`;
  }
  const obj = value as Record<string, unknown>;
  const keys = Object.keys(obj).filter((k) => obj[k] !== undefined);
  if (keys.length === 0) return '{}';
  const entries: string[] = new Array(keys.length);
  for (let i = 0; i < keys.length; i++) {
    const k = keys[i];
    entries[i] = `${innerPad}${JSON.stringify(k)}: ${formatCompactPrettyJson(
      obj[k],
      indent + 2
    )}`;
  }
  return `{\n${entries.join(',\n')}\n${pad}}`;
}

/**
 * Standalone, zero-solver-dependency derivation of a problem's canonical default ProofContext.
 * Used by `verifySerializedLProofJson(json, { problem })` so binding to an external problem
 * automatically verifies goal, crucial stones, logical operator, and default ko permissions
 * without ever importing `DfpnSolver`.
 */
export function deriveDefaultProofContextFromProblem(
  problem: TsumegoProblemSpec,
  koRule: KoRule = KoRule.SituationalSuperko
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
  else if (crucialExpr.includes('|') || crucialExpr.includes(',')) {
    crucialOp = LogicalOp.Disjunction;
  }

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

  const attackerAllowKo = Boolean(
    problem.attackerAllowKo ?? problem.defaultAllowKo
  );
  const defenderAllowKo = problem.defenderAllowKo ?? true;

  return {
    contextId: `ctx_${problem.id}_${koRule}_${attackerGoal}_ako${
      attackerAllowKo ? 1 : 0
    }_dko${defenderAllowKo ? 1 : 0}`,
    rootAttacker,
    attackerGoal,
    crucialStoneOp: crucialOp,
    koRule,
    attackerAllowKo,
    defenderAllowKo,
    initialTokens,
  };
}

export class ProofArtifactManager {
  // FR-8.3: Serialize self-contained canonical lproof/1 JSON DAG with RFC 8785 JCS SHA-256 checksum
  public serializeLProofJson(
    initialPos: GoPosition,
    context: ProofContext,
    report: SolveReport
  ): { json: string; checksum: string } {
    const immortalWallCoords = Array.from(initialPos.immortalWallSet).sort(
      (a, b) => a - b
    );
    const { hasRegionHint, regionCoords } = resolveReportRegion(report);
    const isTracedSubposition = initialPos.playedMoveTrace.length > 0;

    // Losslessly deduplicate CanonicalSnapshots across historyTable via snapshotPool
    const snapshotPool: CanonicalSnapshot[] = [];
    const snapshotIndexByKey = new Map<string, number>();
    const historySnapshotIds: number[][] = report.historyTable.map((snaps) =>
      snaps.map((s) => {
        const key = `${s.toPlay}:${s.zobristHex}:${s.blackCoords.join(
          ','
        )}/${s.whiteCoords.join(',')}`;
        let idx = snapshotIndexByKey.get(key);
        if (idx === undefined) {
          idx = snapshotPool.length;
          snapshotIndexByKey.set(key, idx);
          snapshotPool.push(s);
        }
        return idx;
      })
    );

    const problemSetup: Record<string, unknown> = {
      boardSize: initialPos.boardSize,
      rootKind: isTracedSubposition ? 'traced_subposition' : 'initial',
      firstToPlay: encodeColorStr(initialPos.toPlay),
      koPoint: initialPos.koPoint,
      consecutivePasses: initialPos.consecutivePasses,
      survivingTokensMask: initialPos.survivingTargetTokensMask,
      zobristHex: initialPos.computeZobristHex(),
      inputHash: report.inputHash,
      blackInitialCoords: initialPos.getBlackCoords(),
      whiteInitialCoords: initialPos.getWhiteCoords(),
      immortalWallCoords,
      hasRegionHint,
      regionCoords,
      rawRegionPointCount: report.rawRegionPointCount ?? regionCoords.length,
      isFullRegionSearch: report.isFullRegionSearch ?? true,
    };

    if (isTracedSubposition) {
      problemSetup.originFirstToPlay = encodeColorStr(initialPos.originToPlay);
      problemSetup.originBlackCoords = initialPos.originBlackCoords.slice();
      problemSetup.originWhiteCoords = initialPos.originWhiteCoords.slice();
      problemSetup.initialTraceMoves = initialPos.playedMoveTrace.slice();
    }

    const payloadWithoutChecksum = {
      magic: 'lproof/1',
      encodingMode: 'full_state_table' as LProofEncodingMode,
      problemId: report.problemId,
      context: {
        contextId: context.contextId,
        rootAttacker: encodeColorStr(context.rootAttacker),
        attackerGoal: context.attackerGoal,
        crucialStoneOp: context.crucialStoneOp,
        koRule: context.koRule,
        attackerAllowKo: context.attackerAllowKo,
        defenderAllowKo: context.defenderAllowKo,
        initialTokens: context.initialTokens.map((t) => ({
          tokenId: t.tokenId,
          initialCoord: t.initialCoord,
          groupIndex: t.groupIndex,
          stoneColor: encodeColorStr(t.stoneColor),
        })),
      },
      problemSetup,
      rootNode: report.rootDagNodeId,
      rootOutcome: report.rootStatus,
      rootPn: report.rootPn >= PN_DN_SATURATION ? 'SAT' : report.rootPn,
      rootDn: report.rootDn >= PN_DN_SATURATION ? 'SAT' : report.rootDn,
      bestMove: report.bestMove,
      bestMoveSgf: report.bestMoveSgf,
      stateTable: report.stateTable,
      snapshotPool,
      historySnapshotIds,
      nodes: report.proofDagNodes.map((n) => ({
        nodeId: n.nodeId,
        stateId: n.stateId,
        historyId: n.historyId,
        parentStateId: n.parentStateId,
        isOrNode: n.isOrNode,
        toPlay: encodeColorStr(n.toPlay),
        incomingMove: n.incomingMove,
        incomingMoveSgf: n.incomingMoveSgf,
        pn: n.pn >= PN_DN_SATURATION ? 'SAT' : n.pn,
        dn: n.dn >= PN_DN_SATURATION ? 'SAT' : n.dn,
        outcome: n.outcome,
        terminalEvidence: n.terminalEvidence,
        isPrunedOutsideRz: n.isPrunedOutsideRz,
        isTtHit: n.isTtHit,
        isKoDependentBarrier: n.isKoDependentBarrier,
        sourceProofNodeId: n.sourceProofNodeId,
        proofRzCoords: n.proofRzCoords,
        disproofRzCoords: n.disproofRzCoords,
        childNodeIds: n.childNodeIds,
        childMoves: n.childMoves,
        prunedCertificate: n.prunedCertificate ?? null,
      })),
    };

    const jcsCanonicalBody = canonicalizeJsonJcs(payloadWithoutChecksum);
    const checksum = `sha256-jcs:${sha256Hex(jcsCanonicalBody)}`;

    const fullObject = {
      ...payloadWithoutChecksum,
      checksum,
    };

    return {
      json: `${formatCompactPrettyJson(fullObject, 0)}\n`,
      checksum,
    };
  }

  // FR-8.1: Serialize result_<problem>.json
  public serializeResultJson(report: SolveReport): string {
    const resultPayload = {
      ProblemId: report.problemId,
      InputHash: report.inputHash,
      ConfigFingerprint: report.configFingerprint,
      SolverVersion: report.solverVersion,
      RootStatus: report.rootStatus,
      UnknownReason: report.unknownReason,
      RootPn: report.rootPn,
      RootDn: report.rootDn,
      BestMove: report.bestMoveSgf,
      NumNodes: report.numNodes,
      TimeMs: report.timeMs,
      Time: Number((report.timeMs / 1000).toFixed(4)),
      RegionPointCount: report.regionCoords?.length ?? 0,
      RawRegionPointCount:
        report.rawRegionPointCount ?? (report.regionCoords?.length ?? 0),
      IsFullRegionSearch: report.isFullRegionSearch ?? true,
      BoardTTHits: report.boardTtHits,
      PatternTTHits: report.patternTtHits,
      PatternProofReusable: report.patternProofReusableHits,
      NumGhiRejected: report.ghiRejectedCount,
      NumPrunedOutsideRZ: report.prunedOutsideRzCount,
      NumWideningUpgrades: report.wideningUpgrades,
      NumCycleDetections: report.cycleDetections,
      RZSizeAtRoot: report.rzSizeAtRoot,
      ResourceExhausted: report.resourceExhausted,
      ArtifactsComplete: report.artifactsComplete,
      ProofFile: `proof_${report.problemId}.json`,
      ProofChecksum: report.proofChecksum,
      SgfFile: `uct_tree_${report.problemId}.sgf`,
      SgfChecksum: report.sgfChecksum,
    };
    return JSON.stringify(resultPayload, null, 2);
  }

  // FR-8.2: Export uct_tree_<problem>.sgf with RZ color coding
  public exportSolutionTreeSgf(
    initialPos: GoPosition,
    context: ProofContext,
    report: SolveReport
  ): { sgf: string; checksum: string } {
    const sz = initialPos.boardSize;
    const ab = initialPos
      .getBlackCoords()
      .map((c) => `[${coordToSgf(c, sz)}]`)
      .join('');
    const aw = initialPos
      .getWhiteCoords()
      .map((c) => `[${coordToSgf(c, sz)}]`)
      .join('');

    const rzMarks = report.rootProofRzCoords
      .map((c) => `[${coordToSgf(c, sz)}]`)
      .join('');

    let pvSgf = '';
    for (const step of report.principalVariation) {
      const colChar = step.color === Color.Black ? 'B' : 'W';
      const moveStr = step.move === PASS_MOVE ? '' : step.sgf;
      pvSgf += `;${colChar}[${moveStr}]C[${step.comment}]`;
    }

    const sgf = `(;GM[1]FF[4]CA[UTF-8]AP[LDProver:1.8.2]SZ[${sz}]PL[${
      initialPos.toPlay === Color.Black ? 'B' : 'W'
    }]${ab ? `AB${ab}` : ''}${aw ? `AW${aw}` : ''}${
      rzMarks ? `TR${rzMarks}` : ''
    }C[LDProver v1.8.2 | RootStatus=${report.rootStatus} | PN=${
      report.rootPn
    } DN=${report.rootDn} | RZSizeAtRoot=${report.rzSizeAtRoot} | Goal=${
      context.attackerGoal
    }]${pvSgf})`;

    return {
      sgf,
      checksum: `sha256-sgf:${sha256Hex(sgf)}`,
    };
  }

  /**
   * Standalone process-independent verifier that reconstructs ALL problem assumptions,
   * initial board (or traced sub-position), context, states, histories, and DAG solely from a
   * serialized `.lproof.json` file string without requiring any in-memory solver objects.
   * Supports both full-table TS exports and compact DAG-only C++ exports under the unified
   * `lproof/1` protocol, plus optional binding against an external `expectedProblem`.
   */
  public verifySerializedLProofJson(
    lproofJsonText: string,
    expectedBinding?: {
      problem?: TsumegoProblemSpec;
      context?: ProofContext;
      koRule?: KoRule;
      scope?: VerificationScope;
    }
  ): VerificationReport {
    const makeJsonError = (
      errorCode: string,
      message: string,
      detail: string,
      schemaVersion = 'lproof/1',
      checksum = '',
      extra?: Partial<VerificationReport>
    ): VerificationReport => ({
      passed: false,
      schemaVersion,
      jcsSha256Checksum: checksum,
      verifiedNodes: 0,
      verifiedStates: 0,
      verifiedHistories: 0,
      replayedPrunedCertificates: 0,
      replayedTtHits: 0,
      failedNodeId: null,
      errorCode,
      message,
      auditChecks: [
        {
          checkId: 'CHK-01',
          requirementRef: 'FR-8.3 / FR-9.1',
          title: 'lproof/1 独立文件结构与完整性质检',
          passed: false,
          detail,
        },
      ],
      ...extra,
    });

    let rawParsed: unknown;
    try {
      rawParsed = JSON.parse(lproofJsonText);
    } catch (err) {
      return makeJsonError(
        'LP-J01',
        `JSON 解析失败: ${err instanceof Error ? err.message : String(err)}`,
        'Malformed JSON payload.'
      );
    }

    if (jsonHasLoneSurrogate(rawParsed)) {
      return makeJsonError(
        'LP-J01',
        'JSON 包含非法孤立 UTF-16 代理项 (lone surrogate)，违反 RFC 8259 / RFC 8785 Unicode 标量规范。',
        'JSON contains unpaired UTF-16 surrogate code unit.'
      );
    }

    // Fail-closed guard BEFORE accessing ANY property on parsed (R3 F6.1: rejects null/arrays/primitives)
    if (!rawParsed || typeof rawParsed !== 'object' || Array.isArray(rawParsed)) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 根载荷必须为 JSON 对象（拒绝 null、数组或原始标量）。',
        'Top-level JSON value is not a plain object.',
        'unknown'
      );
    }

    const parsed = rawParsed as Record<string, unknown>;
    const hasStateTable = Array.isArray(parsed.stateTable);
    const hasPooledHistory =
      Array.isArray(parsed.snapshotPool) &&
      Array.isArray(parsed.historySnapshotIds);
    const hasInlineHistory = Array.isArray(parsed.historyTable);
    const declaredEncodingMode =
      typeof parsed.encodingMode === 'string' ? parsed.encodingMode : undefined;

    if (
      declaredEncodingMode !== undefined &&
      declaredEncodingMode !== 'full_state_table' &&
      declaredEncodingMode !== 'compact_dag'
    ) {
      return makeJsonError(
        'LP-J02',
        `lproof/1 非法 encodingMode="${declaredEncodingMode}"。`,
        'Invalid encodingMode field.',
        String(parsed.magic ?? 'unknown'),
        typeof parsed.checksum === 'string' ? parsed.checksum : ''
      );
    }

    if (
      (declaredEncodingMode === 'full_state_table' && !hasStateTable) ||
      (declaredEncodingMode === 'compact_dag' && hasStateTable)
    ) {
      return makeJsonError(
        'LP-J02',
        `lproof/1 encodingMode="${declaredEncodingMode}" 与 stateTable 存在性冲突。`,
        'encodingMode contradicts stateTable presence.',
        String(parsed.magic ?? 'unknown'),
        typeof parsed.checksum === 'string' ? parsed.checksum : ''
      );
    }

    const encodingMode: LProofEncodingMode = hasStateTable
      ? 'full_state_table'
      : 'compact_dag';

    if (
      parsed.magic !== 'lproof/1' ||
      typeof parsed.checksum !== 'string' ||
      !parsed.context ||
      typeof parsed.context !== 'object' ||
      Array.isArray(parsed.context) ||
      !parsed.problemSetup ||
      typeof parsed.problemSetup !== 'object' ||
      Array.isArray(parsed.problemSetup) ||
      !Array.isArray(parsed.nodes) ||
      (hasStateTable && !hasPooledHistory && !hasInlineHistory)
    ) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 独立文件缺少必要字段（magic / checksum / context / problemSetup / nodes）或历史表缺失。',
        'Missing required top-level fields.',
        String(parsed.magic ?? 'unknown'),
        typeof parsed.checksum === 'string' ? parsed.checksum : ''
      );
    }

    const fileChecksum = parsed.checksum;
    const { checksum: _ignored, ...withoutChecksum } = parsed;
    void _ignored;
    const expectedChecksum = `sha256-jcs:${sha256Hex(
      canonicalizeJsonJcs(withoutChecksum)
    )}`;
    if (fileChecksum !== expectedChecksum) {
      return makeJsonError(
        'LP-C01',
        '独立文件 RFC 8785 JCS SHA-256 校验和不匹配，证书已被篡改。',
        `Expected=${expectedChecksum.slice(0, 28)}... Got=${fileChecksum.slice(
          0,
          28
        )}...`,
        'lproof/1',
        fileChecksum
      );
    }

    const rawCtx = parsed.context as Record<string, unknown>;
    const setup = parsed.problemSetup as Record<string, unknown>;

    const rootAttacker = decodeColor(rawCtx.rootAttacker);
    if (rootAttacker === null) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 context.rootAttacker 字段非法。',
        'Invalid rootAttacker.',
        'lproof/1',
        fileChecksum
      );
    }

    const attackerGoal =
      rawCtx.attackerGoal === SearchGoal.ToKill
        ? SearchGoal.ToKill
        : rawCtx.attackerGoal === SearchGoal.ToLive
        ? SearchGoal.ToLive
        : null;
    if (attackerGoal === null) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 context.attackerGoal 字段非法。',
        'Invalid attackerGoal.',
        'lproof/1',
        fileChecksum
      );
    }

    const decodeLogicalOp = (v: unknown): LogicalOp | null => {
      if (v === LogicalOp.Single || v === 0) return LogicalOp.Single;
      if (v === LogicalOp.Conjunction || v === 1) return LogicalOp.Conjunction;
      if (v === LogicalOp.Disjunction || v === 2) return LogicalOp.Disjunction;
      return null;
    };
    const crucialStoneOp = decodeLogicalOp(rawCtx.crucialStoneOp);
    if (crucialStoneOp === null) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 context.crucialStoneOp 字段非法。',
        'Invalid crucialStoneOp.',
        'lproof/1',
        fileChecksum
      );
    }

    const decodeKoRule = (v: unknown): KoRule | null => {
      if (v === KoRule.SituationalSuperko || v === 0) {
        return KoRule.SituationalSuperko;
      }
      if (v === KoRule.PositionalSuperko || v === 1) {
        return KoRule.PositionalSuperko;
      }
      if (v === KoRule.SimpleKoOnly || v === 'SIMPLE_KO' || v === 2) {
        return KoRule.SimpleKoOnly;
      }
      return null;
    };
    const koRule = decodeKoRule(rawCtx.koRule);
    if (koRule === null) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 context.koRule 字段非法。',
        'Invalid koRule.',
        'lproof/1',
        fileChecksum
      );
    }

    if (
      typeof rawCtx.attackerAllowKo !== 'boolean' ||
      typeof rawCtx.defenderAllowKo !== 'boolean' ||
      !Array.isArray(rawCtx.initialTokens)
    ) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 context 缺少合法的劫争权限或 initialTokens 数组。',
        'Invalid ko flags or initialTokens.',
        'lproof/1',
        fileChecksum
      );
    }

    const initialTokens: ProofContext['initialTokens'] = [];
    for (const rawTok of rawCtx.initialTokens) {
      if (!rawTok || typeof rawTok !== 'object' || Array.isArray(rawTok)) {
        return makeJsonError(
          'LP-J02',
          'lproof/1 initialTokens 条目格式非法。',
          'Malformed TargetToken.',
          'lproof/1',
          fileChecksum
        );
      }
      const tObj = rawTok as Record<string, unknown>;
      const tCol = decodeColor(tObj.stoneColor);
      if (
        typeof tObj.tokenId !== 'number' ||
        typeof tObj.initialCoord !== 'number' ||
        typeof tObj.groupIndex !== 'number' ||
        tCol === null
      ) {
        return makeJsonError(
          'LP-J02',
          'lproof/1 initialTokens 条目字段缺失或类型非法。',
          'Invalid TargetToken fields.',
          'lproof/1',
          fileChecksum
        );
      }
      initialTokens.push({
        tokenId: tObj.tokenId,
        initialCoord: tObj.initialCoord,
        groupIndex: tObj.groupIndex,
        stoneColor: tCol,
      });
    }

    const context: ProofContext = {
      contextId: String(rawCtx.contextId ?? ''),
      rootAttacker,
      attackerGoal,
      crucialStoneOp,
      koRule,
      attackerAllowKo: rawCtx.attackerAllowKo,
      defenderAllowKo: rawCtx.defenderAllowKo,
      initialTokens,
    };

    const boardSizeRaw =
      typeof setup.boardSize === 'number'
        ? setup.boardSize
        : typeof parsed.boardSize === 'number'
        ? parsed.boardSize
        : -1;
    if (boardSizeRaw !== 5 && boardSizeRaw !== 7 && boardSizeRaw !== 19) {
      return makeJsonError(
        'LP-J02',
        `lproof/1 非法棋盘尺寸 boardSize=${String(boardSizeRaw)}。`,
        'Invalid boardSize.',
        'lproof/1',
        fileChecksum
      );
    }
    const boardSize = boardSizeRaw;

    const firstToPlay = decodeColor(setup.firstToPlay);
    if (
      firstToPlay === null ||
      !isIntegerArray(setup.blackInitialCoords) ||
      !isIntegerArray(setup.whiteInitialCoords) ||
      !isIntegerArray(setup.immortalWallCoords) ||
      !isIntegerArray(setup.regionCoords)
    ) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 problemSetup 缺少合法的初始棋子/围墙/区域数组或 firstToPlay。',
        'Malformed problemSetup arrays.',
        'lproof/1',
        fileChecksum
      );
    }

    const blackInitialCoords = setup.blackInitialCoords;
    const whiteInitialCoords = setup.whiteInitialCoords;
    const immortalWallCoords = setup.immortalWallCoords;
    if (
      setup.hasRegionHint !== undefined &&
      typeof setup.hasRegionHint !== 'boolean'
    ) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 problemSetup.hasRegionHint 类型非法（必须为布尔值）。',
        'Invalid non-boolean problemSetup.hasRegionHint.',
        'lproof/1',
        fileChecksum
      );
    }
    const hasRegionHint =
      typeof setup.hasRegionHint === 'boolean'
        ? setup.hasRegionHint
        : setup.regionCoords.length > 0;
    if (!hasRegionHint && setup.regionCoords.length > 0) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 problemSetup 自相矛盾：hasRegionHint=false 时不允许携带非空 regionCoords。',
        'Contradictory hasRegionHint=false with non-empty regionCoords.',
        'lproof/1',
        fileChecksum
      );
    }
    const regionCoords = hasRegionHint ? setup.regionCoords : [];

    // Reconstruct active root position (R3 F3 & R4 §3 P1-A: explicit scope + trace rule enforcement!)
    const rawRootKind =
      typeof setup.rootKind === 'string' ? setup.rootKind : 'initial';
    if (rawRootKind !== 'initial' && rawRootKind !== 'traced_subposition') {
      return makeJsonError(
        'LP-J02',
        `未知的 problemSetup.rootKind="${rawRootKind}"。`,
        'Unsupported rootKind.',
        'lproof/1',
        fileChecksum
      );
    }
    const rootKind: 'initial' | 'traced_subposition' = rawRootKind;

    // Resolve verification proposition scope:
    // - When binding to an external problem without explicit scope, default strictly to `original_root`
    //   so a traced sub-position cannot masquerade as an original-problem proof!
    // - Otherwise, a standalone `traced_subposition` defaults to `traced_within_rules`.
    const effectiveScope: VerificationScope =
      expectedBinding?.scope ??
      (expectedBinding?.problem
        ? 'original_root'
        : rootKind === 'traced_subposition'
        ? 'traced_within_rules'
        : 'original_root');

    const scopeMeta: Partial<VerificationReport> = {
      encodingMode,
      verifiedScope: effectiveScope,
      verifiedRootKind: rootKind,
      verifiedGoal: context.attackerGoal,
      verifiedAttackerAllowKo: context.attackerAllowKo,
      verifiedDefenderAllowKo: context.defenderAllowKo,
    };

    if (effectiveScope === 'original_root' && rootKind !== 'initial') {
      return makeJsonError(
        'LP-P02',
        '原题命题校验模式 (original_root) 拒绝 traced_subposition 子局面证书；该证书仅证明给定到达轨迹后的子局面，不等价于原题初始命题。',
        'Rejected traced_subposition under original_root verification scope.',
        'lproof/1',
        fileChecksum,
        scopeMeta
      );
    }

    const initialPos = new GoPosition(context, boardSize, immortalWallCoords);
    let originBlackForBinding = blackInitialCoords;
    let originWhiteForBinding = whiteInitialCoords;
    let originToPlayForBinding = firstToPlay;
    let traceOutsideRegion = false;
    let traceHasRestrictedKoCapture = false;
    const regionSetForTrace =
      hasRegionHint ? new Set<number>(regionCoords) : null;

    if (rootKind === 'traced_subposition') {
      const originToPlay = decodeColor(setup.originFirstToPlay);
      if (
        originToPlay === null ||
        !isIntegerArray(setup.originBlackCoords) ||
        !isIntegerArray(setup.originWhiteCoords) ||
        !isIntegerArray(setup.initialTraceMoves) ||
        setup.initialTraceMoves.length === 0
      ) {
        return makeJsonError(
          'LP-J02',
          'traced_subposition 证书缺少合法的 originBlackCoords / originWhiteCoords / originFirstToPlay / initialTraceMoves。',
          'Incomplete traced_subposition provenance.',
          'lproof/1',
          fileChecksum,
          scopeMeta
        );
      }
      originBlackForBinding = setup.originBlackCoords;
      originWhiteForBinding = setup.originWhiteCoords;
      originToPlayForBinding = originToPlay;
      initialPos.setupInitialStones(
        setup.originBlackCoords,
        setup.originWhiteCoords,
        originToPlay
      );
      for (let i = 0; i < setup.initialTraceMoves.length; i++) {
        const tmv = setup.initialTraceMoves[i];
        const outsideRegion =
          tmv !== PASS_MOVE &&
          regionSetForTrace !== null &&
          !regionSetForTrace.has(tmv);
        if (outsideRegion) {
          traceOutsideRegion = true;
          if (effectiveScope === 'traced_within_rules') {
            return makeJsonError(
              'LP-S11',
              `traced_subposition 到达轨迹第 ${i + 1} 手 ${coordToSgf(
                tmv,
                boardSize
              )} (move=${tmv}) 超出题目声明的合法 region 集合。`,
              `Trace move ${tmv} at index ${i} lies outside declared region.`,
              'lproof/1',
              fileChecksum,
              {
                ...scopeMeta,
                traceOutsideRegion: true,
                traceHasRestrictedKoCapture,
              }
            );
          }
        }
        const sideToPlay = initialPos.toPlay;
        const restrictedSide =
          (sideToPlay === context.rootAttacker && !context.attackerAllowKo) ||
          (sideToPlay !== context.rootAttacker && !context.defenderAllowKo);
        const res = initialPos.playMove(tmv);
        if (!res.legal) {
          return makeJsonError(
            'LP-S09',
            `traced_subposition 到达轨迹第 ${i + 1} 手 move=${tmv} 在规则下非法。`,
            `Illegal move ${tmv} at trace index ${i}.`,
            'lproof/1',
            fileChecksum,
            scopeMeta
          );
        }
        if (res.isKoCapture && restrictedSide) {
          traceHasRestrictedKoCapture = true;
          if (effectiveScope === 'traced_within_rules') {
            return makeJsonError(
              'LP-S12',
              `traced_subposition 到达轨迹第 ${i + 1} 手 ${coordToSgf(
                tmv,
                boardSize
              )} 属于受限方禁劫提劫，在 traced_within_rules 范围内被拒绝。`,
              `Restricted-side ko capture at trace index ${i} rejected under traced_within_rules.`,
              'lproof/1',
              fileChecksum,
              {
                ...scopeMeta,
                traceOutsideRegion,
                traceHasRestrictedKoCapture: true,
              }
            );
          }
        }
      }
      // Verify traced replay matches declared sub-root setup 100%
      if (
        initialPos.toPlay !== firstToPlay ||
        !numberArraysEqual(
          initialPos.getBlackCoords(),
          sortedUniqueNumbers(blackInitialCoords)
        ) ||
        !numberArraysEqual(
          initialPos.getWhiteCoords(),
          sortedUniqueNumbers(whiteInitialCoords)
        ) ||
        (typeof setup.koPoint === 'number' &&
          initialPos.koPoint !== setup.koPoint) ||
        (typeof setup.consecutivePasses === 'number' &&
          initialPos.consecutivePasses !== setup.consecutivePasses) ||
        (typeof setup.survivingTokensMask === 'number' &&
          initialPos.survivingTargetTokensMask !== setup.survivingTokensMask) ||
        (typeof setup.zobristHex === 'string' &&
          initialPos.computeZobristHex() !== setup.zobristHex)
      ) {
        return makeJsonError(
          'LP-S02',
          'traced_subposition 重放结果与 problemSetup 声明的子根棋面/劫点/虚手/关键子掩码/Zobrist 不一致。',
          'Replayed traced sub-position diverges from declared problemSetup.',
          'lproof/1',
          fileChecksum,
          scopeMeta
        );
      }
    } else {
      // R5 §2: Contradictory `rootKind="initial"` with non-empty `initialTraceMoves` must be rejected!
      if (setup.initialTraceMoves !== undefined) {
        if (!isIntegerArray(setup.initialTraceMoves)) {
          return makeJsonError(
            'LP-J02',
            'initial 根证书包含非法非整数数组 initialTraceMoves。',
            'Malformed initialTraceMoves on initial root.',
            'lproof/1',
            fileChecksum,
            scopeMeta
          );
        }
        if (setup.initialTraceMoves.length > 0) {
          return makeJsonError(
            'LP-P02',
            '自相矛盾的根声明：rootKind="initial" 不允许携带非空 initialTraceMoves 前置轨迹。',
            'Contradictory initial root declares non-empty initialTraceMoves.',
            'lproof/1',
            fileChecksum,
            scopeMeta
          );
        }
      }
      initialPos.setupInitialStones(
        blackInitialCoords,
        whiteInitialCoords,
        firstToPlay
      );
      if (
        (typeof setup.koPoint === 'number' &&
          setup.koPoint !== initialPos.koPoint) ||
        (typeof setup.consecutivePasses === 'number' &&
          setup.consecutivePasses !== 0) ||
        (typeof setup.survivingTokensMask === 'number' &&
          setup.survivingTokensMask !== initialPos.survivingTargetTokensMask)
      ) {
        return makeJsonError(
          'LP-S02',
          'initial 根证书声称了非初始 koPoint / consecutivePasses / survivingTokensMask。',
          'Initial root setup violates clean initial invariants.',
          'lproof/1',
          fileChecksum,
          scopeMeta
        );
      }
    }

    // Optional external original-problem identity binding (R3 F4 + R4 §3 P1-B + R8 §3)
    if (expectedBinding?.problem) {
      const expProb = expectedBinding.problem;
      if (
        expProb.hasRegionHint !== undefined &&
        typeof expProb.hasRegionHint !== 'boolean'
      ) {
        return makeJsonError(
          'LP-J02',
          `外部待验原题 "${expProb.id}" 的 hasRegionHint 类型非法（必须为布尔值或省略）。`,
          'Invalid non-boolean expectedBinding.problem.hasRegionHint.',
          'lproof/1',
          fileChecksum,
          scopeMeta
        );
      }
      if (expProb.hasRegionHint === false && expProb.regionCoords.length > 0) {
        return makeJsonError(
          'LP-J02',
          `外部待验原题 "${expProb.id}" 自相矛盾：hasRegionHint=false 时不允许携带非空 regionCoords。`,
          'Contradictory expectedBinding.problem: hasRegionHint=false with non-empty regionCoords.',
          'lproof/1',
          fileChecksum,
          scopeMeta
        );
      }
      const expHasRegionHint =
        expProb.hasRegionHint !== undefined
          ? expProb.hasRegionHint
          : expProb.regionCoords.length > 0;
      const expRegion = expHasRegionHint
        ? sortedUniqueNumbers(expProb.regionCoords)
        : [];
      const certRegion = hasRegionHint ? sortedUniqueNumbers(regionCoords) : [];
      const expWall = sortedUniqueNumbers(expProb.immortalWallCoords);
      const certWall = sortedUniqueNumbers(immortalWallCoords);
      const expBlack = sortedUniqueNumbers(expProb.blackInitialCoords);
      const expWhite = sortedUniqueNumbers(expProb.whiteInitialCoords);
      const expTurn = expProb.turnColor === 'W' ? Color.White : Color.Black;
      if (
        boardSize !== expProb.boardSize ||
        originToPlayForBinding !== expTurn ||
        !numberArraysEqual(sortedUniqueNumbers(originBlackForBinding), expBlack) ||
        !numberArraysEqual(sortedUniqueNumbers(originWhiteForBinding), expWhite) ||
        !numberArraysEqual(certWall, expWall) ||
        hasRegionHint !== expHasRegionHint ||
        !numberArraysEqual(certRegion, expRegion)
      ) {
        return makeJsonError(
          'LP-P01',
          `证书与外部待验原题 "${expProb.id}" 的棋盘尺寸/初始棋子/先手/围墙或 region 不一致。`,
          'Problem identity binding mismatch against expectedProblem.',
          'lproof/1',
          fileChecksum,
          scopeMeta
        );
      }
    }

    // R4 §3 P1-B: If `problem` is provided without explicit `context`, auto-derive the problem's
    // canonical default ProofContext (goal, crucial stones, op, default ko permissions) and bind it!
    const expectedContext: ProofContext | undefined =
      expectedBinding?.context ??
      (expectedBinding?.problem
        ? deriveDefaultProofContextFromProblem(
            expectedBinding.problem,
            expectedBinding.koRule ?? KoRule.SituationalSuperko
          )
        : undefined);

    if (expectedContext) {
      const ec = expectedContext;
      const tokensMatch =
        context.initialTokens.length === ec.initialTokens.length &&
        context.initialTokens.every(
          (t, i) =>
            t.initialCoord === ec.initialTokens[i].initialCoord &&
            t.stoneColor === ec.initialTokens[i].stoneColor &&
            t.groupIndex === ec.initialTokens[i].groupIndex
        );
      if (
        context.rootAttacker !== ec.rootAttacker ||
        context.attackerGoal !== ec.attackerGoal ||
        context.crucialStoneOp !== ec.crucialStoneOp ||
        context.koRule !== ec.koRule ||
        context.attackerAllowKo !== ec.attackerAllowKo ||
        context.defenderAllowKo !== ec.defenderAllowKo ||
        !tokensMatch
      ) {
        return makeJsonError(
          'LP-P01',
          '证书的 ProofContext（攻防目标/关键子/劫规则/劫权）与外部待验命题不一致。',
          'ProofContext binding mismatch against expectedContext.',
          'lproof/1',
          fileChecksum,
          scopeMeta
        );
      }
    }

    const nodes: ProofDagNode[] = [];
    for (const rawNode of parsed.nodes) {
      if (!rawNode || typeof rawNode !== 'object' || Array.isArray(rawNode)) {
        return makeJsonError(
          'LP-J02',
          'lproof/1 nodes 包含非对象条目。',
          'Malformed node entry.',
          'lproof/1',
          fileChecksum
        );
      }
      const n = rawNode as Record<string, unknown>;
      const nodeToPlay = decodeColor(n.toPlay);
      if (
        typeof n.nodeId !== 'number' ||
        !Number.isInteger(n.nodeId) ||
        typeof n.isOrNode !== 'boolean' ||
        nodeToPlay === null ||
        typeof n.incomingMove !== 'number' ||
        !Number.isInteger(n.incomingMove) ||
        typeof n.outcome !== 'string' ||
        !isIntegerArray(n.childNodeIds) ||
        !isIntegerArray(n.childMoves)
      ) {
        return makeJsonError(
          'LP-J02',
          `lproof/1 节点条目字段缺失或类型非法 (nodeId=${String(n.nodeId)})。`,
          'Malformed ProofDagNode fields.',
          'lproof/1',
          fileChecksum
        );
      }
      if (hasStateTable) {
        if (
          typeof n.stateId !== 'number' ||
          !Number.isInteger(n.stateId) ||
          typeof n.historyId !== 'number' ||
          !Number.isInteger(n.historyId) ||
          typeof n.parentStateId !== 'number' ||
          !Number.isInteger(n.parentStateId)
        ) {
          return makeJsonError(
            'LP-J02',
            `full_state_table 模式下节点 #${n.nodeId} 必须声明合法整数 stateId、historyId 与 parentStateId。`,
            'full_state_table ProofDagNode must declare integer stateId, historyId, and parentStateId.',
            'lproof/1',
            fileChecksum
          );
        }
      }
      nodes.push({
        nodeId: n.nodeId,
        stateId: typeof n.stateId === 'number' ? n.stateId : 0,
        historyId: typeof n.historyId === 'number' ? n.historyId : 0,
        parentStateId: typeof n.parentStateId === 'number' ? n.parentStateId : -1,
        isOrNode: n.isOrNode,
        toPlay: nodeToPlay,
        incomingMove: n.incomingMove,
        incomingMoveSgf:
          typeof n.incomingMoveSgf === 'string'
            ? n.incomingMoveSgf
            : coordToSgf(n.incomingMove, boardSize),
        pn: decodeSatNumber(n.pn),
        dn: decodeSatNumber(n.dn),
        outcome: n.outcome as ProofOutcome,
        terminalEvidence: String(n.terminalEvidence ?? ''),
        isPrunedOutsideRz: Boolean(n.isPrunedOutsideRz),
        isTtHit: Boolean(n.isTtHit),
        isKoDependentBarrier: Boolean(n.isKoDependentBarrier),
        sourceProofNodeId:
          typeof n.sourceProofNodeId === 'number' ? n.sourceProofNodeId : null,
        proofRzCoords: isIntegerArray(n.proofRzCoords) ? n.proofRzCoords : [],
        disproofRzCoords: isIntegerArray(n.disproofRzCoords)
          ? n.disproofRzCoords
          : [],
        childNodeIds: n.childNodeIds,
        childMoves: n.childMoves,
        prunedCertificate:
          n.prunedCertificate &&
          typeof n.prunedCertificate === 'object' &&
          !Array.isArray(n.prunedCertificate)
            ? (n.prunedCertificate as ProofDagNode['prunedCertificate'])
            : undefined,
      });
    }

    let reconstructedHistoryTable: CanonicalSnapshot[][] = [];
    if (hasStateTable) {
      if (hasPooledHistory) {
        const rawPool = parsed.snapshotPool as unknown[];
        const pool: CanonicalSnapshot[] = [];
        for (let i = 0; i < rawPool.length; i++) {
          if (!isValidSnapshotShape(rawPool[i])) {
            return makeJsonError(
              'LP-J02',
              `lproof/1 snapshotPool[${i}] 结构非法。`,
              'Invalid snapshotPool entry.',
              'lproof/1',
              fileChecksum
            );
          }
          pool.push(normalizeSnapshot(rawPool[i] as Record<string, unknown>));
        }
        const idRows = parsed.historySnapshotIds as unknown[];
        for (let r = 0; r < idRows.length; r++) {
          const row = idRows[r];
          if (!isIntegerArray(row)) {
            return makeJsonError(
              'LP-J02',
              `lproof/1 historySnapshotIds[${r}] 非整数数组。`,
              'Invalid historySnapshotIds row.',
              'lproof/1',
              fileChecksum
            );
          }
          const snaps: CanonicalSnapshot[] = [];
          for (const idx of row) {
            if (idx < 0 || idx >= pool.length) {
              return makeJsonError(
                'LP-J02',
                `lproof/1 historySnapshotIds[${r}] 包含越界快照索引 ${idx}。`,
                'Out-of-bounds snapshotPool index.',
                'lproof/1',
                fileChecksum
              );
            }
            snaps.push(pool[idx]);
          }
          reconstructedHistoryTable.push(snaps);
        }
      } else if (hasInlineHistory) {
        const rawHist = parsed.historyTable as unknown[];
        for (let r = 0; r < rawHist.length; r++) {
          const row = rawHist[r];
          if (!Array.isArray(row)) {
            return makeJsonError(
              'LP-J02',
              `lproof/1 historyTable[${r}] 非数组。`,
              'Invalid historyTable row.',
              'lproof/1',
              fileChecksum
            );
          }
          const snaps: CanonicalSnapshot[] = [];
          for (const item of row) {
            if (!isValidSnapshotShape(item)) {
              return makeJsonError(
                'LP-J02',
                `lproof/1 historyTable[${r}] 包含非法快照对象。`,
                'Invalid inline history snapshot.',
                'lproof/1',
                fileChecksum
              );
            }
            snaps.push(
              normalizeSnapshot(item as unknown as Record<string, unknown>)
            );
          }
          reconstructedHistoryTable.push(snaps);
        }
      }
    }

    const stateTable: StateTableEntry[] = [];
    if (hasStateTable) {
      for (let i = 0; i < (parsed.stateTable as unknown[]).length; i++) {
        const rawSt = (parsed.stateTable as unknown[])[i];
        if (!rawSt || typeof rawSt !== 'object' || Array.isArray(rawSt)) {
          return makeJsonError(
            'LP-J02',
            `lproof/1 stateTable[${i}] 非对象。`,
            'Malformed stateTable entry.',
            'lproof/1',
            fileChecksum
          );
        }
        const stObj = rawSt as Record<string, unknown>;
        const stToPlay = decodeColor(stObj.toPlay);
        if (
          typeof stObj.stateId !== 'number' ||
          typeof stObj.parentStateId !== 'number' ||
          typeof stObj.moveFromParent !== 'number' ||
          stToPlay === null ||
          typeof stObj.koPoint !== 'number' ||
          typeof stObj.consecutivePasses !== 'number' ||
          typeof stObj.survivingTokensMask !== 'number' ||
          typeof stObj.zobristHex !== 'string' ||
          !isIntegerArray(stObj.blackCoords) ||
          !isIntegerArray(stObj.whiteCoords) ||
          typeof stObj.historyId !== 'number'
        ) {
          return makeJsonError(
            'LP-J02',
            `lproof/1 stateTable[${i}] 缺少必要字段或类型非法。`,
            'Invalid stateTable fields.',
            'lproof/1',
            fileChecksum
          );
        }
        stateTable.push({
          stateId: stObj.stateId,
          parentStateId: stObj.parentStateId,
          moveFromParent: stObj.moveFromParent,
          toPlay: stToPlay,
          koPoint: stObj.koPoint,
          consecutivePasses: stObj.consecutivePasses,
          survivingTokensMask: stObj.survivingTokensMask,
          zobristHex: stObj.zobristHex,
          blackCoords: stObj.blackCoords,
          whiteCoords: stObj.whiteCoords,
          historyId: stObj.historyId,
        });
      }
    }

    if (
      typeof parsed.rootNode !== 'number' ||
      typeof parsed.rootOutcome !== 'string'
    ) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 缺少合法的 rootNode 或 rootOutcome。',
        'Missing rootNode or rootOutcome.',
        'lproof/1',
        fileChecksum
      );
    }

    if (
      parsed.bestMoveSgf !== undefined &&
      parsed.bestMoveSgf !== null &&
      typeof parsed.bestMoveSgf !== 'string'
    ) {
      return makeJsonError(
        'LP-J02',
        'lproof/1 顶层 bestMoveSgf 字段必须为字符串或 null。',
        'Invalid bestMoveSgf type.',
        'lproof/1',
        fileChecksum,
        scopeMeta
      );
    }

    const reconstructedReport: SolveReport = {
      problemId: String(parsed.problemId ?? ''),
      problemTitle: String(parsed.problemId ?? ''),
      boardSize,
      firstToPlay,
      blackInitialCoords,
      whiteInitialCoords,
      immortalWallCoords,
      hasRegionHint,
      regionCoords,
      rawRegionPointCount:
        typeof setup.rawRegionPointCount === 'number'
          ? setup.rawRegionPointCount
          : regionCoords.length,
      isFullRegionSearch:
        typeof setup.isFullRegionSearch === 'boolean'
          ? setup.isFullRegionSearch
          : true,
      inputHash: String(setup.inputHash ?? ''),
      configFingerprint: '',
      solverVersion: 'lproof/1-standalone',
      rootStatus: parsed.rootOutcome as ProofOutcome,
      unknownReason: null,
      rootPn: decodeSatNumber(parsed.rootPn),
      rootDn: decodeSatNumber(parsed.rootDn),
      bestMove: typeof parsed.bestMove === 'number' ? parsed.bestMove : PASS_MOVE,
      bestMoveSgf:
        typeof parsed.bestMoveSgf === 'string' ? parsed.bestMoveSgf : null,
      numNodes: nodes.length,
      timeMs: 0,
      boardTtHits: 0,
      patternTtHits: 0,
      patternProofReusableHits: 0,
      ghiRejectedCount: 0,
      prunedOutsideRzCount: nodes.filter((x) => x.isPrunedOutsideRz).length,
      wideningUpgrades: 0,
      cycleDetections: 0,
      koDependentRejections: 0,
      rzSizeAtRoot: 0,
      resourceExhausted: false,
      artifactsComplete: true,
      rootProofRzCoords: [],
      rootDisproofRzCoords: [],
      bensonAliveCoords: [],
      eyeTopologyRegions: [],
      principalVariation: [],
      proofDagNodes: nodes,
      stateTable,
      historyTable: reconstructedHistoryTable,
      rootDagNodeId: parsed.rootNode,
      proofChecksum: fileChecksum,
      sgfContent: '',
      sgfChecksum: '',
      lproofJson: lproofJsonText,
      resultJson: '',
    };

    const ver = this.verifyProofDag(initialPos, context, reconstructedReport, {
      skipChecksumRecompute: true,
      skipTraceReplay: true,
      isCompactDag: !hasStateTable,
      verifiedScope: effectiveScope,
      verifiedRootKind: rootKind,
      encodingMode,
      traceOutsideRegion,
      traceHasRestrictedKoCapture,
    });
    return {
      ...ver,
      jcsSha256Checksum: fileChecksum,
    };
  }

  /**
   * Independent recursive semantic proof replay on `queryPos` (with its authentic HistorySet)
   * for `OutsideRZRevalidated` and `TT` reuse nodes. Zero shared code with DfpnSolver!
   */
  private replaySourceSubgraphOnQueryState(
    queryPos: GoPosition,
    regionCoords: number[] | null,
    context: ProofContext,
    dagNodes: ProofDagNode[],
    sourceNodeId: number,
    expectedOutcome: ProofOutcome,
    terminalEvaluator: BensonTerminalEvaluator,
    guardDepth: number
  ): boolean {
    if (
      guardDepth > 64 ||
      sourceNodeId < 0 ||
      sourceNodeId >= dagNodes.length
    ) {
      return false;
    }

    let resolvedId = sourceNodeId;
    const seenRedirect = new Set<number>();
    while (true) {
      if (
        resolvedId < 0 ||
        resolvedId >= dagNodes.length ||
        seenRedirect.has(resolvedId)
      ) {
        return false;
      }
      seenRedirect.add(resolvedId);
      const cur = dagNodes[resolvedId];
      if (!cur) return false;
      if (!cur.isPrunedOutsideRz && !cur.isTtHit) break;
      if (
        cur.sourceProofNodeId === null ||
        cur.sourceProofNodeId < 0 ||
        cur.sourceProofNodeId >= cur.nodeId
      ) {
        return false;
      }
      resolvedId = cur.sourceProofNodeId;
    }

    const sourceNode = dagNodes[resolvedId];
    if (!sourceNode || sourceNode.outcome !== expectedOutcome) {
      return false;
    }

    const checkEarlyTerminal = (): boolean => {
      const term = terminalEvaluator.evaluateTerminal(queryPos, context, false);
      if (term.status === TerminalStatus.Win) {
        return expectedOutcome === ProofOutcome.ProvenWin;
      }
      if (term.status === TerminalStatus.Loss) {
        return expectedOutcome === ProofOutcome.ProvenLoss;
      }
      return false;
    };

    if (sourceNode.childNodeIds.length === 0 || queryPos.isAtDoublePass()) {
      return checkEarlyTerminal();
    }
    if (sourceNode.childMoves.length !== sourceNode.childNodeIds.length) {
      return false;
    }

    const isOr = queryPos.toPlay === context.rootAttacker;
    const restrictedSide =
      (queryPos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
      (queryPos.toPlay !== context.rootAttacker && !context.defenderAllowKo);

    const allowedRegion =
      regionCoords !== null ? new Set<number>(regionCoords) : null;

    // Existential replay: OR -> ProvenWin or AND -> ProvenLoss
    if (
      (isOr && expectedOutcome === ProofOutcome.ProvenWin) ||
      (!isOr && expectedOutcome === ProofOutcome.ProvenLoss)
    ) {
      for (let i = 0; i < sourceNode.childNodeIds.length; i++) {
        const mv = sourceNode.childMoves[i];
        // R3 F1: Existential witness moves MUST belong to the query's allowed region (or PASS)
        if (mv !== PASS_MOVE && allowedRegion !== null && !allowedRegion.has(mv)) {
          continue;
        }
        const cid = sourceNode.childNodeIds[i];
        if (cid < 0 || cid >= sourceNode.nodeId) continue;
        const chNode = dagNodes[cid];
        if (!chNode || chNode.outcome !== expectedOutcome) continue;
        const nextPos = queryPos.clone();
        const playRes = nextPos.playMove(mv);
        if (!playRes.legal) continue;
        if (playRes.isKoCapture && restrictedSide) continue;
        if (
          this.replaySourceSubgraphOnQueryState(
            nextPos,
            regionCoords,
            context,
            dagNodes,
            cid,
            expectedOutcome,
            terminalEvaluator,
            guardDepth + 1
          )
        ) {
          return true;
        }
      }
      return checkEarlyTerminal();
    }

    // Universal / Full-coverage replay: AND -> ProvenWin or OR -> ProvenLoss
    // EVERY legal move on `queryPos` inside `regionCoords` must exist in `sourceNode` and hold!
    const moveMap = new Map<number, number>();
    for (let i = 0; i < sourceNode.childMoves.length; i++) {
      const cid = sourceNode.childNodeIds[i];
      if (cid < 0 || cid >= sourceNode.nodeId) return false;
      moveMap.set(sourceNode.childMoves[i], cid);
    }

    const queryLegalMoves = queryPos.generateLegalMoves(regionCoords);
    for (let i = 0; i < queryLegalMoves.length; i++) {
      const mv = queryLegalMoves[i];
      const cid = moveMap.get(mv);
      if (cid === undefined) return checkEarlyTerminal();
      const chNode = dagNodes[cid];
      if (!chNode || chNode.outcome !== expectedOutcome) {
        return checkEarlyTerminal();
      }
      const nextPos = queryPos.clone();
      const playRes = nextPos.playMove(mv);
      if (!playRes.legal) return checkEarlyTerminal();
      if (
        !this.replaySourceSubgraphOnQueryState(
          nextPos,
          regionCoords,
          context,
          dagNodes,
          cid,
          expectedOutcome,
          terminalEvaluator,
          guardDepth + 1
        )
      ) {
        return checkEarlyTerminal();
      }
    }

    return true;
  }

  /**
   * Zero-trust recursive DAG verifier for compact `lproof/1` files (without StateTable, e.g. C++ CLI output).
   */
  private verifyCompactDagRecursive(
    pos: GoPosition,
    effectiveRegionMask: number[] | null,
    allowedRegionSet: Set<number> | null,
    context: ProofContext,
    report: SolveReport,
    nodeId: number,
    independentTerminal: BensonTerminalEvaluator,
    depth: number,
    stats: {
      verifiedStates: number;
      verifiedLeaves: number;
      verifiedUniversals: number;
      replayedPruned: number;
      replayedTt: number;
    },
    recordFailure: (code: string, nid: number | null) => void,
    onVisitNode?: (
      node: ProofDagNode,
      pos: GoPosition,
      parentNode: ProofDagNode | null,
      incomingMoveFromParent: number | null
    ) => { ok: boolean; code: string; detail: string },
    parentNode: ProofDagNode | null = null,
    incomingMoveFromParent: number | null = null
  ): { ok: boolean; detail: string } {
    if (depth > 256 || nodeId < 0 || nodeId >= report.proofDagNodes.length) {
      recordFailure('LP-S01', nodeId);
      return { ok: false, detail: `DAG 递归超深或节点 #${nodeId} 越界` };
    }
    const node = report.proofDagNodes[nodeId];
    if (!node || node.nodeId !== nodeId) {
      recordFailure('LP-N01', nodeId);
      return { ok: false, detail: `DAG 节点 #${nodeId} 缺失或 nodeId 不匹配` };
    }
    stats.verifiedStates++;

    const expectedIsOr = pos.toPlay === context.rootAttacker;
    if (node.toPlay !== pos.toPlay || node.isOrNode !== expectedIsOr) {
      recordFailure('LP-N10', nodeId);
      return {
        ok: false,
        detail: `节点 #${nodeId} 轮次/AND-OR 角色与真实可达局面冲突`,
      };
    }

    if (
      (node.outcome === ProofOutcome.ProvenWin &&
        (node.pn !== 0 || node.dn < PN_DN_SATURATION)) ||
      (node.outcome === ProofOutcome.ProvenLoss &&
        (node.dn !== 0 || node.pn < PN_DN_SATURATION))
    ) {
      recordFailure('LP-N15', nodeId);
      return {
        ok: false,
        detail: `节点 #${nodeId} 的 PN/DN (${node.pn}/${node.dn}) 与结论 ${node.outcome} 不一致`,
      };
    }

    if (onVisitNode) {
      const bindRes = onVisitNode(node, pos, parentNode, incomingMoveFromParent);
      if (!bindRes.ok) {
        recordFailure(bindRes.code, nodeId);
        return { ok: false, detail: bindRes.detail };
      }
    }

    if (node.isPrunedOutsideRz || node.isTtHit) {
      if (
        node.sourceProofNodeId === null ||
        node.sourceProofNodeId < 0 ||
        node.sourceProofNodeId >= node.nodeId
      ) {
        recordFailure('LP-R02', nodeId);
        return {
          ok: false,
          detail: `复用/剪枝节点 #${nodeId} 缺失有效 sourceProofNodeId`,
        };
      }
      const ok = this.replaySourceSubgraphOnQueryState(
        pos,
        effectiveRegionMask,
        context,
        report.proofDagNodes,
        node.sourceProofNodeId,
        node.outcome,
        independentTerminal,
        0
      );
      if (!ok) {
        recordFailure('LP-R03', nodeId);
        return {
          ok: false,
          detail: `节点 #${nodeId} 在真实可达 QueryState+HistorySet 下重放源证明 #${node.sourceProofNodeId} 失败`,
        };
      }
      if (node.isPrunedOutsideRz) stats.replayedPruned++;
      if (node.isTtHit) stats.replayedTt++;
      return { ok: true, detail: '' };
    }

    if (node.childNodeIds.length === 0) {
      stats.verifiedLeaves++;
      const term = independentTerminal.evaluateTerminal(pos, context);
      const expectedStatus =
        node.outcome === ProofOutcome.ProvenWin
          ? TerminalStatus.Win
          : TerminalStatus.Loss;
      if (term.status !== expectedStatus) {
        recordFailure('LP-L04', nodeId);
        return {
          ok: false,
          detail: `叶节点 #${nodeId} 独立终局复算失败：声称 ${node.outcome}，实测 ${term.status}`,
        };
      }
      return { ok: true, detail: '' };
    }

    if (node.childMoves.length !== node.childNodeIds.length) {
      recordFailure('LP-N11', nodeId);
      return {
        ok: false,
        detail: `内部节点 #${nodeId} childMoves 与 childNodeIds 数量不一致`,
      };
    }

    const moveToEdge = new Map<
      number,
      { cid: number; nextPos: GoPosition; isKoCapture: boolean }
    >();
    for (let k = 0; k < node.childMoves.length; k++) {
      const mv = node.childMoves[k];
      const cid = node.childNodeIds[k];
      if (!Number.isInteger(cid) || cid < 0 || cid >= node.nodeId) {
        recordFailure('LP-T02', nodeId);
        return {
          ok: false,
          detail: `内部节点 #${nodeId} 的子节点索引 #${cid} 越界或违反后序拓扑约束 (child_id < node_id)`,
        };
      }
      if (moveToEdge.has(mv)) {
        recordFailure('LP-N11', nodeId);
        return { ok: false, detail: `内部节点 #${nodeId} 存在重复着法边 move=${mv}` };
      }
      if (
        mv !== PASS_MOVE &&
        allowedRegionSet !== null &&
        !allowedRegionSet.has(mv)
      ) {
        recordFailure('LP-S11', nodeId);
        return {
          ok: false,
          detail: `内部节点 #${nodeId} 的着法边 ${coordToSgf(
            mv,
            pos.boardSize
          )} (move=${mv}) 超出声明的合法 region 集合`,
        };
      }
      const nextPos = pos.clone();
      const playRes = nextPos.playMove(mv);
      if (!playRes.legal) {
        recordFailure('LP-S09', nodeId);
        return { ok: false, detail: `内部节点 #${nodeId} 包含非法着法边 move=${mv}` };
      }
      moveToEdge.set(mv, { cid, nextPos, isKoCapture: playRes.isKoCapture });
    }

    const restrictedSide =
      (pos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
      (pos.toPlay !== context.rootAttacker && !context.defenderAllowKo);
    const existentialMode =
      (node.isOrNode && node.outcome === ProofOutcome.ProvenWin) ||
      (!node.isOrNode && node.outcome === ProofOutcome.ProvenLoss);

    if (existentialMode) {
      for (const [mv, edge] of moveToEdge) {
        const chNode = report.proofDagNodes[edge.cid];
        if (!chNode || chNode.outcome !== node.outcome) continue;
        if (edge.isKoCapture && restrictedSide) continue;
        const sub = this.verifyCompactDagRecursive(
          edge.nextPos,
          effectiveRegionMask,
          allowedRegionSet,
          context,
          report,
          edge.cid,
          independentTerminal,
          depth + 1,
          stats,
          recordFailure,
          onVisitNode,
          node,
          mv
        );
        if (sub.ok) return { ok: true, detail: '' };
        return sub;
      }
      recordFailure('LP-N21', nodeId);
      return {
        ok: false,
        detail: `单见证节点 #${nodeId} 缺少合法、区域内、非禁劫的同结论见证子节点`,
      };
    }

    stats.verifiedUniversals++;
    const expectedLegalMoves = pos.generateLegalMoves(effectiveRegionMask);
    for (const lm of expectedLegalMoves) {
      const edge = moveToEdge.get(lm);
      if (!edge) {
        recordFailure('LP-N22', nodeId);
        return {
          ok: false,
          detail: `全覆盖节点 #${nodeId} 遗漏合法应手 ${coordToSgf(
            lm,
            pos.boardSize
          )}`,
        };
      }
      const chNode = report.proofDagNodes[edge.cid];
      if (!chNode || chNode.outcome !== node.outcome) {
        recordFailure('LP-N22', nodeId);
        return {
          ok: false,
          detail: `全覆盖节点 #${nodeId} 应手子节点 #${edge.cid} 结论不一致`,
        };
      }
      const sub = this.verifyCompactDagRecursive(
        edge.nextPos,
        effectiveRegionMask,
        allowedRegionSet,
        context,
        report,
        edge.cid,
        independentTerminal,
        depth + 1,
        stats,
        recordFailure,
        onVisitNode,
        node,
        lm
      );
      if (!sub.ok) return sub;
    }

    return { ok: true, detail: '' };
  }

  /**
   * Shared provenance & arrival-trace validation used by the memory entrypoint
   * (`verifyProofDag`) so memory and file verification produce identical scope,
   * LP-P02, LP-S11, LP-S12, and trace-violation flags.
   */
  private validateRootProvenanceAndTrace(
    initialPos: GoPosition,
    context: ProofContext,
    regionMask: number[] | null,
    effectiveScope: VerificationScope
  ): {
    ok: boolean;
    errorCode: string;
    message: string;
    detail: string;
    traceOutsideRegion: boolean;
    traceHasRestrictedKoCapture: boolean;
  } {
    const isTraced = initialPos.playedMoveTrace.length > 0;
    if (effectiveScope === 'original_root' && isTraced) {
      return {
        ok: false,
        errorCode: 'LP-P02',
        message:
          '原题命题校验模式 (original_root) 拒绝 traced_subposition 子局面证书；该证书仅证明给定到达轨迹后的子局面，不等价于原题初始命题。',
        detail:
          'Rejected traced_subposition under original_root verification scope.',
        traceOutsideRegion: false,
        traceHasRestrictedKoCapture: false,
      };
    }

    if (!isTraced) {
      const expectedRootSnap = initialPos.currentCanonicalSnapshot();
      if (!historyTablesMatch(initialPos.historySnapshots, [expectedRootSnap])) {
        return {
          ok: false,
          errorCode: 'LP-S02',
          message:
            '初始根局面的超劫历史快照列表 (historySnapshots) 缺失或与当前棋面不一致。',
          detail:
            'Initial root historySnapshots disagrees with canonical root snapshot.',
          traceOutsideRegion: false,
          traceHasRestrictedKoCapture: false,
        };
      }
      return {
        ok: true,
        errorCode: 'PASS',
        message: '',
        detail: '',
        traceOutsideRegion: false,
        traceHasRestrictedKoCapture: false,
      };
    }

    const regionSet =
      regionMask !== null ? new Set<number>(regionMask) : null;
    const replayPos = new GoPosition(
      context,
      initialPos.boardSize,
      Array.from(initialPos.immortalWallSet)
    );
    replayPos.setupInitialStones(
      initialPos.originBlackCoords,
      initialPos.originWhiteCoords,
      initialPos.originToPlay
    );

    let traceOutsideRegion = false;
    let traceHasRestrictedKoCapture = false;

    for (let i = 0; i < initialPos.playedMoveTrace.length; i++) {
      const tmv = initialPos.playedMoveTrace[i];
      const outsideRegion =
        tmv !== PASS_MOVE && regionSet !== null && !regionSet.has(tmv);
      if (outsideRegion) {
        traceOutsideRegion = true;
        if (effectiveScope === 'traced_within_rules') {
          return {
            ok: false,
            errorCode: 'LP-S11',
            message: `traced_subposition 到达轨迹第 ${i + 1} 手 ${coordToSgf(
              tmv,
              initialPos.boardSize
            )} (move=${tmv}) 超出题目声明的合法 region 集合。`,
            detail: `Trace move ${tmv} at index ${i} lies outside declared region.`,
            traceOutsideRegion: true,
            traceHasRestrictedKoCapture,
          };
        }
      }

      const sideToPlay = replayPos.toPlay;
      const restrictedSide =
        (sideToPlay === context.rootAttacker && !context.attackerAllowKo) ||
        (sideToPlay !== context.rootAttacker && !context.defenderAllowKo);
      const playRes = replayPos.playMove(tmv);
      if (!playRes.legal) {
        return {
          ok: false,
          errorCode: 'LP-S09',
          message: `traced_subposition 到达轨迹第 ${i + 1} 手 move=${tmv} 在规则下非法。`,
          detail: `Illegal move ${tmv} at trace index ${i}.`,
          traceOutsideRegion,
          traceHasRestrictedKoCapture,
        };
      }
      if (playRes.isKoCapture && restrictedSide) {
        traceHasRestrictedKoCapture = true;
        if (effectiveScope === 'traced_within_rules') {
          return {
            ok: false,
            errorCode: 'LP-S12',
            message: `traced_subposition 到达轨迹第 ${i + 1} 手 ${coordToSgf(
              tmv,
              initialPos.boardSize
            )} 属于受限方禁劫提劫，在 traced_within_rules 范围内被拒绝。`,
            detail: `Restricted-side ko capture at trace index ${i} rejected under traced_within_rules.`,
            traceOutsideRegion,
            traceHasRestrictedKoCapture: true,
          };
        }
      }
    }

    if (
      replayPos.toPlay !== initialPos.toPlay ||
      replayPos.koPoint !== initialPos.koPoint ||
      replayPos.consecutivePasses !== initialPos.consecutivePasses ||
      replayPos.survivingTargetTokensMask !==
        initialPos.survivingTargetTokensMask ||
      replayPos.computeZobristHex() !== initialPos.computeZobristHex() ||
      !numberArraysEqual(
        replayPos.getBlackCoords(),
        initialPos.getBlackCoords()
      ) ||
      !numberArraysEqual(
        replayPos.getWhiteCoords(),
        initialPos.getWhiteCoords()
      ) ||
      !historyTablesMatch(
        initialPos.historySnapshots,
        replayPos.historySnapshots
      )
    ) {
      return {
        ok: false,
        errorCode: 'LP-S02',
        message:
          'traced_subposition 到达轨迹重放结果（含完整超劫历史快照）与当前内存初始局面不一致。',
        detail:
          'Replayed trace position or historySnapshots diverges from provided initialPos.',
        traceOutsideRegion,
        traceHasRestrictedKoCapture,
      };
    }

    return {
      ok: true,
      errorCode: 'PASS',
      message: '',
      detail: '',
      traceOutsideRegion,
      traceHasRestrictedKoCapture,
    };
  }

  /**
   * Computes the encoding-independent canonical `compact_dag` RFC 8785 JCS
   * SHA-256 digest of ONLY the semantic lproof/1 proof DAG schema fields
   * (stripping StateTable/HistoryTable/prunedCertificate and any non-semantic
   * extra JSON properties) so TS and C++ produce identical canonical digests
   * for both `full_state_table` and `compact_dag` certificates.
   */
  private computeCanonicalSchemaChecksum(
    initialPos: GoPosition,
    context: ProofContext,
    report: SolveReport
  ): string {
    const sortUniqueBoardCoords = (coords: number[]): number[] => {
      const maxPts = initialPos.boardSize * initialPos.boardSize;
      const set = new Set<number>();
      for (const c of coords) {
        if (Number.isInteger(c) && c >= 0 && c < maxPts) set.add(c);
      }
      return Array.from(set).sort((a, b) => a - b);
    };

    const normalizeEvidence = (n: ProofDagNode): string => {
      if (
        n.terminalEvidence === 'BENSON_UCA' ||
        n.terminalEvidence === 'TOKENS_CAPTURED' ||
        n.terminalEvidence === 'DOUBLE_PASS_RESOLUTION' ||
        n.terminalEvidence === 'EMPTY_TARGET_CONSTANT_FALSE'
      ) {
        return n.terminalEvidence;
      }
      if (n.isPrunedOutsideRz) return 'OUTSIDE_RZ_REVALIDATED';
      if (n.isTtHit) return 'TT_REVALIDATED_REUSE';
      if (n.childNodeIds.length > 0) return 'INTERNAL_AGGREGATION';
      return 'NONE';
    };

    const resolvedRegion = resolveReportRegion(report);
    const hasRegionHint = resolvedRegion.hasRegionHint;
    const regionCoords = sortUniqueBoardCoords(resolvedRegion.regionCoords);
    const immortalWallCoords = sortUniqueBoardCoords(
      Array.from(initialPos.immortalWallSet)
    );
    const isTraced = initialPos.playedMoveTrace.length > 0;
    const problemSetup: Record<string, unknown> = {
      boardSize: initialPos.boardSize,
      rootKind: isTraced ? 'traced_subposition' : 'initial',
      firstToPlay: encodeColorStr(initialPos.toPlay),
      koPoint: initialPos.koPoint,
      consecutivePasses: initialPos.consecutivePasses,
      survivingTokensMask: initialPos.survivingTargetTokensMask,
      zobristHex: initialPos.computeZobristHex(),
      inputHash: report.inputHash,
      blackInitialCoords: initialPos.getBlackCoords(),
      whiteInitialCoords: initialPos.getWhiteCoords(),
      immortalWallCoords,
      hasRegionHint,
      regionCoords,
      rawRegionPointCount: regionCoords.length,
      isFullRegionSearch: true,
    };
    if (isTraced) {
      problemSetup.originFirstToPlay = encodeColorStr(initialPos.originToPlay);
      problemSetup.originBlackCoords = sortUniqueBoardCoords(
        initialPos.originBlackCoords
      );
      problemSetup.originWhiteCoords = sortUniqueBoardCoords(
        initialPos.originWhiteCoords
      );
      problemSetup.initialTraceMoves = initialPos.playedMoveTrace.slice();
    }

    const compactPayload = {
      magic: 'lproof/1',
      encodingMode: 'compact_dag' as LProofEncodingMode,
      problemId: report.problemId,
      context: {
        contextId: context.contextId,
        rootAttacker: encodeColorStr(context.rootAttacker),
        attackerGoal: context.attackerGoal,
        crucialStoneOp: context.crucialStoneOp,
        koRule: context.koRule,
        attackerAllowKo: context.attackerAllowKo,
        defenderAllowKo: context.defenderAllowKo,
        initialTokens: context.initialTokens.map((t) => ({
          tokenId: t.tokenId,
          initialCoord: t.initialCoord,
          groupIndex: t.groupIndex,
          stoneColor: encodeColorStr(t.stoneColor),
        })),
      },
      problemSetup,
      rootNode: report.rootDagNodeId,
      rootOutcome: report.rootStatus,
      rootPn: report.rootPn >= PN_DN_SATURATION ? 'SAT' : report.rootPn,
      rootDn: report.rootDn >= PN_DN_SATURATION ? 'SAT' : report.rootDn,
      bestMove: report.bestMove,
      bestMoveSgf: moveToCanonicalSgf(report.bestMove, initialPos.boardSize),
      nodes: report.proofDagNodes.map((n) => ({
        nodeId: n.nodeId,
        isOrNode: n.isOrNode,
        toPlay: encodeColorStr(n.toPlay),
        incomingMove: n.incomingMove,
        incomingMoveSgf: moveToCanonicalSgf(
          n.incomingMove,
          initialPos.boardSize
        ),
        pn: n.pn >= PN_DN_SATURATION ? 'SAT' : n.pn,
        dn: n.dn >= PN_DN_SATURATION ? 'SAT' : n.dn,
        outcome: n.outcome,
        terminalEvidence: normalizeEvidence(n),
        isPrunedOutsideRz: n.isPrunedOutsideRz,
        isTtHit: n.isTtHit,
        isKoDependentBarrier: false,
        sourceProofNodeId:
          (n.isPrunedOutsideRz || n.isTtHit) && n.sourceProofNodeId !== null
            ? n.sourceProofNodeId
            : null,
        proofRzCoords: sortUniqueBoardCoords(n.proofRzCoords),
        disproofRzCoords: sortUniqueBoardCoords(n.disproofRzCoords),
        childNodeIds: n.childNodeIds,
        childMoves: n.childMoves,
        prunedCertificate: null,
      })),
    };

    return `sha256-jcs:${sha256Hex(canonicalizeJsonJcs(compactPayload))}`;
  }

  // FR-9.1, FR-9.2, FR-9.3: Zero-trust Independent Proof Checker (`tprover check`)
  public verifyProofDag(
    initialPos: GoPosition,
    context: ProofContext,
    report: SolveReport,
    options?: {
      skipChecksumRecompute?: boolean;
      skipTraceReplay?: boolean;
      isCompactDag?: boolean;
      verifiedScope?: VerificationScope;
      verifiedRootKind?: 'initial' | 'traced_subposition';
      encodingMode?: LProofEncodingMode;
      traceOutsideRegion?: boolean;
      traceHasRestrictedKoCapture?: boolean;
    }
  ): VerificationReport {
    const auditChecks: VerificationReport['auditChecks'] = [];
    const independentTerminal = new BensonTerminalEvaluator();
    let firstErrorCode = 'PASS';
    let failedNode: number | null = null;
    const recordFailure = (code: string, nodeId: number | null = null) => {
      if (firstErrorCode === 'PASS') {
        firstErrorCode = code;
        failedNode = nodeId;
      }
    };

    const isCompactDag = Boolean(options?.isCompactDag);
    const effectiveEncodingMode: LProofEncodingMode =
      options?.encodingMode ??
      (isCompactDag ? 'compact_dag' : 'full_state_table');
    const inferredRootKind: 'initial' | 'traced_subposition' =
      options?.verifiedRootKind ??
      (initialPos.playedMoveTrace.length > 0 ? 'traced_subposition' : 'initial');
    const effectiveScope: VerificationScope =
      options?.verifiedScope ??
      (inferredRootKind === 'traced_subposition'
        ? 'traced_within_rules'
        : 'original_root');

    // R8 §3: Reject non-boolean or contradictory hasRegionHint=false + non-empty regionCoords
    // in the in-memory verification entrypoint instead of silently rewriting regionCoords.
    if (
      report.hasRegionHint !== undefined &&
      typeof report.hasRegionHint !== 'boolean'
    ) {
      return {
        encodingMode: effectiveEncodingMode,
        verifiedScope: effectiveScope,
        verifiedRootKind: inferredRootKind,
        verifiedGoal: context.attackerGoal,
        verifiedAttackerAllowKo: context.attackerAllowKo,
        verifiedDefenderAllowKo: context.defenderAllowKo,
        traceOutsideRegion: Boolean(options?.traceOutsideRegion),
        traceHasRestrictedKoCapture: Boolean(
          options?.traceHasRestrictedKoCapture
        ),
        passed: false,
        schemaVersion: 'lproof/1',
        jcsSha256Checksum: report.proofChecksum,
        verifiedNodes: 0,
        verifiedStates: 0,
        verifiedHistories: 0,
        replayedPrunedCertificates: 0,
        replayedTtHits: 0,
        failedNodeId: null,
        errorCode: 'LP-J02',
        message: 'SolveReport.hasRegionHint 类型非法（必须为布尔值或省略）。',
        auditChecks: [
          {
            checkId: 'CHK-01',
            requirementRef: 'FR-8.3 / R8 §3',
            title: '区域提示契约一致性校验',
            passed: false,
            detail: `Invalid non-boolean hasRegionHint=${String(
              report.hasRegionHint
            )}.`,
          },
        ],
      };
    }
    if (
      report.hasRegionHint === false &&
      (report.regionCoords?.length ?? 0) > 0
    ) {
      return {
        encodingMode: effectiveEncodingMode,
        verifiedScope: effectiveScope,
        verifiedRootKind: inferredRootKind,
        verifiedGoal: context.attackerGoal,
        verifiedAttackerAllowKo: context.attackerAllowKo,
        verifiedDefenderAllowKo: context.defenderAllowKo,
        traceOutsideRegion: Boolean(options?.traceOutsideRegion),
        traceHasRestrictedKoCapture: Boolean(
          options?.traceHasRestrictedKoCapture
        ),
        passed: false,
        schemaVersion: 'lproof/1',
        jcsSha256Checksum: report.proofChecksum,
        verifiedNodes: 0,
        verifiedStates: 0,
        verifiedHistories: 0,
        replayedPrunedCertificates: 0,
        replayedTtHits: 0,
        failedNodeId: null,
        errorCode: 'LP-J02',
        message:
          'SolveReport 自相矛盾：hasRegionHint=false 时不允许携带非空 regionCoords。',
        auditChecks: [
          {
            checkId: 'CHK-01',
            requirementRef: 'FR-8.3 / R8 §3',
            title: '区域提示契约一致性校验',
            passed: false,
            detail: `Contradictory hasRegionHint=false with regionCoords.length=${
              report.regionCoords?.length ?? 0
            }.`,
          },
        ],
      };
    }

    const resolvedRegion = resolveReportRegion(report);
    const effectiveRegionCoords = resolvedRegion.regionCoords;
    const effectiveRegionMask = resolvedRegion.regionMask;
    const allowedRegionSet = resolvedRegion.regionSet;

    let traceOutsideRegion = Boolean(options?.traceOutsideRegion);
    let traceHasRestrictedKoCapture = Boolean(
      options?.traceHasRestrictedKoCapture
    );

    // R5 §2: Enforce identical root provenance & arrival-trace rules in memory entrypoint!
    if (!options?.skipTraceReplay) {
      const traceCheck = this.validateRootProvenanceAndTrace(
        initialPos,
        context,
        effectiveRegionMask,
        effectiveScope
      );
      traceOutsideRegion = traceCheck.traceOutsideRegion;
      traceHasRestrictedKoCapture = traceCheck.traceHasRestrictedKoCapture;
      if (!traceCheck.ok) {
        return {
          encodingMode: effectiveEncodingMode,
          verifiedScope: effectiveScope,
          verifiedRootKind: inferredRootKind,
          verifiedGoal: context.attackerGoal,
          verifiedAttackerAllowKo: context.attackerAllowKo,
          verifiedDefenderAllowKo: context.defenderAllowKo,
          traceOutsideRegion,
          traceHasRestrictedKoCapture,
          passed: false,
          schemaVersion: 'lproof/1',
          jcsSha256Checksum: report.proofChecksum,
          verifiedNodes: 0,
          verifiedStates: 0,
          verifiedHistories: 0,
          replayedPrunedCertificates: 0,
          replayedTtHits: 0,
          failedNodeId: null,
          errorCode: traceCheck.errorCode,
          message: traceCheck.message,
          auditChecks: [
            {
              checkId: 'CHK-01',
              requirementRef: 'FR-8.3 / FR-9.1 / R5 §2',
              title: '根命题作用域与到达轨迹规则一致性校验',
              passed: false,
              detail: traceCheck.detail,
            },
          ],
        };
      }
    }

    const commonMeta: Partial<VerificationReport> = {
      encodingMode: effectiveEncodingMode,
      verifiedScope: effectiveScope,
      verifiedRootKind: inferredRootKind,
      verifiedGoal: context.attackerGoal,
      verifiedAttackerAllowKo: context.attackerAllowKo,
      verifiedDefenderAllowKo: context.defenderAllowKo,
      traceOutsideRegion,
      traceHasRestrictedKoCapture,
    };

    // Check 1: RFC 8785 JCS SHA-256 Checksum, InputHash, Root Proposition & bestMove Binding (FR-8.3, FR-9.1, R4 §4)
    let checksumValid = true;
    let displayChecksum = report.proofChecksum;
    let canonicalSchemaChecksum: string | undefined = undefined;
    if (!options?.skipChecksumRecompute) {
      const recomputed = this.serializeLProofJson(initialPos, context, report);
      checksumValid = recomputed.checksum === report.proofChecksum;
      displayChecksum = recomputed.checksum;
      canonicalSchemaChecksum = this.computeCanonicalSchemaChecksum(
        initialPos,
        context,
        report
      );
    } else if (report.rootStatus !== ProofOutcome.Unknown) {
      canonicalSchemaChecksum = this.computeCanonicalSchemaChecksum(
        initialPos,
        context,
        report
      );
    }
    const expectedInputHash = initialPos.computeZobristHex();
    const inputHashValid = report.inputHash === expectedInputHash;

    let rootBindingValid = true;
    let rootBindingFailureCode = 'LP-R00';
    let rootBindingDetail = '';
    if (report.rootStatus !== ProofOutcome.Unknown) {
      const rootId = report.rootDagNodeId;
      const rootNode =
        rootId >= 0 && rootId < report.proofDagNodes.length
          ? report.proofDagNodes[rootId]
          : null;
      if (!rootNode) {
        rootBindingValid = false;
        rootBindingDetail = `缺失根节点 rootDagNodeId=${rootId}`;
      } else if (!isCompactDag && rootNode.stateId !== 0) {
        rootBindingValid = false;
        rootBindingDetail = `根节点 #${rootNode.nodeId} 未绑定初始状态 stateId=0 (实为 ${rootNode.stateId})`;
      } else if (rootNode.outcome !== report.rootStatus) {
        rootBindingValid = false;
        rootBindingDetail = `根结论 ${report.rootStatus} 与根节点 #${rootNode.nodeId} 结论 ${rootNode.outcome} 冲突`;
      } else if (
        (report.rootStatus === ProofOutcome.ProvenWin &&
          (report.rootPn !== 0 || report.rootDn !== PN_DN_SATURATION)) ||
        (report.rootStatus === ProofOutcome.ProvenLoss &&
          (report.rootPn !== PN_DN_SATURATION || report.rootDn !== 0))
      ) {
        rootBindingValid = false;
        rootBindingDetail = `报告根部 (rootPn=${report.rootPn}, rootDn=${report.rootDn}) 与 ${report.rootStatus} 不一致`;
      } else {
        // R4 §4 P1-C & R7 §3: Validate top-level `bestMove` & `bestMoveSgf` using shared canonical move label.
        // For NULL_MOVE (-2), both canonical `""` and JSON `null` are accepted; any mismatched string fails LP-R02.
        const bm = report.bestMove;
        const expectedBmSgf = moveToCanonicalSgf(bm, initialPos.boardSize);
        if (
          report.bestMoveSgf !== null &&
          report.bestMoveSgf !== undefined &&
          report.bestMoveSgf !== expectedBmSgf
        ) {
          rootBindingValid = false;
          rootBindingFailureCode = 'LP-R02';
          rootBindingDetail = `顶层 bestMove=${bm} 与 bestMoveSgf="${report.bestMoveSgf}" 不一致（期望 "${expectedBmSgf}"）`;
        } else {
          // Resolve redirected source root if root is TT/RZ reuse
          let effRoot: ProofDagNode | null = rootNode;
          const seenRoots = new Set<number>();
          while (
            effRoot &&
            (effRoot.isPrunedOutsideRz || effRoot.isTtHit) &&
            effRoot.sourceProofNodeId !== null &&
            effRoot.sourceProofNodeId >= 0 &&
            effRoot.sourceProofNodeId < report.proofDagNodes.length &&
            !seenRoots.has(effRoot.sourceProofNodeId)
          ) {
            seenRoots.add(effRoot.nodeId);
            effRoot = report.proofDagNodes[effRoot.sourceProofNodeId];
          }

          if (effRoot && effRoot.childNodeIds.length === 0) {
            if (bm !== PASS_MOVE && bm !== NULL_MOVE) {
              rootBindingValid = false;
              rootBindingFailureCode = 'LP-R02';
              rootBindingDetail = `终局叶根节点不允许声明非虚手 bestMove=${bm}`;
            }
          } else if (effRoot) {
            const rootExistential =
              (effRoot.isOrNode && effRoot.outcome === ProofOutcome.ProvenWin) ||
              (!effRoot.isOrNode &&
                effRoot.outcome === ProofOutcome.ProvenLoss);
            if (rootExistential) {
              const restrictedSide =
                (initialPos.toPlay === context.rootAttacker &&
                  !context.attackerAllowKo) ||
                (initialPos.toPlay !== context.rootAttacker &&
                  !context.defenderAllowKo);
              let matchedWitness = false;
              for (let k = 0; k < effRoot.childMoves.length; k++) {
                if (effRoot.childMoves[k] !== bm) continue;
                const cid = effRoot.childNodeIds[k];
                const chNode =
                  cid >= 0 && cid < report.proofDagNodes.length
                    ? report.proofDagNodes[cid]
                    : null;
                if (!chNode || chNode.outcome !== effRoot.outcome) continue;
                if (
                  bm !== PASS_MOVE &&
                  allowedRegionSet !== null &&
                  !allowedRegionSet.has(bm)
                ) {
                  continue;
                }
                const probe = initialPos.clone();
                const playRes = probe.playMove(bm);
                if (playRes.legal && !(playRes.isKoCapture && restrictedSide)) {
                  matchedWitness = true;
                  break;
                }
              }
              if (!matchedWitness) {
                rootBindingValid = false;
                rootBindingFailureCode = 'LP-R02';
                rootBindingDetail = `顶层 bestMove=${bm} (${String(
                  report.bestMoveSgf
                )}) 并非根节点 #${effRoot.nodeId} 下的合法有效见证着法`;
              }
            } else {
              // Universal root: bestMove must be PASS/NULL or one of the verified legal child moves
              const isChildMove = effRoot.childMoves.includes(bm);
              if (bm !== PASS_MOVE && bm !== NULL_MOVE && !isChildMove) {
                rootBindingValid = false;
                rootBindingFailureCode = 'LP-R02';
                rootBindingDetail = `全称根节点 #${effRoot.nodeId} 的顶层 bestMove=${bm} 不属于其合法子节点集合`;
              }
            }
          }
        }
      }
    }

    const chk01Passed = checksumValid && inputHashValid && rootBindingValid;
    if (!chk01Passed) {
      recordFailure(
        !checksumValid || !inputHashValid ? 'LP-C01' : rootBindingFailureCode,
        rootBindingFailureCode === 'LP-R02' ? report.rootDagNodeId : null
      );
    }

    auditChecks.push({
      checkId: 'CHK-01',
      requirementRef: 'FR-8.3 / FR-9.1',
      title: 'RFC 8785 JCS SHA-256 Checksum、InputHash 与根命题绑定校验',
      passed: chk01Passed,
      detail: chk01Passed
        ? `SHA-256=${displayChecksum.slice(0, 27)}... | InputHash=${
            report.inputHash
          } | Root=#${report.rootDagNodeId}`
        : `Checksum=${checksumValid}, InputHash=${inputHashValid} (${
            report.inputHash
          } vs ${expectedInputHash})${
            rootBindingDetail ? ` | ${rootBindingDetail}` : ''
          }`,
    });

    if (report.rootStatus === ProofOutcome.Unknown) {
      auditChecks.push({
        checkId: 'CHK-02',
        requirementRef: 'NFR-1 / FR-4.8',
        title: '根命题状态定论检查 (UNKNOWN Barrier)',
        passed: false,
        detail: `RootStatus=UNKNOWN (${report.unknownReason}); 仅 PROVEN_WIN / PROVEN_LOSS 生成完备定论证书。`,
      });
      return {
        ...commonMeta,
        passed: false,
        schemaVersion: 'lproof/1',
        jcsSha256Checksum: report.proofChecksum,
        verifiedNodes: 0,
        verifiedStates: 0,
        verifiedHistories: 0,
        replayedPrunedCertificates: 0,
        replayedTtHits: 0,
        failedNodeId: null,
        errorCode: firstErrorCode === 'PASS' ? 'LP-U01' : firstErrorCode,
        message: `根命题为 UNKNOWN (${report.unknownReason})，触发安全屏障（未做伪定论）。`,
        auditChecks,
      };
    }

    // Compute reachable node closure from `rootDagNodeId` (including sourceProofNodeId targets)
    const reachableNodeIds = new Set<number>();
    let indexingAndTopologyOk = report.proofDagNodes.length > 0;
    let topologyDetail = '';

    for (let i = 0; i < report.proofDagNodes.length; i++) {
      if (!report.proofDagNodes[i] || report.proofDagNodes[i].nodeId !== i) {
        indexingAndTopologyOk = false;
        topologyDetail = `DAG 节点数组索引 #${i} 与 nodeId=${report.proofDagNodes[i]?.nodeId} 不一致`;
        recordFailure('LP-T01', i);
        break;
      }
    }

    // Check 2: Zero-Trust StateTable & Canonical HistorySet Reconstruction (when not compact DAG)
    let stateReplayOk = isCompactDag ? true : report.stateTable.length > 0;
    let stateReplayDetail = '';
    const rebuiltPositions: GoPosition[] = isCompactDag
      ? []
      : new Array(report.stateTable.length);

    if (isCompactDag) {
      stateReplayDetail =
        '紧凑 DAG 模式（无外置 StateTable）：由独立 Checker 从初始局面按 DAG 边递归全量重放状态、历史集与令牌掩码。';
    } else if (!stateReplayOk) {
      stateReplayDetail = 'StateTable 为空，无法从初始局面恢复可达状态。';
      recordFailure('LP-S02');
    } else {
      for (let s = 0; s < report.stateTable.length; s++) {
        const st = report.stateTable[s];
        if (!st || st.stateId !== s) {
          stateReplayOk = false;
          stateReplayDetail = `StateTable 索引不连续：期望 stateId=${s}，实际 ${st?.stateId}`;
          recordFailure('LP-S02');
          break;
        }

        let expectedPos: GoPosition;
        if (s === 0) {
          if (st.parentStateId !== -1) {
            stateReplayOk = false;
            stateReplayDetail = `根状态 stateId=0 的 parentStateId 必须为 -1（实际 ${st.parentStateId}）`;
            recordFailure('LP-S02');
            break;
          }
          expectedPos = initialPos.clone();
        } else {
          if (st.parentStateId < 0 || st.parentStateId >= s) {
            stateReplayOk = false;
            stateReplayDetail = `State #${s} 的 parentStateId=${st.parentStateId} 越界或非拓扑前驱`;
            recordFailure('LP-S02');
            break;
          }
          if (
            st.moveFromParent !== PASS_MOVE &&
            allowedRegionSet !== null &&
            !allowedRegionSet.has(st.moveFromParent)
          ) {
            stateReplayOk = false;
            stateReplayDetail = `State #${s} 的转移着法 move=${st.moveFromParent} 超出题目声明的合法 region 集合`;
            recordFailure('LP-S11');
            break;
          }
          expectedPos = rebuiltPositions[st.parentStateId].clone();
          const playRes = expectedPos.playMove(st.moveFromParent);
          if (!playRes.legal) {
            stateReplayOk = false;
            stateReplayDetail = `State #${s} 从父状态 #${st.parentStateId} 落子 move=${st.moveFromParent} 非法`;
            recordFailure('LP-S09');
            break;
          }
        }

        const expectedZobrist = expectedPos.computeZobristHex();
        const expectedBlack = expectedPos.getBlackCoords();
        const expectedWhite = expectedPos.getWhiteCoords();
        const claimedHistory = report.historyTable[st.historyId];

        if (
          st.zobristHex !== expectedZobrist ||
          st.toPlay !== expectedPos.toPlay ||
          st.koPoint !== expectedPos.koPoint ||
          st.consecutivePasses !== expectedPos.consecutivePasses ||
          st.survivingTokensMask !== expectedPos.survivingTargetTokensMask ||
          !numberArraysEqual(st.blackCoords, expectedBlack) ||
          !numberArraysEqual(st.whiteCoords, expectedWhite) ||
          !historyTablesMatch(claimedHistory, expectedPos.historySnapshots)
        ) {
          stateReplayOk = false;
          stateReplayDetail = `State #${s} 字段与从初始局面合法回放的真实状态不一致（Zobrist/棋子/轮次/Ko/Pass/SurvivingTokensMask/HistoryTable 篡改拦截）`;
          recordFailure('LP-S02');
          break;
        }

        rebuiltPositions[s] = expectedPos;
      }
      if (stateReplayOk) {
        stateReplayDetail = `从初始输入严格回放验证全部 ${rebuiltPositions.length} 个可达状态、不可复活令牌掩码与 SSK/PSK HistorySet`;
      }
    }

    auditChecks.push({
      checkId: 'CHK-02',
      requirementRef: 'FR-2.2 / FR-2.6 / FR-9.2',
      title: 'StateTable 可达性重放、目标令牌掩码与 SSK/PSK 历史全量核验',
      passed: stateReplayOk,
      detail: stateReplayDetail,
    });

    // Check 3: Post-order topological acyclicity, LP-N15 (0, SAT)/(SAT, 0), & AND/OR role binding
    let lpN15AndRoleOk = indexingAndTopologyOk;
    if (indexingAndTopologyOk) {
      const queue: number[] = [];
      if (
        report.rootDagNodeId >= 0 &&
        report.rootDagNodeId < report.proofDagNodes.length
      ) {
        reachableNodeIds.add(report.rootDagNodeId);
        queue.push(report.rootDagNodeId);
      } else {
        lpN15AndRoleOk = false;
        topologyDetail = `rootDagNodeId=${report.rootDagNodeId} 越界`;
        recordFailure('LP-R00');
      }

      while (queue.length > 0 && lpN15AndRoleOk) {
        const nid = queue.pop()!;
        const node = report.proofDagNodes[nid];
        for (const cid of node.childNodeIds) {
          if (cid < 0 || cid >= node.nodeId || cid >= report.proofDagNodes.length) {
            lpN15AndRoleOk = false;
            topologyDetail = `节点 #${node.nodeId} 存在越界或违反后序无环约束的子节点 cid=${cid}`;
            recordFailure('LP-T02', node.nodeId);
            break;
          }
          if (!reachableNodeIds.has(cid)) {
            reachableNodeIds.add(cid);
            queue.push(cid);
          }
        }
        if (!lpN15AndRoleOk) break;

        if (node.isPrunedOutsideRz || node.isTtHit) {
          const sid = node.sourceProofNodeId;
          if (
            sid === null ||
            sid < 0 ||
            sid >= node.nodeId ||
            sid >= report.proofDagNodes.length
          ) {
            lpN15AndRoleOk = false;
            topologyDetail = `复用/剪枝节点 #${node.nodeId} 的 sourceProofNodeId=${sid} 非法或自引用成环`;
            recordFailure('LP-R01', node.nodeId);
            break;
          }
          if (!reachableNodeIds.has(sid)) {
            reachableNodeIds.add(sid);
            queue.push(sid);
          }
        }
      }

      for (const node of report.proofDagNodes) {
        if (!lpN15AndRoleOk) break;
        if (node.outcome === ProofOutcome.ProvenWin) {
          if (node.pn !== 0 || node.dn !== PN_DN_SATURATION) {
            lpN15AndRoleOk = false;
            topologyDetail = `节点 #${node.nodeId} (PROVEN_WIN) 违反 (PN=0, DN=SAT) 绑定`;
            recordFailure('LP-N15', node.nodeId);
            break;
          }
        } else if (node.outcome === ProofOutcome.ProvenLoss) {
          if (node.pn !== PN_DN_SATURATION || node.dn !== 0) {
            lpN15AndRoleOk = false;
            topologyDetail = `节点 #${node.nodeId} (PROVEN_LOSS) 违反 (PN=SAT, DN=0) 绑定`;
            recordFailure('LP-N15', node.nodeId);
            break;
          }
        } else if (reachableNodeIds.has(node.nodeId)) {
          lpN15AndRoleOk = false;
          topologyDetail = `可达证明闭包内节点 #${node.nodeId} 结论为 UNKNOWN`;
          recordFailure('LP-N15', node.nodeId);
          break;
        }

        for (const cid of node.childNodeIds) {
          if (cid < 0 || cid >= node.nodeId || cid >= report.proofDagNodes.length) {
            lpN15AndRoleOk = false;
            topologyDetail = `节点 #${node.nodeId} 违反后序拓扑约束 cid=${cid}`;
            recordFailure('LP-T02', node.nodeId);
            break;
          }
        }

        if (!isCompactDag && stateReplayOk && reachableNodeIds.has(node.nodeId)) {
          const pos = rebuiltPositions[node.stateId];
          const stateRow = report.stateTable[node.stateId];
          if (
            !pos ||
            !stateRow ||
            node.historyId < 0 ||
            node.historyId >= report.historyTable.length
          ) {
            lpN15AndRoleOk = false;
            topologyDetail = `节点 #${node.nodeId} 指向越界的 stateId=${node.stateId} 或 historyId=${node.historyId}`;
            recordFailure('LP-S02', node.nodeId);
            break;
          }
          const expectedIsOr = pos.toPlay === context.rootAttacker;
          if (node.toPlay !== pos.toPlay || node.isOrNode !== expectedIsOr) {
            lpN15AndRoleOk = false;
            topologyDetail = `节点 #${node.nodeId} 的轮次/AND-OR 角色与真实可达局面冲突`;
            recordFailure('LP-N10', node.nodeId);
            break;
          }
          if (
            node.historyId !== stateRow.historyId ||
            node.parentStateId !== stateRow.parentStateId
          ) {
            lpN15AndRoleOk = false;
            topologyDetail = `节点 #${node.nodeId} 的 historyId=${node.historyId} / parentStateId=${node.parentStateId} 与 stateTable[${node.stateId}] (historyId=${stateRow.historyId}, parentStateId=${stateRow.parentStateId}) 冲突`;
            recordFailure('LP-S10', node.nodeId);
            break;
          }
        }
      }
    }

    if (lpN15AndRoleOk) {
      topologyDetail = `可达闭包 ${reachableNodeIds.size} / ${report.proofDagNodes.length} 节点全部满足后序无环拓扑、LP-N15 饱和绑定与真实轮次角色`;
    }

    auditChecks.push({
      checkId: 'CHK-03',
      requirementRef: '§4.1 LP-N15 / LP-T02 / FR-8.3',
      title: '后序无环拓扑、LP-N15 饱和绑定与真实轮次 AND/OR 角色核验',
      passed: lpN15AndRoleOk,
      detail: topologyDetail,
    });

    // Compact DAG path (e.g., C++ CLI exported lproof/1 without StateTable)
    if (isCompactDag) {
      const stats = {
        verifiedStates: 0,
        verifiedLeaves: 0,
        verifiedUniversals: 0,
        replayedPruned: 0,
        replayedTt: 0,
      };
      let compactOk = chk01Passed && lpN15AndRoleOk;
      let compactDetail = '';
      if (!compactOk) {
        compactDetail = '前置校验未通过，中止紧凑 DAG 递归重放。';
      } else {
        const res = this.verifyCompactDagRecursive(
          initialPos.clone(),
          effectiveRegionMask,
          allowedRegionSet,
          context,
          report,
          report.rootDagNodeId,
          independentTerminal,
          0,
          stats,
          recordFailure
        );
        compactOk = res.ok;
        compactDetail = res.ok
          ? `递归重放验证 ${stats.verifiedStates} 个状态、${stats.verifiedLeaves} 个终局叶与 ${stats.verifiedUniversals} 个全称节点（region=${effectiveRegionCoords.length} 点）`
          : res.detail;
      }

      auditChecks.push({
        checkId: 'CHK-04',
        requirementRef: 'FR-3.1..FR-3.8 / FR-4.2 / FR-9.2',
        title: '可达终局叶独立重算、走子合法性、区域约束与全称覆盖核验',
        passed: compactOk,
        detail: compactDetail,
      });

      auditChecks.push({
        checkId: 'CHK-05',
        requirementRef: 'FR-5.5 / FR-5.6 / FR-6.9 / FR-9.3',
        title: 'OutsideRZRevalidated 与 TT 证明复用独立语义闭包重放',
        passed: compactOk,
        detail: compactOk
          ? `独立语义重放通过 ${stats.replayedPruned} 个 OutsideRZRevalidated 节点与 ${stats.replayedTt} 个 TT 复用节点`
          : compactDetail,
      });

      const allPassed = auditChecks.every((chk) => chk.passed);
      return {
        ...commonMeta,
        passed: allPassed,
        schemaVersion: 'lproof/1',
        jcsSha256Checksum: report.proofChecksum,
        canonicalDagChecksum: canonicalSchemaChecksum,
        verifiedNodes: reachableNodeIds.size,
        verifiedStates: stats.verifiedStates,
        verifiedHistories: stats.verifiedStates,
        replayedPrunedCertificates: stats.replayedPruned,
        replayedTtHits: stats.replayedTt,
        failedNodeId: failedNode,
        errorCode: allPassed
          ? 'PASS'
          : firstErrorCode === 'PASS'
          ? 'LP-S01'
          : firstErrorCode,
        message: allPassed
          ? `PASS — 独立 Proof Checker 完成紧凑 lproof/1 全图递归重放、区域约束与终局校验（scope=${effectiveScope}, region=${effectiveRegionCoords.length} 点）`
          : `FAIL (${firstErrorCode}) — 独立证明校验拒绝无效或不完备证书`,
        auditChecks,
      };
    }

    // Check 4: Independent Terminal Leaf Evaluation + Region & Edge Legality + Full Legal-Move Coverage
    let semanticsOk = stateReplayOk && lpN15AndRoleOk;
    let semanticsDetail = '';
    let verifiedLeafCount = 0;
    let verifiedUniversalCount = 0;

    if (!semanticsOk) {
      semanticsDetail = '前置状态重建或拓扑校验未通过，跳过叶节点与全覆盖归约放行。';
    } else {
      const sortedReachable = Array.from(reachableNodeIds).sort((a, b) => a - b);
      for (const nid of sortedReachable) {
        const node = report.proofDagNodes[nid];
        if (node.isPrunedOutsideRz || node.isTtHit) {
          continue; // Verified by full semantic replay in CHK-05
        }
        const pos = rebuiltPositions[node.stateId];

        if (node.childNodeIds.length === 0) {
          verifiedLeafCount++;
          const termRes = independentTerminal.evaluateTerminal(pos, context);
          const expectedStatus =
            node.outcome === ProofOutcome.ProvenWin
              ? TerminalStatus.Win
              : TerminalStatus.Loss;
          if (termRes.status !== expectedStatus) {
            semanticsOk = false;
            semanticsDetail = `叶节点 #${node.nodeId} 独立终局复算失败：声称 ${node.outcome}，实测 ${termRes.status} (${termRes.evidenceKind})`;
            recordFailure('LP-L04', node.nodeId);
            break;
          }
        } else {
          if (node.childMoves.length !== node.childNodeIds.length) {
            semanticsOk = false;
            semanticsDetail = `内部节点 #${node.nodeId} 的 childMoves (${node.childMoves.length}) 与 childNodeIds (${node.childNodeIds.length}) 数量不一致`;
            recordFailure('LP-N11', node.nodeId);
            break;
          }

          const moveToEdge = new Map<
            number,
            { cid: number; isKoCapture: boolean }
          >();
          for (let k = 0; k < node.childNodeIds.length; k++) {
            const mv = node.childMoves[k];
            const cid = node.childNodeIds[k];
            if (moveToEdge.has(mv)) {
              semanticsOk = false;
              semanticsDetail = `内部节点 #${node.nodeId} 存在重复着法边 move=${mv}`;
              recordFailure('LP-N11', node.nodeId);
              break;
            }
            // R3 F1: EVERY proof edge (including existential witnesses) must lie inside declared region or be PASS
            if (
              mv !== PASS_MOVE &&
              allowedRegionSet !== null &&
              !allowedRegionSet.has(mv)
            ) {
              semanticsOk = false;
              semanticsDetail = `内部节点 #${node.nodeId} 的着法边 ${coordToSgf(
                mv,
                pos.boardSize
              )} (move=${mv}) 超出题目声明的合法 region 集合`;
              recordFailure('LP-S11', node.nodeId);
              break;
            }
            const stepPos = pos.clone();
            const playRes = stepPos.playMove(mv);
            if (!playRes.legal) {
              semanticsOk = false;
              semanticsDetail = `内部节点 #${node.nodeId} 包含非法着法边 move=${mv}`;
              recordFailure('LP-S09', node.nodeId);
              break;
            }
            const childNode = report.proofDagNodes[cid];
            const childState = report.stateTable[childNode.stateId];
            if (
              !childState ||
              childState.parentStateId !== node.stateId ||
              childState.moveFromParent !== mv ||
              childNode.incomingMove !== mv
            ) {
              semanticsOk = false;
              semanticsDetail = `内部节点 #${node.nodeId} -> 子节点 #${cid} (move=${mv}) 状态转移与 StateTable 不匹配`;
              recordFailure('LP-S10', node.nodeId);
              break;
            }
            moveToEdge.set(mv, { cid, isKoCapture: playRes.isKoCapture });
          }
          if (!semanticsOk) break;

          const restrictedSide =
            (pos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
            (pos.toPlay !== context.rootAttacker && !context.defenderAllowKo);
          const existentialMode =
            (node.isOrNode && node.outcome === ProofOutcome.ProvenWin) ||
            (!node.isOrNode && node.outcome === ProofOutcome.ProvenLoss);

          if (existentialMode) {
            let hasValidWitness = false;
            for (const [, edge] of moveToEdge) {
              const chNode = report.proofDagNodes[edge.cid];
              if (
                chNode.outcome === node.outcome &&
                !(edge.isKoCapture && restrictedSide)
              ) {
                hasValidWitness = true;
                break;
              }
            }
            if (!hasValidWitness) {
              semanticsOk = false;
              semanticsDetail = `单见证节点 #${node.nodeId} 缺少合法非禁劫的同结论见证子节点`;
              recordFailure('LP-N21', node.nodeId);
              break;
            }
          } else {
            verifiedUniversalCount++;
            const expectedLegalMoves = pos.generateLegalMoves(
              effectiveRegionMask
            );
            for (const lm of expectedLegalMoves) {
              const edge = moveToEdge.get(lm);
              if (!edge) {
                semanticsOk = false;
                semanticsDetail = `全覆盖节点 #${node.nodeId} 遗漏合法应手 ${coordToSgf(
                  lm,
                  pos.boardSize
                )} (move=${lm})，未履行全称覆盖义务`;
                recordFailure('LP-N22', node.nodeId);
                break;
              }
              const chNode = report.proofDagNodes[edge.cid];
              if (chNode.outcome !== node.outcome) {
                semanticsOk = false;
                semanticsDetail = `全覆盖节点 #${node.nodeId} 的应手 ${coordToSgf(
                  lm,
                  pos.boardSize
                )} 子节点 #${edge.cid} 结论不一致`;
                recordFailure('LP-N22', node.nodeId);
                break;
              }
            }
            if (!semanticsOk) break;
          }
        }
      }
    }

    if (semanticsOk) {
      semanticsDetail = `独立验证 ${verifiedLeafCount} 个可达终局叶节点与 ${verifiedUniversalCount} 个全称节点的区域约束与完整合法应手覆盖（region=${effectiveRegionCoords.length} 点）`;
    }

    auditChecks.push({
      checkId: 'CHK-04',
      requirementRef: 'FR-3.1..FR-3.8 / FR-4.2 / FR-9.2',
      title: '可达终局叶独立重算、区域约束与全称节点完整应手覆盖核验',
      passed: semanticsOk,
      detail: semanticsDetail,
    });

    // Check 5: Independent Semantic Replay of ALL Reachable OutsideRZRevalidated & TT-Reuse Nodes
    let reuseReplayOk = stateReplayOk && lpN15AndRoleOk;
    let reuseReplayDetail = '';
    let replayedPrunedCount = 0;
    let replayedTtCount = 0;

    for (const n of report.proofDagNodes) {
      if (n.isPrunedOutsideRz) {
        if (
          !n.prunedCertificate ||
          n.prunedCertificate.reason !== 'OutsideRZRevalidated' ||
          n.sourceProofNodeId === null ||
          n.prunedCertificate.sourceProofNodeId !== n.sourceProofNodeId ||
          n.prunedCertificate.queryStateId !== n.stateId ||
          n.sourceProofNodeId < 0 ||
          n.sourceProofNodeId >= n.nodeId
        ) {
          reuseReplayOk = false;
          reuseReplayDetail = `RZ 剪枝节点 #${n.nodeId} 缺失合法的 PrunedCertificateRecord 或源节点越界`;
          recordFailure('LP-R02', n.nodeId);
          break;
        }
      }
    }

    if (reuseReplayOk) {
      const sortedReachable = Array.from(reachableNodeIds).sort((a, b) => a - b);
      for (const nid of sortedReachable) {
        const node = report.proofDagNodes[nid];
        if (!node.isPrunedOutsideRz && !node.isTtHit) continue;
        const queryPos = rebuiltPositions[node.stateId];
        const ok = this.replaySourceSubgraphOnQueryState(
          queryPos,
          effectiveRegionMask,
          context,
          report.proofDagNodes,
          node.sourceProofNodeId!,
          node.outcome,
          independentTerminal,
          0
        );
        if (!ok) {
          reuseReplayOk = false;
          reuseReplayDetail = `${
            node.isPrunedOutsideRz ? 'OutsideRZRevalidated' : 'TT-Reuse'
          } 节点 #${node.nodeId} 在真实可达 QueryState+HistorySet 下重放源证明 #${
            node.sourceProofNodeId
          } 失败`;
          recordFailure('LP-R03', node.nodeId);
          break;
        }
        if (node.isPrunedOutsideRz) replayedPrunedCount++;
        if (node.isTtHit) replayedTtCount++;
      }
    }

    if (reuseReplayOk) {
      reuseReplayDetail = `独立语义重放通过 ${replayedPrunedCount} 个 OutsideRZRevalidated 证书节点与 ${replayedTtCount} 个 TT 复用节点`;
    }

    auditChecks.push({
      checkId: 'CHK-05',
      requirementRef: 'FR-5.5 / FR-5.6 / FR-6.9 / FR-9.3',
      title: 'OutsideRZRevalidated 与 TT 证明复用独立语义闭包重放',
      passed: reuseReplayOk,
      detail: reuseReplayDetail,
    });

    const allPassed =
      auditChecks.length > 0 && auditChecks.every((chk) => chk.passed);

    return {
      ...commonMeta,
      passed: allPassed,
      schemaVersion: 'lproof/1',
      jcsSha256Checksum: report.proofChecksum,
      canonicalDagChecksum: canonicalSchemaChecksum,
      verifiedNodes: reachableNodeIds.size,
      verifiedStates: stateReplayOk ? rebuiltPositions.length : 0,
      verifiedHistories: stateReplayOk ? rebuiltPositions.length : 0,
      replayedPrunedCertificates: replayedPrunedCount,
      replayedTtHits: replayedTtCount,
      failedNodeId: failedNode,
      errorCode: allPassed
        ? 'PASS'
        : firstErrorCode === 'PASS'
        ? 'LP-S01'
        : firstErrorCode,
      message: allPassed
        ? `PASS — 独立 Proof Checker 完成状态可达重建、区域约束、全称合法着覆盖与 RZ/TT 语义重放（scope=${effectiveScope}, region=${effectiveRegionCoords.length} 点）`
        : `FAIL (${firstErrorCode}) — 独立证明校验拒绝无效或不完备证书`,
      auditChecks,
    };
  }

  /**
   * R11/R12: Independent sub-proof fragment verifier for a specific DAG node captured inside
   * a SolveReport (including UNKNOWN original-root runs and standalone subposition runs).
   *
   * Enforces:
   * 1. Problem-intrinsic contract binding (goal, attacker/defender role, crucial stones/op, board,
   *    walls, region) plus runtime config parity against the report's bound lproof/1 contract.
   * 2. Authentic runSource & runStartMoves derivation from the report's verified starting state and
   *    arrival trace, strictly separating `runRootOutcome` from `originalRootOutcome` (which is
   *    `null` for standalone subposition runs unless an authentic original-root report is supplied).
   * 3. Full stateTable/historyTable index, cross-table, descendant, and TT/RZ source binding when
   *    full tables are present (`verificationMode: 'full_state_table'`), plus explicit distinction
   *    between unclosed sentinel (`targetDagNodeId === -1` -> `UNCLOSED / LP-U01`) and corrupted
   *    out-of-bounds positive indices (`VERIFICATION_FAILED / LP-N01`).
   */
  public verifySubproofFragment(params: {
    problem: TsumegoProblemSpec;
    context?: ProofContext;
    report: SolveReport;
    targetPathMoves: number[];
    targetDagNodeId: number;
    queryPathMoves?: number[];
    runSource?: 'original_root' | 'standalone_subposition';
    originalRootReport?: SolveReport;
  }): SubproofFragmentVerificationResult {
    const {
      problem,
      report,
      targetPathMoves,
      targetDagNodeId,
      queryPathMoves,
    } = params;
    const hasFullTables =
      Array.isArray(report.stateTable) && report.stateTable.length > 0;
    const verificationMode: LProofEncodingMode = hasFullTables
      ? 'full_state_table'
      : 'compact_dag';

    const targetPathSgf = targetPathMoves.map((mv) =>
      coordToSgf(mv, problem.boardSize)
    );
    const queryPathSgf = (queryPathMoves ?? []).map((mv) =>
      coordToSgf(mv, problem.boardSize)
    );

    let derivedRunSource: 'original_root' | 'standalone_subposition' =
      params.runSource ??
      report.branchCoverageSnapshots?.[0]?.runSource ??
      'standalone_subposition';
    let runStartMoves: number[] = [];
    let runStartPathSgf: string[] = [];
    let originalRootOutcome: ProofOutcome | null = null;
    let originalRootNodes: number | null = null;
    let originalRootBindingNote: string | undefined = undefined;

    const notRequestedQuery: SubproofQueryReplayReceipt = {
      status: 'NOT_REQUESTED',
      passed: false,
      errorCode: 'NONE',
      message: '未指定跨局面重放查询路径。',
      sourceDagNodeId: targetDagNodeId,
      queryPathSgf: [],
      queryHistoryLength: 0,
    };

    const makeSourceFail = (
      status: SubproofSourceReceipt['status'],
      errorCode: string,
      message: string,
      failedNodeId: number | null = null,
      outcome: ProofOutcome = ProofOutcome.Unknown
    ): SubproofFragmentVerificationResult => ({
      runSource: derivedRunSource,
      runStartPathSgf,
      runRootOutcome: report.rootStatus,
      originalRootOutcome,
      originalRootNodes,
      ...(originalRootBindingNote !== undefined
        ? { originalRootBindingNote }
        : {}),
      sourceReceipt: {
        status,
        passed: false,
        errorCode,
        message,
        scope: 'subproof_fragment',
        verificationMode,
        targetPathSgf,
        targetDagNodeId,
        outcome,
        verifiedNodes: 0,
        verifiedLeaves: 0,
        verifiedUniversals: 0,
        replayedPruned: 0,
        replayedTt: 0,
        failedNodeId,
      },
      queryReplayReceipt: queryPathMoves
        ? {
            status: 'QUERY_REPLAY_FAILED',
            passed: false,
            errorCode,
            message: `因源片段未通过校验（${errorCode}），跳过查询局面重放。`,
            sourceDagNodeId: targetDagNodeId,
            queryPathSgf,
            queryHistoryLength: 0,
          }
        : notRequestedQuery,
    });

    // 1. Validate region contract consistency first (R8 §3)
    if (
      problem.hasRegionHint !== undefined &&
      typeof problem.hasRegionHint !== 'boolean'
    ) {
      return makeSourceFail(
        'VERIFICATION_FAILED',
        'LP-J02',
        '原题 hasRegionHint 类型非法。'
      );
    }
    if (problem.hasRegionHint === false && problem.regionCoords.length > 0) {
      return makeSourceFail(
        'VERIFICATION_FAILED',
        'LP-J02',
        '原题存在矛盾区域声明：hasRegionHint=false 且 regionCoords 非空。'
      );
    }

    const hasRegionHint =
      problem.hasRegionHint !== undefined
        ? problem.hasRegionHint
        : problem.regionCoords.length > 0;
    const effectiveRegionMask: number[] | null = hasRegionHint
      ? problem.regionCoords.slice()
      : null;
    const allowedRegionSet: Set<number> | null = hasRegionHint
      ? new Set<number>(problem.regionCoords)
      : null;

    // 2. R12 §2: Derive problem-intrinsic context independently and reject goal/role/token conflicts
    const canonicalProbCtx = deriveDefaultProofContextFromProblem(
      problem,
      params.context?.koRule ?? KoRule.SituationalSuperko
    );
    const sameTokens = (
      a: ProofContext['initialTokens'],
      b: ProofContext['initialTokens']
    ): boolean =>
      a.length === b.length &&
      a.every(
        (t, idx) =>
          t.initialCoord === b[idx].initialCoord &&
          t.stoneColor === b[idx].stoneColor &&
          t.groupIndex === b[idx].groupIndex
      );

    if (params.context) {
      const pc = params.context;
      if (
        pc.rootAttacker !== canonicalProbCtx.rootAttacker ||
        pc.attackerGoal !== canonicalProbCtx.attackerGoal ||
        pc.crucialStoneOp !== canonicalProbCtx.crucialStoneOp ||
        !sameTokens(pc.initialTokens, canonicalProbCtx.initialTokens)
      ) {
        return makeSourceFail(
          'VERIFICATION_FAILED',
          'LP-P01',
          `传入上下文与原题 "${problem.id}" 的攻防角色/目标 (${canonicalProbCtx.attackerGoal}) 或关键子令牌契约冲突。`
        );
      }
    }
    const context: ProofContext = params.context ?? canonicalProbCtx;

    // 3. R13 §3: Unified run-contract validator across SolveReport, runContract, configFingerprint, and lproofJson
    const expWall = sortedUniqueNumbers(problem.immortalWallCoords);
    const expRegion = hasRegionHint
      ? sortedUniqueNumbers(problem.regionCoords)
      : [];

    const buildOriginalRootPos = (): GoPosition => {
      const pos = new GoPosition(
        context,
        problem.boardSize,
        problem.immortalWallCoords
      );
      const firstToPlay =
        problem.turnColor === 'W' ? Color.White : Color.Black;
      pos.setupInitialStones(
        problem.blackInitialCoords,
        problem.whiteInitialCoords,
        firstToPlay
      );
      return pos;
    };

    const replayPathFromOriginalRoot = (
      moves: number[],
      enforceRegionAndKo = true
    ): { ok: true; pos: GoPosition } | { ok: false; code: string; detail: string } => {
      const pos = buildOriginalRootPos();
      for (let i = 0; i < moves.length; i++) {
        const mv = moves[i];
        const restrictedSide =
          (pos.toPlay === context.rootAttacker && !context.attackerAllowKo) ||
          (pos.toPlay !== context.rootAttacker && !context.defenderAllowKo);
        if (
          enforceRegionAndKo &&
          mv !== PASS_MOVE &&
          allowedRegionSet !== null &&
          !allowedRegionSet.has(mv)
        ) {
          return {
            ok: false,
            code: 'LP-S11',
            detail: `路径第 ${i + 1} 手 ${coordToSgf(mv, problem.boardSize)} 越出声明区域`,
          };
        }
        const playRes = pos.playMove(mv);
        if (!playRes.legal) {
          return {
            ok: false,
            code: 'LP-S09',
            detail: `路径第 ${i + 1} 手 ${coordToSgf(mv, problem.boardSize)} 非法`,
          };
        }
        if (enforceRegionAndKo && playRes.isKoCapture && restrictedSide) {
          return {
            ok: false,
            code: 'LP-S12',
            detail: `路径第 ${i + 1} 手 ${coordToSgf(mv, problem.boardSize)} 违反禁劫规则`,
          };
        }
      }
      return { ok: true, pos };
    };

    const origPos = buildOriginalRootPos();
    const expOrigBlack = origPos.getBlackCoords();
    const expOrigWhite = origPos.getWhiteCoords();
    const expOrigTurn = origPos.toPlay;
    const expOrigHash = origPos.computeZobristHex();

    type ValidatedReportContract =
      | {
          ok: true;
          derivedRunSource: 'original_root' | 'standalone_subposition';
          runStartMoves: number[];
          runStartPos: GoPosition;
          hasEmbeddedLproof: boolean;
        }
      | { ok: false; code: string; detail: string };

    const validateRunReportContract = (
      candReport: SolveReport
    ): ValidatedReportContract => {
      // (a) Outer SolveReport board / wall / 3-state region
      if (
        candReport.hasRegionHint !== undefined &&
        typeof candReport.hasRegionHint !== 'boolean'
      ) {
        return {
          ok: false,
          code: 'LP-J02',
          detail: '报告 hasRegionHint 类型非法（必须为布尔值或省略）。',
        };
      }
      if (
        candReport.hasRegionHint === false &&
        (candReport.regionCoords?.length ?? 0) > 0
      ) {
        return {
          ok: false,
          code: 'LP-J02',
          detail: '报告存在矛盾区域声明：hasRegionHint=false 且 regionCoords 非空。',
        };
      }
      const candWall = sortedUniqueNumbers(candReport.immortalWallCoords ?? []);
      const candHasRegion =
        candReport.hasRegionHint !== undefined
          ? candReport.hasRegionHint
          : (candReport.regionCoords?.length ?? 0) > 0;
      const candRegion = candHasRegion
        ? sortedUniqueNumbers(candReport.regionCoords ?? [])
        : [];

      if (
        candReport.boardSize !== problem.boardSize ||
        !numberArraysEqual(candWall, expWall) ||
        candHasRegion !== hasRegionHint ||
        !numberArraysEqual(candRegion, expRegion)
      ) {
        return {
          ok: false,
          code: 'LP-P01',
          detail: `报告产物的棋盘尺寸/围墙/区域声明与原题 "${problem.id}" 不一致。`,
        };
      }

      // (b) Structured runContract metadata (persisted on in-memory SolveReport)
      if (candReport.runContract !== undefined) {
        const rc = candReport.runContract;
        if (!rc || typeof rc !== 'object' || typeof rc.hasRegionHint !== 'boolean') {
          return {
            ok: false,
            code: 'LP-J02',
            detail: '报告 runContract 字段结构非法。',
          };
        }
        if (rc.hasRegionHint === false && rc.regionCoords.length > 0) {
          return {
            ok: false,
            code: 'LP-J02',
            detail: '报告 runContract 存在矛盾区域声明。',
          };
        }
        const rcWall = sortedUniqueNumbers(rc.immortalWallCoords ?? []);
        const rcRegion = rc.hasRegionHint
          ? sortedUniqueNumbers(rc.regionCoords ?? [])
          : [];
        if (
          rc.boardSize !== problem.boardSize ||
          !numberArraysEqual(rcWall, expWall) ||
          rc.hasRegionHint !== hasRegionHint ||
          !numberArraysEqual(rcRegion, expRegion) ||
          rc.rootAttacker !== context.rootAttacker ||
          rc.attackerGoal !== context.attackerGoal ||
          rc.crucialStoneOp !== context.crucialStoneOp ||
          rc.koRule !== context.koRule ||
          rc.attackerAllowKo !== context.attackerAllowKo ||
          rc.defenderAllowKo !== context.defenderAllowKo ||
          !sameTokens(rc.initialTokens ?? [], context.initialTokens)
        ) {
          return {
            ok: false,
            code: 'LP-P01',
            detail: '报告 runContract（棋盘/围墙/区域/攻防目标/关键子/劫规则/劫权）与当前待验原题或运行上下文不一致。',
          };
        }
      }

      // (c) Defense-in-depth configFingerprint parity (covers stripped-lproofJson / legacy reports)
      if (
        typeof candReport.configFingerprint === 'string' &&
        candReport.configFingerprint.length > 0
      ) {
        const koMatch = candReport.configFingerprint.match(
          /:(SSK|PSK|SIMPLE):/
        );
        if (koMatch && koMatch[1] !== context.koRule) {
          return {
            ok: false,
            code: 'LP-P01',
            detail: `报告 configFingerprint 的劫规则 (${koMatch[1]}) 与待验上下文 (${context.koRule}) 不一致。`,
          };
        }
        const akoDkoMatch = candReport.configFingerprint.match(
          /:ako=(true|false):dko=(true|false)(?::|$)/
        );
        if (akoDkoMatch) {
          const fpAko = akoDkoMatch[1] === 'true';
          const fpDko = akoDkoMatch[2] === 'true';
          if (
            fpAko !== context.attackerAllowKo ||
            fpDko !== context.defenderAllowKo
          ) {
            return {
              ok: false,
              code: 'LP-P01',
              detail: `报告 configFingerprint 的劫权 (ako=${fpAko}, dko=${fpDko}) 与待验上下文 (ako=${context.attackerAllowKo}, dko=${context.defenderAllowKo}) 不一致。`,
            };
          }
        }
      }

      const candStartBlack = sortedUniqueNumbers(
        candReport.blackInitialCoords ?? []
      );
      const candStartWhite = sortedUniqueNumbers(
        candReport.whiteInitialCoords ?? []
      );

      let parsedLproof: Record<string, unknown> | null = null;
      if (
        candReport.lproofJson !== undefined &&
        candReport.lproofJson !== null &&
        typeof candReport.lproofJson !== 'string'
      ) {
        return {
          ok: false,
          code: 'LP-J01',
          detail: '报告内嵌的 lproofJson 类型非法（非字符串）。',
        };
      }
      if (
        typeof candReport.lproofJson === 'string' &&
        candReport.lproofJson.trim().length > 0
      ) {
        try {
          const obj = JSON.parse(candReport.lproofJson);
          if (!obj || typeof obj !== 'object' || Array.isArray(obj)) {
            return {
              ok: false,
              code: 'LP-J01',
              detail: '报告内嵌的 lproofJson 顶层不是合法 JSON 对象。',
            };
          }
          parsedLproof = obj as Record<string, unknown>;
        } catch {
          return {
            ok: false,
            code: 'LP-J01',
            detail: '报告内嵌的 lproofJson 无法解析为合法 JSON。',
          };
        }
      }

      let candRunSource: 'original_root' | 'standalone_subposition' =
        'original_root';
      let candStartMoves: number[] = [];

      if (parsedLproof) {
        // (d) Mandatory lproof/1 contract & cross-binding with outer SolveReport (R13 §3)
        if (parsedLproof.magic !== 'lproof/1') {
          return {
            ok: false,
            code: 'LP-J02',
            detail: `报告内嵌 lproofJson 的 magic="${String(
              parsedLproof.magic
            )}" 非法（必须为 "lproof/1"）。`,
          };
        }

        const lpCtx = parsedLproof.context;
        if (!lpCtx || typeof lpCtx !== 'object' || Array.isArray(lpCtx)) {
          return {
            ok: false,
            code: 'LP-J02',
            detail: '报告内嵌 lproofJson 缺失必需的 context 契约对象，拒绝跳过核验。',
          };
        }
        const ctxObj = lpCtx as Record<string, unknown>;
        const lpAttacker = decodeColor(ctxObj.rootAttacker);
        const lpGoal = ctxObj.attackerGoal;
        const lpOp = ctxObj.crucialStoneOp;
        const lpKoRule = ctxObj.koRule;
        const lpAttKo = ctxObj.attackerAllowKo;
        const lpDefKo = ctxObj.defenderAllowKo;
        const lpTokens = Array.isArray(ctxObj.initialTokens)
          ? (ctxObj.initialTokens as Record<string, unknown>[])
          : null;
        if (
          lpAttacker === null ||
          typeof lpGoal !== 'string' ||
          typeof lpOp !== 'string' ||
          typeof lpKoRule !== 'string' ||
          typeof lpAttKo !== 'boolean' ||
          typeof lpDefKo !== 'boolean' ||
          lpTokens === null
        ) {
          return {
            ok: false,
            code: 'LP-J02',
            detail: '报告内嵌 lproofJson.context 缺少必需字段或字段类型非法。',
          };
        }
        const tokensEqual =
          lpTokens.length === context.initialTokens.length &&
          lpTokens.every((t, idx) => {
            if (!t || typeof t !== 'object') return false;
            const c = decodeColor(t.stoneColor);
            return (
              t.initialCoord === context.initialTokens[idx].initialCoord &&
              c === context.initialTokens[idx].stoneColor &&
              t.groupIndex === context.initialTokens[idx].groupIndex
            );
          });
        if (
          lpAttacker !== context.rootAttacker ||
          lpGoal !== context.attackerGoal ||
          lpOp !== context.crucialStoneOp ||
          lpKoRule !== context.koRule ||
          lpAttKo !== context.attackerAllowKo ||
          lpDefKo !== context.defenderAllowKo ||
          !tokensEqual
        ) {
          return {
            ok: false,
            code: 'LP-P01',
            detail: '报告已绑定的 lproof/1 契约上下文（攻防目标/关键子/劫规则/劫权）与当前待验命题及运行配置不一致。',
          };
        }

        const lpSetupRaw = parsedLproof.problemSetup;
        if (
          !lpSetupRaw ||
          typeof lpSetupRaw !== 'object' ||
          Array.isArray(lpSetupRaw)
        ) {
          return {
            ok: false,
            code: 'LP-J02',
            detail: '报告内嵌 lproofJson 缺失必需的 problemSetup 对象，拒绝跳过核验。',
          };
        }
        const lpSetup = lpSetupRaw as Record<string, unknown>;

        // Mandatory boardSize, walls, and 3-state region binding on lproof.problemSetup
        if (
          typeof lpSetup.boardSize !== 'number' ||
          !Number.isInteger(lpSetup.boardSize) ||
          !isIntegerArray(lpSetup.immortalWallCoords) ||
          !isIntegerArray(lpSetup.regionCoords) ||
          (lpSetup.hasRegionHint !== undefined &&
            typeof lpSetup.hasRegionHint !== 'boolean')
        ) {
          return {
            ok: false,
            code: 'LP-J02',
            detail: '报告内嵌 lproofJson.problemSetup 的棋盘尺寸/围墙/区域字段缺失或类型非法。',
          };
        }
        if (lpSetup.hasRegionHint === false && lpSetup.regionCoords.length > 0) {
          return {
            ok: false,
            code: 'LP-J02',
            detail: '报告内嵌 lproofJson.problemSetup 存在矛盾区域声明：hasRegionHint=false 且 regionCoords 非空。',
          };
        }
        const lpWall = sortedUniqueNumbers(lpSetup.immortalWallCoords);
        const lpHasRegion =
          lpSetup.hasRegionHint !== undefined
            ? lpSetup.hasRegionHint
            : lpSetup.regionCoords.length > 0;
        const lpRegion = lpHasRegion
          ? sortedUniqueNumbers(lpSetup.regionCoords)
          : [];
        if (
          lpSetup.boardSize !== problem.boardSize ||
          !numberArraysEqual(lpWall, expWall) ||
          lpHasRegion !== hasRegionHint ||
          !numberArraysEqual(lpRegion, expRegion)
        ) {
          return {
            ok: false,
            code: 'LP-P01',
            detail: `报告内嵌 lproofJson.problemSetup 的棋盘尺寸/围墙/区域声明与原题 "${problem.id}" 不一致。`,
          };
        }

        // Cross-bind lproofJson start board, inputHash, rootOutcome, and rootNode to outer SolveReport
        const lpFirst = decodeColor(lpSetup.firstToPlay);
        if (
          lpFirst === null ||
          !isIntegerArray(lpSetup.blackInitialCoords) ||
          !isIntegerArray(lpSetup.whiteInitialCoords) ||
          typeof lpSetup.inputHash !== 'string'
        ) {
          return {
            ok: false,
            code: 'LP-J02',
            detail: '报告内嵌 lproofJson.problemSetup 缺少起始棋面/先手/inputHash。',
          };
        }
        if (
          lpFirst !== candReport.firstToPlay ||
          !numberArraysEqual(
            sortedUniqueNumbers(lpSetup.blackInitialCoords),
            candStartBlack
          ) ||
          !numberArraysEqual(
            sortedUniqueNumbers(lpSetup.whiteInitialCoords),
            candStartWhite
          ) ||
          lpSetup.inputHash !== candReport.inputHash ||
          parsedLproof.rootOutcome !== candReport.rootStatus ||
          parsedLproof.rootNode !== candReport.rootDagNodeId
        ) {
          return {
            ok: false,
            code: 'LP-P01',
            detail: '内存报告与内嵌 lproofJson 的起始局面、inputHash、rootOutcome 或 rootNode 不一致（疑似串用异次运行证书）。',
          };
        }

        const rootKind = lpSetup.rootKind;
        if (rootKind === 'traced_subposition') {
          const originTurn = decodeColor(lpSetup.originFirstToPlay);
          if (
            originTurn === null ||
            !isIntegerArray(lpSetup.originBlackCoords) ||
            !isIntegerArray(lpSetup.originWhiteCoords) ||
            !isIntegerArray(lpSetup.initialTraceMoves) ||
            lpSetup.initialTraceMoves.length === 0
          ) {
            return {
              ok: false,
              code: 'LP-J02',
              detail: '独立子局面产物缺少合法的 originBlackCoords / originWhiteCoords / originFirstToPlay / initialTraceMoves。',
            };
          }
          if (
            originTurn !== expOrigTurn ||
            !numberArraysEqual(
              sortedUniqueNumbers(lpSetup.originBlackCoords),
              expOrigBlack
            ) ||
            !numberArraysEqual(
              sortedUniqueNumbers(lpSetup.originWhiteCoords),
              expOrigWhite
            )
          ) {
            return {
              ok: false,
              code: 'LP-P01',
              detail: `独立子局面产物的原根起点与待验原题 "${problem.id}" 不一致。`,
            };
          }
          candStartMoves = lpSetup.initialTraceMoves.slice();
          candRunSource = 'standalone_subposition';
        } else if (rootKind === 'initial') {
          if (
            lpSetup.initialTraceMoves !== undefined &&
            (!isIntegerArray(lpSetup.initialTraceMoves) ||
              lpSetup.initialTraceMoves.length > 0)
          ) {
            return {
              ok: false,
              code: 'LP-P02',
              detail: '产物声称 rootKind="initial" 却携带非空 initialTraceMoves。',
            };
          }
          if (
            lpFirst !== expOrigTurn ||
            !numberArraysEqual(
              sortedUniqueNumbers(lpSetup.blackInitialCoords),
              expOrigBlack
            ) ||
            !numberArraysEqual(
              sortedUniqueNumbers(lpSetup.whiteInitialCoords),
              expOrigWhite
            )
          ) {
            return {
              ok: false,
              code: 'LP-P01',
              detail: `产物初始局面与待验原题 "${problem.id}" 不一致。`,
            };
          }
          candStartMoves = [];
          candRunSource = 'original_root';
        } else {
          return {
            ok: false,
            code: 'LP-J02',
            detail: `报告内嵌 lproofJson.problemSetup.rootKind="${String(
              rootKind
            )}" 非法。`,
          };
        }

        if (candReport.runContract !== undefined) {
          if (
            candReport.runContract.rootKind !== rootKind ||
            !numberArraysEqual(
              candReport.runContract.initialTraceMoves ?? [],
              candStartMoves
            )
          ) {
            return {
              ok: false,
              code: 'LP-P01',
              detail: '内存报告 runContract 的 rootKind / initialTraceMoves 与内嵌 lproofJson 不一致。',
            };
          }
        }
      } else if (
        candReport.runContract !== undefined &&
        candReport.runContract.rootKind === 'traced_subposition'
      ) {
        if (
          !isIntegerArray(candReport.runContract.initialTraceMoves) ||
          candReport.runContract.initialTraceMoves.length === 0
        ) {
          return {
            ok: false,
            code: 'LP-J02',
            detail: '无 lproofJson 的独立子局面报告缺失合法的 runContract.initialTraceMoves。',
          };
        }
        candStartMoves = candReport.runContract.initialTraceMoves.slice();
        candRunSource = 'standalone_subposition';
      } else {
        // No embedded lproofJson: derive strictly by comparing report's starting position to problem root
        const matchesOrigRoot =
          candReport.firstToPlay === expOrigTurn &&
          numberArraysEqual(candStartBlack, expOrigBlack) &&
          numberArraysEqual(candStartWhite, expOrigWhite) &&
          candReport.inputHash === expOrigHash &&
          candReport.branchCoverageSnapshots?.[0]?.runSource !==
            'standalone_subposition';
        if (!matchesOrigRoot) {
          return {
            ok: false,
            code: 'LP-P01',
            detail: '报告起点与原题初始局面不一致，且缺少可核验的 lproofJson / runContract 到达轨迹。',
          };
        }
        candStartMoves = [];
        candRunSource = 'original_root';
      }

      // Independently replay arrival trace and verify starting position parity
      const startReplay = replayPathFromOriginalRoot(candStartMoves, false);
      if (!startReplay.ok) {
        return {
          ok: false,
          code: startReplay.code,
          detail: `运行起点轨迹独立重放失败：${startReplay.detail}`,
        };
      }
      const startPos = startReplay.pos;
      if (
        candReport.firstToPlay !== startPos.toPlay ||
        !numberArraysEqual(candStartBlack, startPos.getBlackCoords()) ||
        !numberArraysEqual(candStartWhite, startPos.getWhiteCoords()) ||
        candReport.inputHash !== startPos.computeZobristHex()
      ) {
        return {
          ok: false,
          code: 'LP-S02',
          detail: '运行起点重放盘面与报告声明的起始棋面/先手/inputHash 不一致。',
        };
      }

      if (parsedLproof) {
        const lpSetup = parsedLproof.problemSetup as Record<string, unknown>;
        if (
          lpSetup.zobristHex !== startPos.computeZobristHex() ||
          lpSetup.koPoint !== startPos.koPoint ||
          lpSetup.consecutivePasses !== startPos.consecutivePasses ||
          lpSetup.survivingTokensMask !== startPos.survivingTargetTokensMask
        ) {
          return {
            ok: false,
            code: 'LP-S02',
            detail: '内嵌 lproofJson.problemSetup 的 zobristHex/koPoint/consecutivePasses/survivingTokensMask 与重放起点不一致。',
          };
        }
      }

      return {
        ok: true,
        derivedRunSource: candRunSource,
        runStartMoves: candStartMoves,
        runStartPos: startPos,
        hasEmbeddedLproof: parsedLproof !== null,
      };
    };

    const mainContract = validateRunReportContract(report);
    if (!mainContract.ok) {
      return makeSourceFail(
        'VERIFICATION_FAILED',
        mainContract.code,
        mainContract.detail
      );
    }

    derivedRunSource = mainContract.derivedRunSource;
    runStartMoves = mainContract.runStartMoves;
    runStartPathSgf = runStartMoves.map((mv) =>
      coordToSgf(mv, problem.boardSize)
    );
    const runStartPos = mainContract.runStartPos;

    // 4. R13 §1: Verify authentic originalRootOutcome (NEVER copy unverified rootStatus or cross-contract reports!)
    const resolveVerifiedOriginalRoot = (
      candReport: SolveReport,
      preValidated?: Extract<ValidatedReportContract, { ok: true }>
    ): {
      outcome: ProofOutcome | null;
      nodes: number | null;
      note?: string;
    } => {
      const contractRes = preValidated ?? validateRunReportContract(candReport);
      if (!contractRes.ok) {
        return {
          outcome: null,
          nodes: null,
          note: `原根报告未通过契约绑定 (${contractRes.code})：${contractRes.detail}`,
        };
      }
      if (contractRes.derivedRunSource !== 'original_root') {
        return {
          outcome: null,
          nodes: null,
          note: '原根报告来自独立子局面 (traced_subposition)，不能代表原题根部结论 (LP-P02)。',
        };
      }
      if (candReport.rootStatus === ProofOutcome.Unknown) {
        return {
          outcome: ProofOutcome.Unknown,
          nodes: candReport.numNodes,
        };
      }

      // Claimed PROVEN_WIN / PROVEN_LOSS MUST pass independent original_root proof verification
      if (contractRes.hasEmbeddedLproof) {
        const fileVr = this.verifySerializedLProofJson(candReport.lproofJson, {
          problem,
          context,
          scope: 'original_root',
        });
        if (!fileVr.passed) {
          return {
            outcome: null,
            nodes: candReport.numNodes,
            note: `原根声称 ${candReport.rootStatus}，但 lproof/1 证书未通过 original_root 独立校验 (${fileVr.errorCode})：${fileVr.message}`,
          };
        }
      }
      const memIsCompact =
        !Array.isArray(candReport.stateTable) ||
        candReport.stateTable.length === 0;
      const memVr = this.verifyProofDag(origPos, context, candReport, {
        skipChecksumRecompute: true,
        isCompactDag: memIsCompact,
        encodingMode: memIsCompact ? 'compact_dag' : 'full_state_table',
        verifiedScope: 'original_root',
        verifiedRootKind: 'initial',
      });
      if (!memVr.passed) {
        return {
          outcome: null,
          nodes: candReport.numNodes,
          note: `原根声称 ${candReport.rootStatus}，但内存证明 DAG 未通过 original_root 独立校验 (${memVr.errorCode})：${memVr.message}`,
        };
      }
      return {
        outcome: candReport.rootStatus,
        nodes: candReport.numNodes,
      };
    };

    if (derivedRunSource === 'original_root') {
      const origRes = resolveVerifiedOriginalRoot(report, mainContract);
      originalRootOutcome = origRes.outcome;
      originalRootNodes = origRes.nodes;
      originalRootBindingNote = origRes.note;
    } else if (params.originalRootReport) {
      const origRes = resolveVerifiedOriginalRoot(params.originalRootReport);
      originalRootOutcome = origRes.outcome;
      originalRootNodes = origRes.nodes;
      originalRootBindingNote = origRes.note;
    } else {
      originalRootOutcome = null;
      originalRootNodes = null;
    }

    // Reject contradictory caller-supplied runSource (R12 §4)
    if (
      params.runSource !== undefined &&
      params.runSource !== derivedRunSource
    ) {
      return makeSourceFail(
        'VERIFICATION_FAILED',
        'LP-P02',
        `调用方声明的 runSource="${params.runSource}" 与产物实际运行来源 "${derivedRunSource}" 矛盾。`
      );
    }

    // Verify targetPathMoves belongs to this run's starting trajectory (R12 §4)
    if (derivedRunSource === 'standalone_subposition') {
      const prefixOk =
        targetPathMoves.length >= runStartMoves.length &&
        runStartMoves.every((mv, idx) => targetPathMoves[idx] === mv);
      if (!prefixOk) {
        return makeSourceFail(
          'VERIFICATION_FAILED',
          'LP-P02',
          `目标路径 [${targetPathSgf.join('/') || 'root'}] 不以当前独立子局面运行起点 [${runStartPathSgf.join('/')}] 为前缀。`
        );
      }
    }

    // 5. R12 §3: Distinguish unclosed sentinel (-1) from corrupted out-of-bounds positive/invalid DAG node IDs
    if (targetDagNodeId === -1) {
      return makeSourceFail(
        'UNCLOSED',
        'LP-U01',
        '该路径在当前运行产物中未形成已闭合的 DAG 片段（sentinel=-1）。',
        null,
        ProofOutcome.Unknown
      );
    }
    if (
      !Number.isInteger(targetDagNodeId) ||
      targetDagNodeId < -1 ||
      targetDagNodeId >= report.proofDagNodes.length
    ) {
      return makeSourceFail(
        'VERIFICATION_FAILED',
        'LP-N01',
        `目标节点索引 #${targetDagNodeId} 越界或非法（当前 DAG 节点总数 ${report.proofDagNodes.length}）。`,
        targetDagNodeId,
        ProofOutcome.Unknown
      );
    }

    const targetNode = report.proofDagNodes[targetDagNodeId];
    if (!targetNode || targetNode.nodeId !== targetDagNodeId) {
      return makeSourceFail(
        'VERIFICATION_FAILED',
        'LP-N01',
        `目标节点 #${targetDagNodeId} 缺失或 nodeId 字段不一致。`,
        targetDagNodeId,
        ProofOutcome.Unknown
      );
    }
    if (targetNode.outcome === ProofOutcome.Unknown) {
      return makeSourceFail(
        'UNCLOSED',
        'LP-U01',
        `节点 #${targetDagNodeId} 尚未闭合为胜/负证明片段。`,
        targetDagNodeId,
        ProofOutcome.Unknown
      );
    }

    const targetReplay = replayPathFromOriginalRoot(targetPathMoves, true);
    if (!targetReplay.ok) {
      return makeSourceFail(
        'VERIFICATION_FAILED',
        targetReplay.code,
        `源路径独立重放失败：${targetReplay.detail}`,
        targetDagNodeId,
        targetNode.outcome
      );
    }
    const targetPos = targetReplay.pos;

    // 6. R12 §3 & R13 §2: Entry-point-invariant full-table verification
    //    (full ancestor chain from fragment entry back to stateId=0 + full source subgraph traversal on RZ/TT refs)
    if (hasFullTables) {
      if (!Array.isArray(report.historyTable) || report.historyTable.length === 0) {
        return makeSourceFail(
          'VERIFICATION_FAILED',
          'LP-S02',
          'full_state_table 模式下缺失有效 historyTable。',
          targetDagNodeId,
          targetNode.outcome
        );
      }
      // Verify stateTable[0] matches runStartPos
      const rootSt = report.stateTable[0];
      if (
        !rootSt ||
        rootSt.stateId !== 0 ||
        rootSt.parentStateId !== -1 ||
        !Number.isInteger(rootSt.historyId) ||
        rootSt.historyId < 0 ||
        rootSt.historyId >= report.historyTable.length ||
        rootSt.toPlay !== runStartPos.toPlay ||
        rootSt.koPoint !== runStartPos.koPoint ||
        rootSt.consecutivePasses !== runStartPos.consecutivePasses ||
        rootSt.survivingTokensMask !== runStartPos.survivingTargetTokensMask ||
        rootSt.zobristHex !== runStartPos.computeZobristHex() ||
        !numberArraysEqual(rootSt.blackCoords, runStartPos.getBlackCoords()) ||
        !numberArraysEqual(rootSt.whiteCoords, runStartPos.getWhiteCoords()) ||
        !historyTablesMatch(
          report.historyTable[rootSt.historyId],
          runStartPos.historySnapshots
        )
      ) {
        return makeSourceFail(
          'VERIFICATION_FAILED',
          'LP-S02',
          'stateTable[0] 或其历史快照与运行起点真实重放局面不一致。',
          targetDagNodeId,
          targetNode.outcome
        );
      }
    }

    const independentTerminal = new BensonTerminalEvaluator();
    const verifiedSourceSubgraphIds = new Set<number>();
    const inProgressSourceIds = new Set<number>();
    const targetRelativeMoves = targetPathMoves.slice(runStartMoves.length);

    const reconstructPosFromStateTable = (
      stateId: number
    ):
      | { ok: true; pos: GoPosition; chainMoves: number[] }
      | { ok: false; code: string; detail: string } => {
      const chain: number[] = [];
      const visited = new Set<number>();
      let cur = stateId;
      while (cur >= 0) {
        if (
          !Number.isInteger(cur) ||
          cur < 0 ||
          cur >= report.stateTable.length ||
          visited.has(cur)
        ) {
          return {
            ok: false,
            code: 'LP-S10',
            detail: `状态表祖先链在 stateId=${cur} 处越界或存在环`,
          };
        }
        visited.add(cur);
        const row = report.stateTable[cur];
        if (!row || row.stateId !== cur) {
          return {
            ok: false,
            code: 'LP-S10',
            detail: `stateTable[${cur}] 缺失或 stateId 不一致`,
          };
        }
        chain.push(cur);
        if (cur === 0) break;
        cur = row.parentStateId;
      }
      if (
        chain.length === 0 ||
        chain[chain.length - 1] !== 0 ||
        report.stateTable[0]?.parentStateId !== -1
      ) {
        return {
          ok: false,
          code: 'LP-S10',
          detail: `stateId=${stateId} 的祖先链未回溯到根状态 stateId=0`,
        };
      }
      const p = runStartPos.clone();
      const chainMoves: number[] = [];
      for (let i = chain.length - 2; i >= 0; i--) {
        const row = report.stateTable[chain[i]];
        chainMoves.push(row.moveFromParent);
        const res = p.playMove(row.moveFromParent);
        if (!res.legal) {
          return {
            ok: false,
            code: 'LP-S09',
            detail: `状态表 stateId=${row.stateId} 的 moveFromParent=${row.moveFromParent} 非法`,
          };
        }
        if (
          !Number.isInteger(row.historyId) ||
          row.historyId < 0 ||
          row.historyId >= report.historyTable.length
        ) {
          return {
            ok: false,
            code: 'LP-S10',
            detail: `祖先状态 stateTable[${row.stateId}] 的 historyId=${row.historyId} 越界`,
          };
        }
        if (
          row.toPlay !== p.toPlay ||
          row.koPoint !== p.koPoint ||
          row.consecutivePasses !== p.consecutivePasses ||
          row.survivingTokensMask !== p.survivingTargetTokensMask ||
          row.zobristHex !== p.computeZobristHex() ||
          !numberArraysEqual(row.blackCoords, p.getBlackCoords()) ||
          !numberArraysEqual(row.whiteCoords, p.getWhiteCoords())
        ) {
          return {
            ok: false,
            code: 'LP-N10',
            detail: `祖先状态 stateTable[${row.stateId}] 盘面/劫点/Zobrist 与真实重放局面不一致`,
          };
        }
        if (
          !historyTablesMatch(
            report.historyTable[row.historyId],
            p.historySnapshots
          )
        ) {
          return {
            ok: false,
            code: 'LP-S02',
            detail: `祖先状态 stateTable[${row.stateId}] 的 historyTable[${row.historyId}] 与重放超劫历史不一致`,
          };
        }
      }
      return { ok: true, pos: p, chainMoves };
    };

    const verifyNodeFullTableBinding = (
      node: ProofDagNode,
      expectedPos: GoPosition,
      parentNode: ProofDagNode | null,
      incomingMoveFromParent: number | null,
      expectedEntryRelativeMoves: number[] | null
    ): { ok: boolean; code: string; detail: string } => {
      if (
        !Number.isInteger(node.stateId) ||
        node.stateId < 0 ||
        node.stateId >= report.stateTable.length
      ) {
        return {
          ok: false,
          code: 'LP-S10',
          detail: `节点 #${node.nodeId} 的 stateId=${node.stateId} 超出 stateTable 范围 (len=${report.stateTable.length})`,
        };
      }
      if (
        !Number.isInteger(node.historyId) ||
        node.historyId < 0 ||
        node.historyId >= report.historyTable.length
      ) {
        return {
          ok: false,
          code: 'LP-S10',
          detail: `节点 #${node.nodeId} 的 historyId=${node.historyId} 超出 historyTable 范围 (len=${report.historyTable.length})`,
        };
      }
      const st = report.stateTable[node.stateId];
      if (
        !st ||
        st.stateId !== node.stateId ||
        st.historyId !== node.historyId ||
        st.parentStateId !== node.parentStateId
      ) {
        return {
          ok: false,
          code: 'LP-S10',
          detail: `节点 #${node.nodeId} 与 stateTable[${node.stateId}] 的 stateId/historyId/parentStateId 关联不一致`,
        };
      }
      if (parentNode !== null) {
        if (
          node.parentStateId !== parentNode.stateId ||
          st.parentStateId !== parentNode.stateId
        ) {
          return {
            ok: false,
            code: 'LP-S10',
            detail: `子节点 #${node.nodeId} 的 parentStateId=${node.parentStateId} 与父节点 #${parentNode.nodeId} 的 stateId=${parentNode.stateId} 不一致`,
          };
        }
        if (
          incomingMoveFromParent !== null &&
          (st.moveFromParent !== incomingMoveFromParent ||
            node.incomingMove !== incomingMoveFromParent)
        ) {
          return {
            ok: false,
            code: 'LP-N10',
            detail: `子节点 #${node.nodeId} 的入边落子与父边着法 ${incomingMoveFromParent} 不一致`,
          };
        }
      } else {
        // R13 §2 Case B: Entry node of fragment (or source subgraph) MUST verify its full ancestor chain back to stateId=0
        const entryRecon = reconstructPosFromStateTable(node.stateId);
        if (!entryRecon.ok) {
          return entryRecon;
        }
        if (expectedEntryRelativeMoves !== null) {
          const relativeLen = expectedEntryRelativeMoves.length;
          if (relativeLen === 0) {
            if (node.stateId !== 0 || node.parentStateId !== -1) {
              return {
                ok: false,
                code: 'LP-S10',
                detail: `运行根节点 #${node.nodeId} 的 stateId=${node.stateId} / parentStateId=${node.parentStateId} 必须为 0 / -1`,
              };
            }
          } else {
            const expectedIncoming =
              expectedEntryRelativeMoves[relativeLen - 1];
            if (
              st.moveFromParent !== expectedIncoming ||
              node.incomingMove !== expectedIncoming
            ) {
              return {
                ok: false,
                code: 'LP-N10',
                detail: `片段节点 #${node.nodeId} 的入边着法与目标路径末手不一致`,
              };
            }
            if (
              !numberArraysEqual(
                entryRecon.chainMoves,
                expectedEntryRelativeMoves
              )
            ) {
              return {
                ok: false,
                code: 'LP-S10',
                detail: `片段节点 #${node.nodeId} 的状态表祖先链轨迹与目标相对路径不一致`,
              };
            }
          }
        } else {
          // Source subgraph root: ensure incomingMove agrees with stateTable chain
          if (node.stateId === 0) {
            if (node.parentStateId !== -1) {
              return {
                ok: false,
                code: 'LP-S10',
                detail: `源证明根节点 #${node.nodeId} (stateId=0) 的 parentStateId=${node.parentStateId} 非法`,
              };
            }
          } else if (node.incomingMove !== st.moveFromParent) {
            return {
              ok: false,
              code: 'LP-N10',
              detail: `源证明节点 #${node.nodeId} 的 incomingMove=${node.incomingMove} 与 stateTable[${node.stateId}].moveFromParent=${st.moveFromParent} 不一致`,
            };
          }
        }
      }

      if (
        st.toPlay !== expectedPos.toPlay ||
        st.koPoint !== expectedPos.koPoint ||
        st.consecutivePasses !== expectedPos.consecutivePasses ||
        st.survivingTokensMask !== expectedPos.survivingTargetTokensMask ||
        st.zobristHex !== expectedPos.computeZobristHex() ||
        !numberArraysEqual(st.blackCoords, expectedPos.getBlackCoords()) ||
        !numberArraysEqual(st.whiteCoords, expectedPos.getWhiteCoords())
      ) {
        return {
          ok: false,
          code: 'LP-N10',
          detail: `节点 #${node.nodeId} 的 stateTable[${node.stateId}] 盘面/劫点/Zobrist 与真实重放局面不匹配`,
        };
      }

      const recHist = report.historyTable[node.historyId];
      const expHist = expectedPos.historySnapshots;
      if (!recHist || !historyTablesMatch(recHist, expHist)) {
        return {
          ok: false,
          code: 'LP-S02',
          detail: `节点 #${node.nodeId} 的历史快照序列（len=${recHist?.length ?? 0}）与真实重放历史（len=${expHist.length}）不一致`,
        };
      }

      if (node.isPrunedOutsideRz) {
        const pc = node.prunedCertificate;
        if (
          !pc ||
          node.sourceProofNodeId === null ||
          node.sourceProofNodeId < 0 ||
          node.sourceProofNodeId >= node.nodeId ||
          pc.sourceProofNodeId !== node.sourceProofNodeId
        ) {
          return {
            ok: false,
            code: 'LP-R02',
            detail: `RZ 剪枝节点 #${node.nodeId} 缺失合法 prunedCertificate 或 sourceProofNodeId`,
          };
        }
        const srcNode = report.proofDagNodes[node.sourceProofNodeId];
        if (
          !srcNode ||
          pc.queryStateId !== node.stateId ||
          pc.queryHistoryId !== node.historyId ||
          pc.sourceStateId !== srcNode.stateId ||
          pc.sourceHistoryId !== srcNode.historyId
        ) {
          return {
            ok: false,
            code: 'LP-S10',
            detail: `RZ 剪枝节点 #${node.nodeId} 的 prunedCertificate 状态/历史引用与节点或源证明不一致`,
          };
        }
        const srcCheck = verifySourceNodeTableIntegrity(node.sourceProofNodeId);
        if (!srcCheck.ok) return srcCheck;
      } else if (node.isTtHit) {
        if (
          node.sourceProofNodeId === null ||
          node.sourceProofNodeId < 0 ||
          node.sourceProofNodeId >= node.nodeId
        ) {
          return {
            ok: false,
            code: 'LP-R02',
            detail: `TT 复用节点 #${node.nodeId} 缺失有效 sourceProofNodeId`,
          };
        }
        const srcCheck = verifySourceNodeTableIntegrity(node.sourceProofNodeId);
        if (!srcCheck.ok) return srcCheck;
      } else if (node.childNodeIds.length > 0) {
        // Also ensure every listed childNodeId on an internal node has valid in-bounds table pointers
        for (let k = 0; k < node.childNodeIds.length; k++) {
          const cid = node.childNodeIds[k];
          if (
            !Number.isInteger(cid) ||
            cid < 0 ||
            cid >= report.proofDagNodes.length
          ) {
            return {
              ok: false,
              code: 'LP-T02',
              detail: `节点 #${node.nodeId} 的子节点索引 #${cid} 越界`,
            };
          }
          const chNode = report.proofDagNodes[cid];
          if (
            !chNode ||
            !Number.isInteger(chNode.stateId) ||
            chNode.stateId < 0 ||
            chNode.stateId >= report.stateTable.length ||
            !Number.isInteger(chNode.historyId) ||
            chNode.historyId < 0 ||
            chNode.historyId >= report.historyTable.length ||
            chNode.parentStateId !== node.stateId
          ) {
            return {
              ok: false,
              code: 'LP-S10',
              detail: `节点 #${node.nodeId} 的子节点 #${cid} 存在越界或不一致的 stateId/historyId/parentStateId`,
            };
          }
        }
      }

      return { ok: true, code: 'PASS', detail: '' };
    };

    // R13 §2 Case A: Entry-point-invariant full source-subgraph verification (ordinary descendants + nested TT/RZ refs)
    const verifySourceNodeTableIntegrity = (
      srcDagId: number
    ): { ok: boolean; code: string; detail: string } => {
      if (verifiedSourceSubgraphIds.has(srcDagId)) {
        return { ok: true, code: 'PASS', detail: '' };
      }
      if (inProgressSourceIds.has(srcDagId)) {
        return {
          ok: false,
          code: 'LP-T02',
          detail: `源证明节点 #${srcDagId} 存在循环引用`,
        };
      }
      if (
        !Number.isInteger(srcDagId) ||
        srcDagId < 0 ||
        srcDagId >= report.proofDagNodes.length
      ) {
        return {
          ok: false,
          code: 'LP-R02',
          detail: `源证明节点索引 #${srcDagId} 越界`,
        };
      }
      const srcNode = report.proofDagNodes[srcDagId];
      if (!srcNode || srcNode.nodeId !== srcDagId) {
        return {
          ok: false,
          code: 'LP-R02',
          detail: `源证明节点 #${srcDagId} 缺失或 nodeId 不一致`,
        };
      }
      const recon = reconstructPosFromStateTable(srcNode.stateId);
      if (!recon.ok) return recon;

      inProgressSourceIds.add(srcDagId);
      let srcFirstError = 'PASS';
      const srcRecordFailure = (code: string) => {
        if (srcFirstError === 'PASS') {
          srcFirstError = code;
        }
      };
      const scratchStats = {
        verifiedStates: 0,
        verifiedLeaves: 0,
        verifiedUniversals: 0,
        replayedPruned: 0,
        replayedTt: 0,
      };
      const subRes = this.verifyCompactDagRecursive(
        recon.pos,
        effectiveRegionMask,
        allowedRegionSet,
        context,
        report,
        srcDagId,
        independentTerminal,
        0,
        scratchStats,
        srcRecordFailure,
        (subNode, subPos, subParent, subIncoming) =>
          verifyNodeFullTableBinding(
            subNode,
            subPos,
            subParent,
            subIncoming,
            null
          ),
        null,
        null
      );
      inProgressSourceIds.delete(srcDagId);

      if (!subRes.ok) {
        return {
          ok: false,
          code: srcFirstError === 'PASS' ? 'LP-S01' : srcFirstError,
          detail: subRes.detail || `源证明子图 #${srcDagId} 完整状态表校验失败`,
        };
      }
      verifiedSourceSubgraphIds.add(srcDagId);
      return { ok: true, code: 'PASS', detail: '' };
    };

    let firstErrorCode = 'PASS';
    let failedNodeId: number | null = null;
    const recordFailure = (code: string, nid: number | null = null) => {
      if (firstErrorCode === 'PASS') {
        firstErrorCode = code;
        failedNodeId = nid;
      }
    };
    const stats = {
      verifiedStates: 0,
      verifiedLeaves: 0,
      verifiedUniversals: 0,
      replayedPruned: 0,
      replayedTt: 0,
    };

    const recursiveRes = this.verifyCompactDagRecursive(
      targetPos,
      effectiveRegionMask,
      allowedRegionSet,
      context,
      report,
      targetDagNodeId,
      independentTerminal,
      0,
      stats,
      recordFailure,
      hasFullTables
        ? (node, pos, parentNode, incomingMove) =>
            verifyNodeFullTableBinding(
              node,
              pos,
              parentNode,
              incomingMove,
              parentNode === null ? targetRelativeMoves : null
            )
        : undefined,
      null,
      null
    );

    const sourceReceipt: SubproofSourceReceipt = recursiveRes.ok
      ? {
          status: 'SOURCE_VERIFIED',
          passed: true,
          errorCode: 'PASS',
          message: `片段 #${targetDagNodeId} (${targetNode.outcome}, mode=${verificationMode}) 在路径 [${
            targetPathSgf.join(' -> ') || 'root'
          }] 下通过独立闭环校验（核验 ${stats.verifiedStates} 节点 / ${
            stats.verifiedLeaves
          } 终局叶 / ${stats.verifiedUniversals} 全覆盖节点 / ${
            stats.replayedPruned
          } RZ重放 / ${stats.replayedTt} TT重放）。`,
          scope: 'subproof_fragment',
          verificationMode,
          targetPathSgf,
          targetDagNodeId,
          outcome: targetNode.outcome,
          verifiedNodes: stats.verifiedStates,
          verifiedLeaves: stats.verifiedLeaves,
          verifiedUniversals: stats.verifiedUniversals,
          replayedPruned: stats.replayedPruned,
          replayedTt: stats.replayedTt,
          failedNodeId: null,
        }
      : {
          status: 'VERIFICATION_FAILED',
          passed: false,
          errorCode: firstErrorCode === 'PASS' ? 'LP-S01' : firstErrorCode,
          message: recursiveRes.detail || `片段 #${targetDagNodeId} 独立闭环校验失败`,
          scope: 'subproof_fragment',
          verificationMode,
          targetPathSgf,
          targetDagNodeId,
          outcome: targetNode.outcome,
          verifiedNodes: stats.verifiedStates,
          verifiedLeaves: stats.verifiedLeaves,
          verifiedUniversals: stats.verifiedUniversals,
          replayedPruned: stats.replayedPruned,
          replayedTt: stats.replayedTt,
          failedNodeId,
        };

    let queryReplayReceipt: SubproofQueryReplayReceipt = notRequestedQuery;
    if (queryPathMoves) {
      if (!sourceReceipt.passed) {
        queryReplayReceipt = {
          status: 'QUERY_REPLAY_FAILED',
          passed: false,
          errorCode: sourceReceipt.errorCode,
          message: `源片段 #${targetDagNodeId} 未通过校验，无法在查询局面重放。`,
          sourceDagNodeId: targetDagNodeId,
          queryPathSgf,
          queryHistoryLength: 0,
        };
      } else {
        const qReplay = replayPathFromOriginalRoot(queryPathMoves, true);
        if (!qReplay.ok) {
          queryReplayReceipt = {
            status: 'QUERY_REPLAY_FAILED',
            passed: false,
            errorCode: qReplay.code,
            message: `查询路径独立重放失败：${qReplay.detail}`,
            sourceDagNodeId: targetDagNodeId,
            queryPathSgf,
            queryHistoryLength: 0,
          };
        } else {
          const queryPos = qReplay.pos;
          const replayOk = this.replaySourceSubgraphOnQueryState(
            queryPos,
            effectiveRegionMask,
            context,
            report.proofDagNodes,
            targetDagNodeId,
            targetNode.outcome,
            independentTerminal,
            0
          );
          queryReplayReceipt = replayOk
            ? {
                status: 'QUERY_REPLAY_VERIFIED',
                passed: true,
                errorCode: 'PASS',
                message: `源片段 #${targetDagNodeId} (${targetNode.outcome}) 在查询路径 [${
                  queryPathSgf.join(' -> ') || 'root'
                }]（历史长度 ${queryPos.historySnapshots.length}）下语义重放通过。`,
                sourceDagNodeId: targetDagNodeId,
                queryPathSgf,
                queryHistoryLength: queryPos.historySnapshots.length,
              }
            : {
                status: 'QUERY_REPLAY_FAILED',
                passed: false,
                errorCode: 'LP-R03',
                message: `源片段 #${targetDagNodeId} 在查询路径 [${
                  queryPathSgf.join(' -> ') || 'root'
                }]（历史长度 ${queryPos.historySnapshots.length}）下语义重放失败（盘面或超劫历史不兼容）。`,
                sourceDagNodeId: targetDagNodeId,
                queryPathSgf,
                queryHistoryLength: queryPos.historySnapshots.length,
              };
        }
      }
    }

    return {
      runSource: derivedRunSource,
      runStartPathSgf,
      runRootOutcome: report.rootStatus,
      originalRootOutcome,
      originalRootNodes,
      ...(originalRootBindingNote !== undefined
        ? { originalRootBindingNote }
        : {}),
      sourceReceipt,
      queryReplayReceipt,
    };
  }
}
