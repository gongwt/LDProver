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
  PN_DN_SATURATION,
  ProofContext,
  ProofDagNode,
  ProofOutcome,
  SolveReport,
  StateTableEntry,
  TerminalStatus,
  VerificationReport,
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
    const regionCoords = (report.regionCoords ?? []).slice();

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

    const payloadWithoutChecksum = {
      magic: 'lproof/1',
      problemId: report.problemId,
      context: {
        contextId: context.contextId,
        rootAttacker: context.rootAttacker === Color.Black ? 'B' : 'W',
        attackerGoal: context.attackerGoal,
        crucialStoneOp: context.crucialStoneOp,
        koRule: context.koRule,
        attackerAllowKo: context.attackerAllowKo,
        defenderAllowKo: context.defenderAllowKo,
        initialTokens: context.initialTokens,
      },
      problemSetup: {
        boardSize: initialPos.boardSize,
        firstToPlay: initialPos.toPlay === Color.Black ? 'B' : 'W',
        zobristHex: initialPos.computeZobristHex(),
        inputHash: report.inputHash,
        blackInitialCoords: initialPos.getBlackCoords(),
        whiteInitialCoords: initialPos.getWhiteCoords(),
        immortalWallCoords,
        regionCoords,
        rawRegionPointCount: report.rawRegionPointCount ?? regionCoords.length,
        isFullRegionSearch: report.isFullRegionSearch ?? true,
      },
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
        toPlay: n.toPlay,
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
   * initial board, context, states, histories, and DAG solely from a serialized `.lproof.json`
   * file string without requiring any in-memory solver objects.
   */
  public verifySerializedLProofJson(lproofJsonText: string): VerificationReport {
    let parsed: Record<string, unknown>;
    try {
      parsed = JSON.parse(lproofJsonText) as Record<string, unknown>;
    } catch (err) {
      return {
        passed: false,
        schemaVersion: 'lproof/1',
        jcsSha256Checksum: '',
        verifiedNodes: 0,
        verifiedStates: 0,
        verifiedHistories: 0,
        replayedPrunedCertificates: 0,
        replayedTtHits: 0,
        failedNodeId: null,
        errorCode: 'LP-J01',
        message: `JSON 解析失败: ${err instanceof Error ? err.message : String(err)}`,
        auditChecks: [
          {
            checkId: 'CHK-01',
            requirementRef: 'FR-8.3 / FR-9.1',
            title: 'lproof/1 独立文件 JSON 语法与魔数检查',
            passed: false,
            detail: 'Malformed JSON payload.',
          },
        ],
      };
    }

    const hasPooledHistory =
      Array.isArray(parsed.snapshotPool) &&
      Array.isArray(parsed.historySnapshotIds);
    const hasInlineHistory = Array.isArray(parsed.historyTable);

    if (
      !parsed ||
      parsed.magic !== 'lproof/1' ||
      typeof parsed.checksum !== 'string' ||
      !parsed.context ||
      !parsed.problemSetup ||
      !Array.isArray(parsed.stateTable) ||
      (!hasPooledHistory && !hasInlineHistory) ||
      !Array.isArray(parsed.nodes)
    ) {
      return {
        passed: false,
        schemaVersion: String(parsed?.magic ?? 'unknown'),
        jcsSha256Checksum: String(parsed?.checksum ?? ''),
        verifiedNodes: 0,
        verifiedStates: 0,
        verifiedHistories: 0,
        replayedPrunedCertificates: 0,
        replayedTtHits: 0,
        failedNodeId: null,
        errorCode: 'LP-J02',
        message: 'lproof/1 独立文件缺少必要字段（context / problemSetup / stateTable / historyTable / nodes）。',
        auditChecks: [
          {
            checkId: 'CHK-01',
            requirementRef: 'FR-8.3 / FR-9.1',
            title: 'lproof/1 独立文件结构完整性',
            passed: false,
            detail: 'Missing required top-level fields.',
          },
        ],
      };
    }

    const { checksum: fileChecksum, ...withoutChecksum } = parsed;
    const expectedChecksum = `sha256-jcs:${sha256Hex(
      canonicalizeJsonJcs(withoutChecksum)
    )}`;
    if (fileChecksum !== expectedChecksum) {
      return {
        passed: false,
        schemaVersion: 'lproof/1',
        jcsSha256Checksum: fileChecksum,
        verifiedNodes: 0,
        verifiedStates: 0,
        verifiedHistories: 0,
        replayedPrunedCertificates: 0,
        replayedTtHits: 0,
        failedNodeId: null,
        errorCode: 'LP-C01',
        message: '独立文件 RFC 8785 JCS SHA-256 校验和不匹配，证书已被篡改。',
        auditChecks: [
          {
            checkId: 'CHK-01',
            requirementRef: 'FR-8.3 / FR-9.1',
            title: 'RFC 8785 JCS SHA-256 Checksum 完整性校验',
            passed: false,
            detail: `Expected=${expectedChecksum.slice(0, 28)}... Got=${fileChecksum.slice(0, 28)}...`,
          },
        ],
      };
    }

    const rawCtx = parsed.context as Record<string, unknown>;
    const setup = parsed.problemSetup as Record<string, unknown>;
    const context: ProofContext = {
      contextId: String(rawCtx.contextId ?? ''),
      rootAttacker: rawCtx.rootAttacker === 'W' ? Color.White : Color.Black,
      attackerGoal: rawCtx.attackerGoal as ProofContext['attackerGoal'],
      crucialStoneOp: rawCtx.crucialStoneOp as ProofContext['crucialStoneOp'],
      koRule: (rawCtx.koRule as KoRule) ?? KoRule.SituationalSuperko,
      attackerAllowKo: Boolean(rawCtx.attackerAllowKo),
      defenderAllowKo: Boolean(rawCtx.defenderAllowKo),
      initialTokens: Array.isArray(rawCtx.initialTokens)
        ? (rawCtx.initialTokens as ProofContext['initialTokens'])
        : [],
    };

    const boardSize =
      typeof setup.boardSize === 'number' ? setup.boardSize : 19;
    const firstToPlay = setup.firstToPlay === 'W' ? Color.White : Color.Black;
    const blackInitialCoords = Array.isArray(setup.blackInitialCoords)
      ? (setup.blackInitialCoords as number[])
      : [];
    const whiteInitialCoords = Array.isArray(setup.whiteInitialCoords)
      ? (setup.whiteInitialCoords as number[])
      : [];
    const immortalWallCoords = Array.isArray(setup.immortalWallCoords)
      ? (setup.immortalWallCoords as number[])
      : [];
    const regionCoords = Array.isArray(setup.regionCoords)
      ? (setup.regionCoords as number[])
      : [];

    const initialPos = new GoPosition(context, boardSize, immortalWallCoords);
    initialPos.setupInitialStones(
      blackInitialCoords,
      whiteInitialCoords,
      firstToPlay
    );

    const nodes: ProofDagNode[] = (
      parsed.nodes as Array<Record<string, unknown>>
    ).map((n) => ({
      nodeId: Number(n.nodeId),
      stateId: Number(n.stateId),
      historyId: Number(n.historyId),
      parentStateId: Number(n.parentStateId),
      isOrNode: Boolean(n.isOrNode),
      toPlay: Number(n.toPlay) as Color,
      incomingMove: Number(n.incomingMove),
      incomingMoveSgf: String(n.incomingMoveSgf ?? ''),
      pn: decodeSatNumber(n.pn),
      dn: decodeSatNumber(n.dn),
      outcome: n.outcome as ProofOutcome,
      terminalEvidence: String(n.terminalEvidence ?? ''),
      isPrunedOutsideRz: Boolean(n.isPrunedOutsideRz),
      isTtHit: Boolean(n.isTtHit),
      isKoDependentBarrier: Boolean(n.isKoDependentBarrier),
      sourceProofNodeId:
        typeof n.sourceProofNodeId === 'number' ? n.sourceProofNodeId : null,
      proofRzCoords: Array.isArray(n.proofRzCoords)
        ? (n.proofRzCoords as number[])
        : [],
      disproofRzCoords: Array.isArray(n.disproofRzCoords)
        ? (n.disproofRzCoords as number[])
        : [],
      childNodeIds: Array.isArray(n.childNodeIds)
        ? (n.childNodeIds as number[])
        : [],
      childMoves: Array.isArray(n.childMoves) ? (n.childMoves as number[]) : [],
      prunedCertificate: n.prunedCertificate
        ? (n.prunedCertificate as ProofDagNode['prunedCertificate'])
        : undefined,
    }));

    let reconstructedHistoryTable: CanonicalSnapshot[][];
    if (hasPooledHistory) {
      const pool = parsed.snapshotPool as CanonicalSnapshot[];
      const idRows = parsed.historySnapshotIds as number[][];
      reconstructedHistoryTable = idRows.map((row) =>
        Array.isArray(row) ? row.map((idx) => pool[idx]) : []
      );
    } else {
      reconstructedHistoryTable = parsed.historyTable as CanonicalSnapshot[][];
    }

    const reconstructedReport: SolveReport = {
      problemId: String(parsed.problemId ?? ''),
      problemTitle: String(parsed.problemId ?? ''),
      boardSize,
      firstToPlay,
      blackInitialCoords,
      whiteInitialCoords,
      immortalWallCoords,
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
      stateTable: parsed.stateTable as StateTableEntry[],
      historyTable: reconstructedHistoryTable,
      rootDagNodeId: Number(parsed.rootNode),
      proofChecksum: fileChecksum,
      sgfContent: '',
      sgfChecksum: '',
      lproofJson: lproofJsonText,
      resultJson: '',
    };

    return this.verifyProofDag(initialPos, context, reconstructedReport);
  }

  /**
   * Independent recursive semantic proof replay on `queryPos` (with its authentic HistorySet)
   * for `OutsideRZRevalidated` and `TT` reuse nodes. Zero shared code with DfpnSolver!
   */
  private replaySourceSubgraphOnQueryState(
    queryPos: GoPosition,
    regionCoords: number[],
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

    // Existential replay: OR -> ProvenWin or AND -> ProvenLoss
    if (
      (isOr && expectedOutcome === ProofOutcome.ProvenWin) ||
      (!isOr && expectedOutcome === ProofOutcome.ProvenLoss)
    ) {
      for (let i = 0; i < sourceNode.childNodeIds.length; i++) {
        const cid = sourceNode.childNodeIds[i];
        if (cid < 0 || cid >= sourceNode.nodeId) continue;
        const chNode = dagNodes[cid];
        if (!chNode || chNode.outcome !== expectedOutcome) continue;
        const nextPos = queryPos.clone();
        const playRes = nextPos.playMove(sourceNode.childMoves[i]);
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

  // FR-9.1, FR-9.2, FR-9.3: Zero-trust Independent Proof Checker (`tprover check`)
  public verifyProofDag(
    initialPos: GoPosition,
    context: ProofContext,
    report: SolveReport
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

    // Check 1: RFC 8785 JCS SHA-256 Checksum, InputHash, & Root Proposition Binding (FR-8.3, FR-9.1)
    const recomputed = this.serializeLProofJson(initialPos, context, report);
    const checksumValid = recomputed.checksum === report.proofChecksum;
    const expectedInputHash = initialPos.computeZobristHex();
    const inputHashValid = report.inputHash === expectedInputHash;

    let rootBindingValid = true;
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
      } else if (rootNode.stateId !== 0) {
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
      }
    }

    const chk01Passed = checksumValid && inputHashValid && rootBindingValid;
    if (!chk01Passed) {
      recordFailure(!checksumValid || !inputHashValid ? 'LP-C01' : 'LP-R00');
    }

    auditChecks.push({
      checkId: 'CHK-01',
      requirementRef: 'FR-8.3 / FR-9.1',
      title: 'RFC 8785 JCS SHA-256 Checksum、InputHash 与根命题绑定校验',
      passed: chk01Passed,
      detail: chk01Passed
        ? `SHA-256=${recomputed.checksum.slice(0, 27)}... | InputHash=${report.inputHash} | Root=#${report.rootDagNodeId}`
        : `Checksum=${checksumValid}, InputHash=${inputHashValid} (${report.inputHash} vs ${expectedInputHash})${
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

    // Check 2: Zero-Trust StateTable & Canonical HistorySet Reconstruction from `initialPos` (FR-2.2, FR-9.2)
    let stateReplayOk = report.stateTable.length > 0;
    let stateReplayDetail = '';
    const rebuiltPositions: GoPosition[] = new Array(report.stateTable.length);

    if (!stateReplayOk) {
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
    }

    if (stateReplayOk) {
      stateReplayDetail = `从初始输入严格回放验证全部 ${rebuiltPositions.length} 个可达状态、不可复活令牌掩码与 SSK/PSK HistorySet`;
    }

    auditChecks.push({
      checkId: 'CHK-02',
      requirementRef: 'FR-2.2 / FR-2.6 / FR-9.2',
      title: 'StateTable 可达性重放、目标令牌掩码与 SSK/PSK 历史全量核验',
      passed: stateReplayOk,
      detail: stateReplayDetail,
    });

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

    // Check 3: Post-order topological acyclicity, LP-N15 (0, SAT)/(SAT, 0), & AND/OR role binding
    let lpN15AndRoleOk = indexingAndTopologyOk;
    if (indexingAndTopologyOk) {
      // Verify topological acyclicity & saturation on ALL nodes in DAG (and collect reachable closure)
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

      // Also check global node array saturation & post-order so fault-injected nodes are caught immediately
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

        if (stateReplayOk && reachableNodeIds.has(node.nodeId)) {
          const pos = rebuiltPositions[node.stateId];
          if (!pos) {
            lpN15AndRoleOk = false;
            topologyDetail = `节点 #${node.nodeId} 指向不存在的 stateId=${node.stateId}`;
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

    // Check 4: Independent Terminal Leaf Evaluation + Edge Legality + Full Legal-Move Coverage
    const effectiveRegionCoords = report.regionCoords ?? [];
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
              effectiveRegionCoords
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
      semanticsDetail = `独立验证 ${verifiedLeafCount} 个可达终局叶节点与 ${verifiedUniversalCount} 个全称节点的完整合法应手覆盖（region=${effectiveRegionCoords.length} 点）`;
    }

    auditChecks.push({
      checkId: 'CHK-04',
      requirementRef: 'FR-3.1..FR-3.8 / FR-4.2 / FR-9.2',
      title: '可达终局叶独立重算、走子合法性与全称节点完整应手覆盖核验',
      passed: semanticsOk,
      detail: semanticsDetail,
    });

    // Check 5: Independent Semantic Replay of ALL Reachable OutsideRZRevalidated & TT-Reuse Nodes
    let reuseReplayOk = stateReplayOk && lpN15AndRoleOk;
    let reuseReplayDetail = '';
    let replayedPrunedCount = 0;
    let replayedTtCount = 0;

    // Also reject any node in the array marked `isPrunedOutsideRz` whose certificate struct is missing/tampered
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
          effectiveRegionCoords,
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
      passed: allPassed,
      schemaVersion: 'lproof/1',
      jcsSha256Checksum: report.proofChecksum,
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
        ? `PASS — 独立 Proof Checker 完成状态可达重建、全称合法着覆盖与 RZ/TT 语义重放（覆盖 region=${effectiveRegionCoords.length} 点）`
        : `FAIL (${firstErrorCode}) — 独立证明校验拒绝无效或不完备证书`,
      auditChecks,
    };
  }
}
