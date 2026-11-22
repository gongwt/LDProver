// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generic Branch Coverage & Sub-Proof Fragment Audit Panel (lives inside Proof DAG tab).
// Works uniformly for all problems without problem-specific branches.

import React, { useEffect, useMemo, useState } from 'react';
import {
  CheckCircle2,
  GitBranch,
  Play,
  ShieldAlert,
  ShieldCheck,
  XCircle,
} from 'lucide-react';
import { DfpnSolver } from '../engine/dfpnSolver';
import {
  coordToHumanLabel,
  GoPosition,
  PASS_MOVE,
  sgfToCoord,
} from '../engine/position';
import { ProofArtifactManager } from '../engine/proofChecker';
import {
  BranchCoverageSnapshot,
  BranchMoveCoverageEntry,
  BranchMoveCoverageStatus,
  Color,
  PN_DN_SATURATION,
  ProofContext,
  ProofOutcome,
  SolveReport,
  SolverConfig,
  SubproofFragmentVerificationResult,
  TsumegoProblemSpec,
  VerificationReport,
} from '../engine/types';

interface BranchCoveragePanelProps {
  problem: TsumegoProblemSpec;
  context: ProofContext;
  rootInitialPosition: GoPosition;
  activeBaseMoves: number[];
  solverConfig: SolverConfig;
  solveReport: SolveReport;
}

interface StandaloneSubSolveReceipt {
  pathLabel: string;
  pathSgf: string[];
  report: SolveReport;
  tracedVerification: VerificationReport;
  originalRootVerification: VerificationReport;
}

type MoveStatusFilter =
  | 'all'
  | 'closed'
  | 'deferred'
  | 'unresolved'
  | 'unexpanded';

const STATUS_BADGE_MAP: Record<
  BranchMoveCoverageStatus,
  { label: string; className: string }
> = {
  PROVEN_SOURCE: {
    label: '源证明',
    className: 'bg-emerald-50 text-emerald-800 border-emerald-200',
  },
  TT_REPLAYED: {
    label: 'TT 重放',
    className: 'bg-sky-50 text-sky-800 border-sky-200',
  },
  RZ_REVALIDATED: {
    label: 'RZ 重验通过',
    className: 'bg-indigo-50 text-indigo-800 border-indigo-200',
  },
  DEFERRED_OUTSIDE_RZ: {
    label: 'RZ 外暂缓(未重验)',
    className: 'bg-amber-50 text-amber-800 border-amber-200',
  },
  EXPANDED_UNRESOLVED: {
    label: '已展开未决',
    className: 'bg-orange-50 text-orange-800 border-orange-200',
  },
  UNEXPANDED: {
    label: '未展开',
    className: 'bg-slate-100 text-slate-600 border-slate-200',
  },
  KO_BARRIER: {
    label: '劫依赖屏障',
    className: 'bg-rose-50 text-rose-800 border-rose-200',
  },
};

function fmtBound(val: number | undefined): string {
  if (val === undefined) return '—';
  return val >= PN_DN_SATURATION ? 'SAT' : String(val);
}

export const BranchCoveragePanel: React.FC<BranchCoveragePanelProps> = ({
  problem,
  context,
  rootInitialPosition,
  activeBaseMoves,
  solverConfig,
  solveReport,
}) => {
  const snapshots = useMemo(
    () => solveReport.branchCoverageSnapshots ?? [],
    [solveReport.branchCoverageSnapshots]
  );

  const defaultSelectedPath = useMemo(() => {
    const firstChild = snapshots.find((s) => s.depth === 1);
    return firstChild ? firstChild.path : snapshots[0]?.path ?? '';
  }, [snapshots]);

  const [selectedPath, setSelectedPath] = useState<string>(defaultSelectedPath);
  const [moveFilter, setMoveFilter] = useState<MoveStatusFilter>('all');
  const [customPathInput, setCustomPathInput] = useState<string>('');
  const [customPathError, setCustomPathError] = useState<string | null>(null);
  const [querySiblingMoveSgf, setQuerySiblingMoveSgf] = useState<string>('');
  const [fragmentReceipt, setFragmentReceipt] = useState<{
    title: string;
    result: SubproofFragmentVerificationResult;
  } | null>(null);
  const [standaloneSubSolve, setStandaloneSubSolve] =
    useState<StandaloneSubSolveReceipt | null>(null);

  // Reset local audit state whenever the problem or solve report changes
  useEffect(() => {
    setSelectedPath(defaultSelectedPath);
    setMoveFilter('all');
    setQuerySiblingMoveSgf('');
    setFragmentReceipt(null);
    setStandaloneSubSolve(null);
    setCustomPathError(null);
  }, [problem.id, solveReport.inputHash, solveReport.numNodes, defaultSelectedPath]);

  const activeSnapshot: BranchCoverageSnapshot | undefined = useMemo(
    () => snapshots.find((s) => s.path === selectedPath) ?? snapshots[0],
    [snapshots, selectedPath]
  );

  const filteredMoves = useMemo(() => {
    if (!activeSnapshot) return [];
    return activeSnapshot.moves.filter((m) => {
      if (moveFilter === 'all') return true;
      if (moveFilter === 'closed') {
        return (
          m.status === 'PROVEN_SOURCE' ||
          m.status === 'TT_REPLAYED' ||
          m.status === 'RZ_REVALIDATED'
        );
      }
      if (moveFilter === 'deferred') return m.status === 'DEFERRED_OUTSIDE_RZ';
      if (moveFilter === 'unresolved') {
        return (
          m.status === 'EXPANDED_UNRESOLVED' || m.status === 'KO_BARRIER'
        );
      }
      return m.status === 'UNEXPANDED';
    });
  }, [activeSnapshot, moveFilter]);

  const parseSgfPath = (
    raw: string
  ): { moves: number[]; sgf: string[] } | { error: string } => {
    const cleaned = raw.trim().replace(/^\/+|\/+$/g, '');
    if (!cleaned) {
      return { moves: [], sgf: [] };
    }
    const segs = cleaned.split('/').filter(Boolean);
    const moves: number[] = [];
    const sgf: string[] = [];
    for (const seg of segs) {
      const lower = seg.toLowerCase();
      if (lower === 'pass' || lower === 'tt') {
        moves.push(PASS_MOVE);
        sgf.push('pass');
      } else if (/^[a-s]{2}$/.test(lower)) {
        const coord = sgfToCoord(lower, problem.boardSize);
        if (coord < 0) {
          return { error: `无效 SGF 坐标片段: "${seg}"` };
        }
        moves.push(coord);
        sgf.push(lower);
      } else {
        return {
          error: `无法解析路径片段 "${seg}"（请使用如 sr/pass 或 rs/as 的 SGF 坐标）`,
        };
      }
    }
    return { moves, sgf };
  };

  const handleVerifyFragment = (
    title: string,
    targetPathMoves: number[],
    targetDagNodeId: number,
    queryPathMoves?: number[]
  ) => {
    const checker = new ProofArtifactManager();
    const fullTargetMoves = [...activeBaseMoves, ...targetPathMoves];
    const fullQueryMoves = queryPathMoves
      ? [...activeBaseMoves, ...queryPathMoves]
      : undefined;
    const result = checker.verifySubproofFragment({
      problem,
      context,
      report: solveReport,
      targetPathMoves: fullTargetMoves,
      targetDagNodeId,
      queryPathMoves: fullQueryMoves,
      runSource:
        activeBaseMoves.length > 0 ? 'standalone_subposition' : 'original_root',
    });
    setFragmentReceipt({ title, result });
  };

  const handleRunStandaloneSubSolve = (moves: number[], sgfLabels: string[]) => {
    setCustomPathError(null);
    const pos = rootInitialPosition.clone();
    for (let i = 0; i < moves.length; i++) {
      const res = pos.playMove(moves[i]);
      if (!res.legal) {
        setCustomPathError(
          `路径第 ${i + 1} 手 ${sgfLabels[i]} 在原题局面下不合法（可能自杀、已有子或违反劫规则）`
        );
        return;
      }
    }
    const solver = new DfpnSolver(solverConfig);
    const subReport = solver.solveFromPosition(problem, pos, context);
    const checker = new ProofArtifactManager();
    const tracedVerification = checker.verifySerializedLProofJson(
      subReport.lproofJson,
      {
        problem,
        context,
        scope: 'traced_within_rules',
      }
    );
    const originalRootVerification = checker.verifySerializedLProofJson(
      subReport.lproofJson,
      {
        problem,
        context,
        scope: 'original_root',
      }
    );
    setStandaloneSubSolve({
      pathLabel: sgfLabels.length > 0 ? sgfLabels.join('/') : '(root)',
      pathSgf: sgfLabels,
      report: subReport,
      tracedVerification,
      originalRootVerification,
    });
  };

  const handleCustomStandaloneSubmit = (e: React.FormEvent) => {
    e.preventDefault();
    const parsed = parseSgfPath(customPathInput);
    if ('error' in parsed) {
      setCustomPathError(parsed.error);
      return;
    }
    handleRunStandaloneSubSolve(parsed.moves, parsed.sgf);
  };

  const runSource = snapshots[0]?.runSource ?? 'original_root';
  const siblingReplayCandidates = useMemo(() => {
    if (!activeSnapshot) return [];
    return activeSnapshot.moves.slice(0, 60);
  }, [activeSnapshot]);

  return (
    <div className="border border-slate-200 bg-white rounded-lg p-6 space-y-5">
      {/* Header & Provenance */}
      <div className="flex flex-wrap items-start justify-between gap-4 pb-4 border-b border-slate-200">
        <div>
          <div className="flex items-center gap-2">
            <GitBranch className="h-4 w-4 text-slate-700" />
            <h2 className="text-base font-semibold text-slate-900">
              分支覆盖与子证明审计 (Generic Branch Coverage &amp; Sub-Proof Audit)
            </h2>
          </div>
          <p className="mt-1 text-xs text-slate-500">
            直接基于求解器真实前沿快照统计应手覆盖，严格区分「已重验闭合」与「RZ 外暂缓」，以及「原次原根搜索」与「独立子局面重搜」的作用域边界。
          </p>
        </div>

        <div className="flex flex-wrap items-center gap-2 text-xs font-mono">
          <span
            className={`px-2.5 py-1 rounded border font-semibold ${
              runSource === 'original_root'
                ? 'bg-slate-100 text-slate-800 border-slate-300'
                : 'bg-indigo-50 text-indigo-800 border-indigo-200'
            }`}
          >
            来源:{' '}
            {runSource === 'original_root'
              ? '原次原根搜索 (original_root)'
              : '独立子局面 (standalone_subposition)'}
          </span>
          <span
            className={`px-2.5 py-1 rounded border font-semibold ${
              solveReport.rootStatus === ProofOutcome.ProvenWin
                ? 'bg-emerald-50 text-emerald-800 border-emerald-200'
                : solveReport.rootStatus === ProofOutcome.ProvenLoss
                ? 'bg-amber-50 text-amber-800 border-amber-200'
                : 'bg-slate-100 text-slate-700 border-slate-300'
            }`}
          >
            根结论: {solveReport.rootStatus} ({solveReport.numNodes} 节点)
          </span>
        </div>
      </div>

      {/* Generic Custom Sub-Path Standalone Re-Solve Bar */}
      <form
        onSubmit={handleCustomStandaloneSubmit}
        className="flex flex-wrap items-center gap-2 rounded-md border border-slate-200 bg-slate-50 px-3.5 py-2.5"
      >
        <span className="text-xs font-medium text-slate-700">
          独立子局面路径重搜（不覆盖上方原根报表）:
        </span>
        <input
          type="text"
          value={customPathInput}
          onChange={(e) => setCustomPathInput(e.target.value)}
          placeholder="输入 SGF 路径，如 sr/pass 或 rs/as"
          className="flex-1 min-w-[200px] rounded border border-slate-300 bg-white px-2.5 py-1 text-xs font-mono text-slate-900 focus:border-slate-500 focus:outline-none"
        />
        <button
          type="submit"
          className="inline-flex items-center gap-1.5 rounded bg-slate-900 px-3 py-1.5 text-xs font-medium text-white hover:bg-slate-800 cursor-pointer"
        >
          <Play className="h-3 w-3" />
          独立重搜并双作用域校验
        </button>
        {customPathError && (
          <span className="w-full text-xs text-rose-700 font-medium">
            {customPathError}
          </span>
        )}
      </form>

      {/* Branch Coverage Summary Table */}
      <div className="overflow-x-auto">
        <table className="w-full text-left border-collapse text-xs font-mono tabular-nums">
          <thead>
            <tr className="border-b border-slate-200 text-slate-500">
              <th className="py-2 pr-3">路径</th>
              <th className="py-2 px-2">义务</th>
              <th className="py-2 px-2">节点结论 / DAG</th>
              <th className="py-2 px-2 text-right">闭合 / 合法应手</th>
              <th className="py-2 px-2">来源细分 (源 / TT / RZ重验 / RZ外暂缓 / 未决 / 未展)</th>
              <th className="py-2 px-2">最后退出与阈值</th>
              <th className="py-2 pl-2 text-right">独立审计</th>
            </tr>
          </thead>
          <tbody className="divide-y divide-slate-200">
            {snapshots.map((snap) => {
              const isSelected = snap.path === activeSnapshot?.path;
              return (
                <tr
                  key={snap.path || '(root)'}
                  onClick={() => {
                    setSelectedPath(snap.path);
                    setQuerySiblingMoveSgf('');
                  }}
                  className={`cursor-pointer transition-colors ${
                    isSelected ? 'bg-slate-100/90' : 'hover:bg-slate-50'
                  }`}
                >
                  <td className="py-2 pr-3 font-semibold text-slate-900">
                    {snap.path ? snap.path : '(root)'}
                  </td>
                  <td className="py-2 px-2 text-slate-700">
                    {snap.obligation === 'EXISTENTIAL_OR'
                      ? 'OR 存在'
                      : 'AND 全称'}{' '}
                    · {snap.toPlay === Color.Black ? 'B' : 'W'}
                  </td>
                  <td className="py-2 px-2">
                    <span
                      className={`font-semibold ${
                        snap.nodeOutcome === ProofOutcome.ProvenWin
                          ? 'text-emerald-700'
                          : snap.nodeOutcome === ProofOutcome.ProvenLoss
                          ? 'text-amber-700'
                          : 'text-slate-600'
                      }`}
                    >
                      {snap.nodeOutcome}
                    </span>{' '}
                    <span className="text-slate-500">
                      {snap.nodeDagNodeId >= 0
                        ? `#${snap.nodeDagNodeId}`
                        : '(未闭合)'}
                    </span>
                  </td>
                  <td className="py-2 px-2 text-right font-semibold text-slate-900">
                    {snap.totalLegalMoves > 0
                      ? `${snap.closedCount} / ${snap.totalLegalMoves}`
                      : snap.terminalEvidence}
                  </td>
                  <td className="py-2 px-2 text-slate-700">
                    {snap.totalLegalMoves > 0 ? (
                      <span>
                        <span className="text-emerald-700">
                          源:{snap.provenSourceCount}
                        </span>{' '}
                        ·{' '}
                        <span className="text-sky-700">
                          TT:{snap.ttReplayedCount}
                        </span>{' '}
                        ·{' '}
                        <span className="text-indigo-700">
                          RZ:{snap.rzRevalidatedCount}
                        </span>{' '}
                        ·{' '}
                        <span className="text-amber-700">
                          暂缓:{snap.deferredOutsideRzCount}
                        </span>{' '}
                        ·{' '}
                        <span className="text-orange-700">
                          未决:{snap.expandedUnresolvedCount}
                        </span>{' '}
                        ·{' '}
                        <span className="text-slate-500">
                          未展:{snap.unexpandedCount}
                        </span>
                      </span>
                    ) : (
                      <span className="text-slate-500">
                        终局/直接返回 ({snap.terminalEvidence})
                      </span>
                    )}
                  </td>
                  <td className="py-2 px-2 text-slate-600">
                    {snap.lastExitReason} · pn/dn={fmtBound(snap.lastPn)}/
                    {fmtBound(snap.lastDn)} · th={fmtBound(snap.lastThPn)}/
                    {fmtBound(snap.lastThDn)}
                  </td>
                  <td
                    className="py-2 pl-2 text-right whitespace-nowrap"
                    onClick={(e) => e.stopPropagation()}
                  >
                    <button
                      type="button"
                      onClick={() =>
                        handleVerifyFragment(
                          snap.path || '(root)',
                          snap.movesFromRoot,
                          snap.nodeDagNodeId
                        )
                      }
                      className="inline-flex items-center gap-1 rounded border border-slate-300 bg-white px-2 py-1 text-[11px] font-medium text-slate-800 hover:bg-slate-50 cursor-pointer"
                    >
                      <ShieldCheck className="h-3 w-3" />
                      校验片段
                    </button>
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
      </div>

      {/* Independent Sub-Proof Fragment Verification Receipt */}
      {fragmentReceipt && (
        <div className="rounded-md border border-slate-200 bg-slate-50 p-4 space-y-2.5 text-xs">
          <div className="flex flex-wrap items-center justify-between gap-2">
            <div className="font-semibold text-slate-900">
              子证明片段独立校验回执 — 目标路径: <code>{fragmentReceipt.title}</code>
            </div>
            <span className="font-mono text-slate-500">
              原搜索结论: {fragmentReceipt.result.originalRootOutcome} (
              {fragmentReceipt.result.runSource})
            </span>
          </div>

          <div className="grid grid-cols-1 gap-3 md:grid-cols-2">
            {/* Source Receipt */}
            <div
              className={`rounded border p-3 ${
                fragmentReceipt.result.sourceReceipt.passed
                  ? 'border-emerald-200 bg-emerald-50/70'
                  : fragmentReceipt.result.sourceReceipt.status === 'UNCLOSED'
                  ? 'border-amber-200 bg-amber-50/70'
                  : 'border-rose-200 bg-rose-50/70'
              }`}
            >
              <div className="flex items-center gap-1.5 font-semibold">
                {fragmentReceipt.result.sourceReceipt.passed ? (
                  <CheckCircle2 className="h-4 w-4 text-emerald-700" />
                ) : fragmentReceipt.result.sourceReceipt.status ===
                  'UNCLOSED' ? (
                  <ShieldAlert className="h-4 w-4 text-amber-700" />
                ) : (
                  <XCircle className="h-4 w-4 text-rose-700" />
                )}
                <span>
                  源片段校验: {fragmentReceipt.result.sourceReceipt.status} (
                  {fragmentReceipt.result.sourceReceipt.errorCode})
                </span>
              </div>
              <p className="mt-1 text-slate-700">
                {fragmentReceipt.result.sourceReceipt.message}
              </p>
              <div className="mt-1.5 font-mono text-[11px] text-slate-600">
                DAG=#{fragmentReceipt.result.sourceReceipt.targetDagNodeId} ·
                nodes={fragmentReceipt.result.sourceReceipt.verifiedNodes} ·
                leaves={fragmentReceipt.result.sourceReceipt.verifiedLeaves} ·
                pruned={fragmentReceipt.result.sourceReceipt.replayedPruned} ·
                tt={fragmentReceipt.result.sourceReceipt.replayedTt}
              </div>
            </div>

            {/* Query Replay Receipt */}
            <div
              className={`rounded border p-3 ${
                fragmentReceipt.result.queryReplayReceipt.status ===
                'NOT_REQUESTED'
                  ? 'border-slate-200 bg-white'
                  : fragmentReceipt.result.queryReplayReceipt.passed
                  ? 'border-indigo-200 bg-indigo-50/70'
                  : 'border-rose-200 bg-rose-50/70'
              }`}
            >
              <div className="flex items-center gap-1.5 font-semibold text-slate-900">
                <span>
                  复用重放校验: {fragmentReceipt.result.queryReplayReceipt.status}{' '}
                  ({fragmentReceipt.result.queryReplayReceipt.errorCode})
                </span>
              </div>
              <p className="mt-1 text-slate-700">
                {fragmentReceipt.result.queryReplayReceipt.message}
              </p>
              {fragmentReceipt.result.queryReplayReceipt.queryPathSgf.length >
                0 && (
                <div className="mt-1.5 font-mono text-[11px] text-slate-600">
                  query=
                  {fragmentReceipt.result.queryReplayReceipt.queryPathSgf.join(
                    '/'
                  )}{' '}
                  · historyLen=
                  {fragmentReceipt.result.queryReplayReceipt.queryHistoryLength}
                </div>
              )}
            </div>
          </div>
        </div>
      )}

      {/* Side-by-Side Standalone Subposition Re-Solve Receipt (separate from original-root table) */}
      {standaloneSubSolve && (
        <div className="rounded-md border border-indigo-200 bg-indigo-50/50 p-4 space-y-2.5 text-xs">
          <div className="flex flex-wrap items-center justify-between gap-2">
            <div className="font-semibold text-indigo-950">
              独立子局面重搜结果 (standalone_subposition) — 路径:{' '}
              <code>{standaloneSubSolve.pathLabel}</code>
            </div>
            <button
              type="button"
              onClick={() => setStandaloneSubSolve(null)}
              className="text-xs text-slate-500 hover:text-slate-800 cursor-pointer"
            >
              关闭此对比卡
            </button>
          </div>
          <div className="grid grid-cols-1 gap-3 md:grid-cols-3 font-mono">
            <div className="rounded border border-indigo-200 bg-white p-2.5">
              <div className="text-[11px] text-slate-500">子局面求解结论</div>
              <div className="mt-1 font-semibold text-slate-900">
                {standaloneSubSolve.report.rootStatus} · best=
                {standaloneSubSolve.report.bestMoveSgf ?? '—'} ·{' '}
                {standaloneSubSolve.report.numNodes} 节点
              </div>
              <div className="mt-0.5 text-[11px] text-slate-500">
                DAG 节点={standaloneSubSolve.report.proofDagNodes.length} · RZ
                剪枝={standaloneSubSolve.report.prunedOutsideRzCount}
              </div>
            </div>
            <div
              className={`rounded border p-2.5 ${
                standaloneSubSolve.tracedVerification.passed
                  ? 'border-emerald-200 bg-emerald-50/70'
                  : 'border-rose-200 bg-rose-50/70'
              }`}
            >
              <div className="text-[11px] text-slate-600">
                试下作用域 (traced_within_rules)
              </div>
              <div className="mt-1 font-semibold text-slate-900">
                {standaloneSubSolve.tracedVerification.passed ? 'PASS' : 'FAIL'}{' '}
                ({standaloneSubSolve.tracedVerification.errorCode})
              </div>
              <div className="mt-0.5 text-[11px] text-slate-600 truncate">
                {standaloneSubSolve.tracedVerification.message}
              </div>
            </div>
            <div
              className={`rounded border p-2.5 ${
                standaloneSubSolve.originalRootVerification.passed
                  ? 'border-emerald-200 bg-emerald-50/70'
                  : 'border-amber-200 bg-amber-50/70'
              }`}
            >
              <div className="text-[11px] text-slate-600">
                原根作用域 (original_root)
              </div>
              <div className="mt-1 font-semibold text-slate-900">
                {standaloneSubSolve.originalRootVerification.passed
                  ? 'PASS'
                  : 'REJECTED'}{' '}
                ({standaloneSubSolve.originalRootVerification.errorCode})
              </div>
              <div className="mt-0.5 text-[11px] text-slate-600 truncate">
                {standaloneSubSolve.originalRootVerification.message}
              </div>
            </div>
          </div>
        </div>
      )}

      {/* Selected Branch Per-Move Coverage Breakdown */}
      {activeSnapshot && activeSnapshot.moves.length > 0 && (
        <div className="space-y-3 pt-2 border-t border-slate-200">
          <div className="flex flex-wrap items-center justify-between gap-3">
            <div className="text-xs text-slate-700">
              <span className="font-semibold text-slate-900">
                当前分支应手明细: {activeSnapshot.path || '(root)'}
              </span>
              {activeSnapshot.representativeMoveSgf && (
                <span className="ml-2 font-mono text-indigo-700">
                  代表源证明: {activeSnapshot.representativeMoveSgf} (DAG #
                  {activeSnapshot.representativeDagNodeId}, RZ=
                  {activeSnapshot.representativeRzSize})
                </span>
              )}
            </div>

            <div className="flex flex-wrap items-center gap-2 text-xs">
              <label className="inline-flex items-center gap-1.5 text-slate-600">
                <span>复用查询应手:</span>
                <select
                  value={querySiblingMoveSgf}
                  onChange={(e) => setQuerySiblingMoveSgf(e.target.value)}
                  className="rounded border border-slate-300 bg-white px-2 py-1 text-xs font-mono text-slate-800"
                >
                  <option value="">(不测复用)</option>
                  {siblingReplayCandidates.map((m) => (
                    <option key={m.moveSgf} value={m.moveSgf}>
                      {m.moveSgf} ({STATUS_BADGE_MAP[m.status].label})
                    </option>
                  ))}
                </select>
              </label>

              <div className="inline-flex rounded border border-slate-200 bg-slate-50 p-0.5">
                {(
                  [
                    ['all', `全部 (${activeSnapshot.totalLegalMoves})`],
                    ['closed', `已闭合 (${activeSnapshot.closedCount})`],
                    [
                      'deferred',
                      `RZ暂缓 (${activeSnapshot.deferredOutsideRzCount})`,
                    ],
                    [
                      'unresolved',
                      `未决 (${
                        activeSnapshot.expandedUnresolvedCount +
                        activeSnapshot.koBarrierCount
                      })`,
                    ],
                    ['unexpanded', `未展 (${activeSnapshot.unexpandedCount})`],
                  ] as [MoveStatusFilter, string][]
                ).map(([key, label]) => (
                  <button
                    key={key}
                    type="button"
                    onClick={() => setMoveFilter(key)}
                    className={`px-2 py-0.5 rounded text-[11px] font-medium cursor-pointer ${
                      moveFilter === key
                        ? 'bg-slate-900 text-white'
                        : 'text-slate-600 hover:text-slate-900'
                    }`}
                  >
                    {label}
                  </button>
                ))}
              </div>
            </div>
          </div>

          <div className="max-h-72 overflow-y-auto overflow-x-auto border border-slate-200 rounded-md">
            <table className="w-full text-left border-collapse text-xs font-mono tabular-nums">
              <thead className="sticky top-0 bg-slate-50 border-b border-slate-200 text-slate-500">
                <tr>
                  <th className="py-2 pl-3 pr-2">#</th>
                  <th className="py-2 px-2">应手</th>
                  <th className="py-2 px-2">覆盖状态</th>
                  <th className="py-2 px-2 text-right">评分</th>
                  <th className="py-2 px-2 text-right">PN / DN</th>
                  <th className="py-2 px-2">DAG / 源引用</th>
                  <th className="py-2 px-2">最近退出</th>
                  <th className="py-2 pl-2 pr-3 text-right">操作</th>
                </tr>
              </thead>
              <tbody className="divide-y divide-slate-200 bg-white">
                {filteredMoves.slice(0, 150).map((m: BranchMoveCoverageEntry) => {
                  const badge = STATUS_BADGE_MAP[m.status];
                  const childMoves = [...activeSnapshot.movesFromRoot, m.move];
                  const childSgf = [
                    ...activeSnapshot.movesFromRootSgf,
                    m.moveSgf,
                  ];
                  const queryTarget = querySiblingMoveSgf
                    ? activeSnapshot.moves.find(
                        (cand) => cand.moveSgf === querySiblingMoveSgf
                      )
                    : undefined;
                  const queryMoves =
                    queryTarget && queryTarget.move !== m.move
                      ? [...activeSnapshot.movesFromRoot, queryTarget.move]
                      : undefined;
                  return (
                    <tr key={`${m.rank}-${m.moveSgf}`} className="hover:bg-slate-50">
                      <td className="py-1.5 pl-3 pr-2 text-slate-400">
                        {m.rank + 1}
                      </td>
                      <td className="py-1.5 px-2 font-semibold text-slate-900">
                        {m.moveSgf}{' '}
                        <span className="font-normal text-slate-400">
                          ({coordToHumanLabel(m.move, problem.boardSize)})
                        </span>
                      </td>
                      <td className="py-1.5 px-2">
                        <span
                          className={`inline-block rounded border px-1.5 py-0.5 text-[11px] font-sans font-medium ${badge.className}`}
                        >
                          {badge.label}
                        </span>
                      </td>
                      <td className="py-1.5 px-2 text-right text-slate-600">
                        {m.tacticalScore}
                      </td>
                      <td className="py-1.5 px-2 text-right text-slate-700">
                        {fmtBound(m.pn)} / {fmtBound(m.dn)}
                      </td>
                      <td className="py-1.5 px-2 text-slate-600">
                        {m.dagNodeId >= 0 ? `#${m.dagNodeId}` : '—'}
                        {m.sourceProofNodeId !== null
                          ? ` ← #${m.sourceProofNodeId}`
                          : ''}
                      </td>
                      <td className="py-1.5 px-2 text-slate-500">
                        {m.lastExitReason ?? '—'}
                      </td>
                      <td className="py-1.5 pl-2 pr-3 text-right whitespace-nowrap space-x-1.5">
                        <button
                          type="button"
                          onClick={() =>
                            handleVerifyFragment(
                              childSgf.join('/'),
                              childMoves,
                              m.dagNodeId,
                              queryMoves
                            )
                          }
                          className="rounded border border-slate-300 bg-white px-2 py-0.5 text-[11px] font-sans font-medium text-slate-700 hover:bg-slate-50 cursor-pointer"
                        >
                          校验
                        </button>
                        <button
                          type="button"
                          onClick={() =>
                            handleRunStandaloneSubSolve(
                              [...activeBaseMoves, ...childMoves],
                              childSgf
                            )
                          }
                          className="rounded border border-indigo-200 bg-indigo-50 px-2 py-0.5 text-[11px] font-sans font-medium text-indigo-800 hover:bg-indigo-100 cursor-pointer"
                        >
                          重搜
                        </button>
                      </td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
        </div>
      )}
    </div>
  );
};
