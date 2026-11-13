/**
 * @license
 * SPDX-License-Identifier: Apache-2.0
 */

import React, { useMemo, useState } from 'react';
import {
  CheckCircle2,
  Code2,
  Copy,
  Download,
  FileCheck2,
  Layers,
  Play,
  RotateCcw,
  ShieldAlert,
  SkipBack,
  SkipForward,
  StepBack,
  StepForward,
  Terminal,
} from 'lucide-react';
import { TsumegoBoardView } from './components/TsumegoBoardView';
import { BensonTerminalEvaluator } from './engine/bensonUca';
import { CPP_SOURCE_FILES } from './engine/cppSourceRegistry';
import { DfpnSolver } from './engine/dfpnSolver';
import {
  coordToHumanLabel,
  coordToSgf,
  PASS_MOVE,
} from './engine/position';
import { TSUMEGO_PROBLEMS_CATALOG } from './engine/problemsCatalog';
import {
  AVAILABLE_GITHUB_STUDY_LD_RZ_FILES,
  parseStudyLdRzJsonToProblemSpec,
  RawStudyLdRzProblemJson,
  STUDY_LD_RZ_FAILURE_TAXONOMY,
  validateStudyLdRzContract,
} from './engine/studyLdRzCatalog';
import { ProofArtifactManager } from './engine/proofChecker';
import {
  Color,
  KoRule,
  PN_DN_SATURATION,
  ProofOutcome,
  SolveReport,
  SolverConfig,
  TsumegoProblemSpec,
  VerificationReport,
} from './engine/types';

type ActiveWorkspaceTab =
  | 'workbench'
  | 'proof-dag'
  | 'checker'
  | 'cpp-source'
  | 'benchmark';

type FaultInjectionMode =
  | 'none'
  | 'lp-n15-violation'
  | 'lp-t02-topology'
  | 'jcs-checksum-tamper'
  | 'missing-pruned-cert';

export default function App() {
  const [activeTab, setActiveTab] = useState<ActiveWorkspaceTab>('workbench');
  const [customProblems, setCustomProblems] = useState<TsumegoProblemSpec[]>([]);
  const [selectedProblemId, setSelectedProblemId] = useState<string>(
    TSUMEGO_PROBLEMS_CATALOG[0].id
  );
  const [problemFilterText, setProblemFilterText] = useState<string>('');
  const [datasetGroupFilter, setDatasetGroupFilter] = useState<
    'all' | 'study-ld-rz' | 'srs-benchmark'
  >('all');
  const [githubFilenameInput, setGithubFilenameInput] = useState<string>(
    'chao_vol1_p098.json'
  );
  const [isFetchingGithub, setIsFetchingGithub] = useState<boolean>(false);

  // Solver Configuration State (FR-4, FR-5, FR-6, FR-7)
  // Initialized from the default problem's ko contract with `useProblemDefaultKo: false`
  // so interactive checkbox toggles work bidirectionally (both true -> false and false -> true).
  const [solverConfig, setSolverConfig] = useState<SolverConfig>(() => {
    const firstProb = TSUMEGO_PROBLEMS_CATALOG[0];
    return {
      maxNodes: 3500,
      maxDepth: 48,
      memoryBudgetMb: 512,
      ttMode: 'pattern-tt',
      enableRzPruning: true,
      enableFastCaptureOrdering: true,
      enableProgressiveWidening: true,
      wideningBaseK: 8,
      deterministicMode: true,
      koRule: KoRule.SituationalSuperko,
      attackerAllowKo: Boolean(
        firstProb.attackerAllowKo ?? firstProb.defaultAllowKo
      ),
      defenderAllowKo: firstProb.defenderAllowKo ?? true,
      useProblemDefaultKo: false,
    };
  });

  // Board Viewport & Overlay State
  const [showFullBoard, setShowFullBoard] = useState<boolean>(false);
  const [overlayMode, setOverlayMode] = useState<
    'proof-rz' | 'disproof-rz' | 'benson-uca' | 'none'
  >('proof-rz');
  const [pvSourceMode, setPvSourceMode] = useState<'engine' | 'reference'>(
    'engine'
  );
  const [pvStepIndex, setPvStepIndex] = useState<number | null>(null);
  const [manualMoves, setManualMoves] = useState<number[]>([]);
  const [solveManualSubposition, setSolveManualSubposition] =
    useState<boolean>(false);
  const [statusToast, setStatusToast] = useState<string | null>(null);

  // C++ Source Browser State
  const [selectedCppPath, setSelectedCppPath] = useState<string>(
    CPP_SOURCE_FILES[0].path
  );
  const [copiedFeedback, setCopiedFeedback] = useState<string | null>(null);

  // Proof Checker Fault Injection State
  const [faultMode, setFaultMode] = useState<FaultInjectionMode>('none');

  // Contract Parser Test State (FR-1.1..1.3)
  const [contractPreset, setContractPreset] = useState<
    | 'valid'
    | 'turn-conflict'
    | 'mixed-op'
    | 'missing-crucial'
    | 'empty-crucial'
  >('valid');

  // Batch Benchmark Results
  const [batchReports, setBatchReports] = useState<
    {
      problem: TsumegoProblemSpec;
      report: SolveReport;
      verification: VerificationReport;
    }[]
  >([]);

  const allProblems = useMemo(
    () => [...customProblems, ...TSUMEGO_PROBLEMS_CATALOG],
    [customProblems]
  );

  const currentProblem = useMemo(
    () =>
      allProblems.find((p) => p.id === selectedProblemId) ?? allProblems[0],
    [allProblems, selectedProblemId]
  );

  // Build root ProofContext and root initial position
  const { rootInitialPosition, proofContext } = useMemo(() => {
    const ctx = DfpnSolver.buildProofContext(currentProblem, solverConfig);
    const initPos = DfpnSolver.buildInitialPosition(currentProblem, ctx);
    return {
      rootInitialPosition: initPos,
      proofContext: ctx,
    };
  }, [currentProblem, solverConfig]);

  // Active solve root: either problem initial root, or user-requested manual sub-position
  // (replayed from rootInitialPosition so survivingTargetTokensMask & SSK HistorySet stay exact).
  const activeSolvePosition = useMemo(() => {
    if (!solveManualSubposition || manualMoves.length === 0) {
      return rootInitialPosition;
    }
    const subPos = rootInitialPosition.clone();
    for (const mv of manualMoves) {
      subPos.playMove(mv);
    }
    return subPos;
  }, [rootInitialPosition, solveManualSubposition, manualMoves]);

  // Run DfpnSolver on activeSolvePosition + proofContext
  const solveReport = useMemo(() => {
    const solver = new DfpnSolver(solverConfig);
    return solver.solveFromPosition(
      currentProblem,
      activeSolvePosition,
      proofContext
    );
  }, [currentProblem, activeSolvePosition, proofContext, solverConfig]);

  // Active Principal Variation sequence (either LDProver engine PV or rawsgf reference PV)
  const activePvSequence = useMemo(() => {
    if (solveManualSubposition && manualMoves.length > 0) {
      return solveReport.principalVariation;
    }
    if (
      pvSourceMode === 'reference' &&
      currentProblem.referencePv &&
      currentProblem.referencePv.length > 0
    ) {
      return currentProblem.referencePv;
    }
    if (
      solveReport.principalVariation.length === 0 &&
      currentProblem.referencePv &&
      currentProblem.referencePv.length > 0
    ) {
      return currentProblem.referencePv;
    }
    return solveReport.principalVariation;
  }, [
    solveManualSubposition,
    manualMoves.length,
    pvSourceMode,
    currentProblem,
    solveReport,
  ]);

  // Compute current displayed board position (manual exploration or PV playback)
  const displayedPosition = useMemo(() => {
    if (manualMoves.length > 0 && !solveManualSubposition) {
      const pos = rootInitialPosition.clone();
      for (const mv of manualMoves) {
        pos.playMove(mv);
      }
      return pos;
    }
    const pos = activeSolvePosition.clone();
    if (pvStepIndex !== null && pvStepIndex >= 0) {
      for (
        let i = 0;
        i <= pvStepIndex && i < activePvSequence.length;
        i++
      ) {
        pos.playMove(activePvSequence[i].move);
      }
    }
    return pos;
  }, [
    rootInitialPosition,
    activeSolvePosition,
    manualMoves,
    solveManualSubposition,
    pvStepIndex,
    activePvSequence,
  ]);

  // Live terminal evaluation on displayedPosition
  const liveTerminalEval = useMemo(() => {
    const evaluator = new BensonTerminalEvaluator();
    return evaluator.evaluateTerminal(displayedPosition, proofContext);
  }, [displayedPosition, proofContext]);

  // Independent lproof/1 Proof Checker execution (with semantic re-signing in Fault Injection Sandbox)
  const verificationReport = useMemo((): VerificationReport => {
    const checker = new ProofArtifactManager();
    if (faultMode === 'none') {
      return checker.verifyProofDag(
        activeSolvePosition,
        proofContext,
        solveReport
      );
    }

    const clonedReport: SolveReport = JSON.parse(JSON.stringify(solveReport));
    if (
      faultMode === 'lp-n15-violation' &&
      clonedReport.proofDagNodes.length > 0
    ) {
      const rootIdx = clonedReport.rootDagNodeId;
      if (rootIdx >= 0 && rootIdx < clonedReport.proofDagNodes.length) {
        clonedReport.proofDagNodes[rootIdx].pn = 7;
        clonedReport.proofDagNodes[rootIdx].dn = 42;
      }
      clonedReport.proofChecksum = checker.serializeLProofJson(
        activeSolvePosition,
        proofContext,
        clonedReport
      ).checksum;
    } else if (
      faultMode === 'lp-t02-topology' &&
      clonedReport.proofDagNodes.length > 0
    ) {
      const rootIdx = clonedReport.rootDagNodeId;
      if (rootIdx >= 0 && rootIdx < clonedReport.proofDagNodes.length) {
        clonedReport.proofDagNodes[rootIdx].childNodeIds.push(rootIdx + 99);
        clonedReport.proofDagNodes[rootIdx].childMoves.push(PASS_MOVE);
      }
      clonedReport.proofChecksum = checker.serializeLProofJson(
        activeSolvePosition,
        proofContext,
        clonedReport
      ).checksum;
    } else if (faultMode === 'jcs-checksum-tamper') {
      clonedReport.proofChecksum =
        'sha256-jcs:deadbeef00000000cafebabe11111111';
    } else if (faultMode === 'missing-pruned-cert') {
      let mutatedPruned = false;
      for (const n of clonedReport.proofDagNodes) {
        if (n.isPrunedOutsideRz) {
          delete n.prunedCertificate;
          mutatedPruned = true;
        }
      }
      if (!mutatedPruned && clonedReport.proofDagNodes.length > 0) {
        const rootIdx = Math.max(0, clonedReport.rootDagNodeId);
        if (clonedReport.proofDagNodes[rootIdx]) {
          clonedReport.proofDagNodes[rootIdx].isPrunedOutsideRz = true;
          clonedReport.proofDagNodes[rootIdx].sourceProofNodeId = rootIdx;
          delete clonedReport.proofDagNodes[rootIdx].prunedCertificate;
        }
      }
      clonedReport.proofChecksum = checker.serializeLProofJson(
        activeSolvePosition,
        proofContext,
        clonedReport
      ).checksum;
    }

    return checker.verifyProofDag(
      activeSolvePosition,
      proofContext,
      clonedReport
    );
  }, [activeSolvePosition, proofContext, solveReport, faultMode]);

  // Process-independent standalone JSON text verifier (runs when viewing Tab 3 Checker)
  const standaloneJsonVerification = useMemo((): VerificationReport | null => {
    if (activeTab !== 'checker' || faultMode !== 'none') return null;
    const checker = new ProofArtifactManager();
    return checker.verifySerializedLProofJson(solveReport.lproofJson);
  }, [activeTab, faultMode, solveReport.lproofJson]);

  const handleSelectProblem = (
    problemId: string,
    explicitSpec?: TsumegoProblemSpec
  ) => {
    const targetProb =
      explicitSpec ?? allProblems.find((p) => p.id === problemId);
    setSelectedProblemId(problemId);
    setPvStepIndex(null);
    setManualMoves([]);
    setSolveManualSubposition(false);
    setStatusToast(null);
    if (targetProb) {
      setSolverConfig((prev) => ({
        ...prev,
        attackerAllowKo: Boolean(
          targetProb.attackerAllowKo ?? targetProb.defaultAllowKo
        ),
        defenderAllowKo: targetProb.defenderAllowKo ?? true,
        useProblemDefaultKo: false,
      }));
    }
  };

  const handleFetchGithubProblem = async (targetFilename?: string) => {
    const rawName = (targetFilename ?? githubFilenameInput).trim();
    if (!rawName) return;
    const filename = rawName.endsWith('.json') ? rawName : `${rawName}.json`;
    const cleanId = filename.replace(/\.json$/i, '');

    const existing = allProblems.find(
      (p) => p.id === cleanId || p.rawJsonFilename === filename
    );
    if (existing) {
      handleSelectProblem(existing.id, existing);
      setStatusToast(`已切换至题库内置题目 ${filename}`);
      return;
    }

    setIsFetchingGithub(true);
    try {
      let resp = await fetch(`/tsumego/${filename}`);
      if (!resp.ok) {
        resp = await fetch(
          `https://raw.githubusercontent.com/rlglab/study-LD-RZ/main/tsumego/${filename}`
        );
      }
      if (!resp.ok) {
        throw new Error(`HTTP ${resp.status}`);
      }
      const rawJson = (await resp.json()) as RawStudyLdRzProblemJson;
      const contractCheck = validateStudyLdRzContract(rawJson, 'strict');
      if (!contractCheck.valid) {
        throw new Error(`${contractCheck.code} — ${contractCheck.summary}`);
      }
      const spec = parseStudyLdRzJsonToProblemSpec(filename, rawJson);
      setCustomProblems((prev) => [
        spec,
        ...prev.filter((p) => p.id !== spec.id),
      ]);
      handleSelectProblem(spec.id, spec);
      setStatusToast(
        `已通过 FR-1 契约校验 (${contractCheck.code}) 并载入 ${filename}（关键子: ${
          spec.winningColor === 'B'
            ? spec.blackCrucialStone
            : spec.whiteCrucialStone
        }，Region: ${spec.regionCoords.length} 点）`
      );
    } catch (err) {
      setStatusToast(
        `抓取或契约校验 ${filename} 失败 (${
          err instanceof Error ? err.message : '网络错误'
        })`
      );
    } finally {
      setIsFetchingGithub(false);
    }
  };

  const handleBoardClick = (coord: number) => {
    const nextPos = displayedPosition.clone();
    const res = nextPos.playMove(coord);
    if (!res.legal) {
      setStatusToast(
        `非法落子 ${coordToHumanLabel(
          coord,
          19
        )}：违反禁自杀、简单劫或 SSK 全局同形禁着 (FR-2.1/FR-2.2)`
      );
      return;
    }
    const baseMoves =
      manualMoves.length > 0 && !solveManualSubposition
        ? manualMoves
        : solveManualSubposition
        ? [
            ...manualMoves,
            ...(pvStepIndex !== null && pvStepIndex >= 0
              ? activePvSequence.slice(0, pvStepIndex + 1).map((s) => s.move)
              : []),
          ]
        : pvStepIndex !== null && pvStepIndex >= 0
        ? activePvSequence.slice(0, pvStepIndex + 1).map((s) => s.move)
        : [];
    setManualMoves([...baseMoves, coord]);
    setSolveManualSubposition(false);
    setPvStepIndex(null);
    setStatusToast(
      `已手动试下 ${coordToHumanLabel(coord, 19)}${
        res.capturedCoords.length > 0
          ? `（提子 ${res.capturedCoords.length} 颗）`
          : ''
      } — 可继续试下或点击下方「求解当前试下子局面」生成子局面形式化证明`
    );
  };

  const handlePlayPass = () => {
    handleBoardClick(PASS_MOVE);
  };

  const handleRunFullBenchmark = () => {
    const checker = new ProofArtifactManager();
    const results = allProblems.map((prob) => {
      const cfg: SolverConfig = {
        ...solverConfig,
        attackerAllowKo: Boolean(prob.attackerAllowKo ?? prob.defaultAllowKo),
        defenderAllowKo: prob.defenderAllowKo ?? true,
        useProblemDefaultKo: true,
      };
      const solver = new DfpnSolver(cfg);
      const rep = solver.solveProblem(prob);
      const ctx = DfpnSolver.buildProofContext(prob, cfg);
      const initPos = DfpnSolver.buildInitialPosition(prob, ctx);
      const ver = checker.verifyProofDag(initPos, ctx, rep);
      return { problem: prob, report: rep, verification: ver };
    });
    setBatchReports(results);
    setActiveTab('benchmark');
  };

  const handleCopyText = (label: string, text: string) => {
    navigator.clipboard.writeText(text);
    setCopiedFeedback(label);
    setTimeout(() => setCopiedFeedback(null), 1800);
  };

  const handleDownloadFile = (
    filename: string,
    content: string,
    mime = 'application/json'
  ) => {
    const blob = new Blob([content], { type: mime });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = filename;
    a.click();
    URL.revokeObjectURL(url);
  };

  const filteredProblems = useMemo(() => {
    const q = problemFilterText.trim().toLowerCase();
    return allProblems.filter((p) => {
      if (
        datasetGroupFilter !== 'all' &&
        (p.datasetGroup ?? 'srs-benchmark') !== datasetGroupFilter
      ) {
        return false;
      }
      if (!q) return true;
      return (
        p.title.toLowerCase().includes(q) ||
        p.subtitle.toLowerCase().includes(q) ||
        p.id.toLowerCase().includes(q)
      );
    });
  }, [allProblems, problemFilterText, datasetGroupFilter]);


  const currentCppFile = useMemo(
    () =>
      CPP_SOURCE_FILES.find((f) => f.path === selectedCppPath) ??
      CPP_SOURCE_FILES[0],
    [selectedCppPath]
  );

  // FR-1.1..1.3 Real Contract Validator execution via `validateStudyLdRzContract`
  const contractTestResult = useMemo(() => {
    let samplePayload: RawStudyLdRzProblemJson;
    if (contractPreset === 'valid') {
      samplePayload = {
        masked_sgf_str: currentProblem.maskedSgfStr,
        winning_color: currentProblem.winningColor,
        turn_color: currentProblem.turnColor,
        black_search_goal: currentProblem.blackSearchGoal,
        white_search_goal: currentProblem.whiteSearchGoal,
        black_crucial_stone: currentProblem.blackCrucialStone,
        white_crucial_stone: currentProblem.whiteCrucialStone,
        answer_firstmove: currentProblem.groundTruthFirstMoves ?? [],
      };
    } else if (contractPreset === 'turn-conflict') {
      samplePayload = {
        masked_sgf_str: '(;GM[1]FF[4]SZ[19]PL[B]AB[da][ab][bb]AW[ea][eb])',
        winning_color: 'B',
        turn_color: 'W',
        black_search_goal: 'TOLIVE',
        white_search_goal: 'TOKILL',
        black_crucial_stone: 'bb',
        white_crucial_stone: 'ea',
        answer_firstmove: 'ca',
      };
    } else if (contractPreset === 'mixed-op') {
      samplePayload = {
        masked_sgf_str: '(;GM[1]FF[4]SZ[19]PL[B]AB[ab][cb][db]AW[ea][eb])',
        winning_color: 'B',
        turn_color: 'B',
        black_search_goal: 'TOLIVE',
        white_search_goal: 'TOKILL',
        black_crucial_stone: 'ab&cb|db',
        white_crucial_stone: 'ea',
        answer_firstmove: 'ca',
      };
    } else if (contractPreset === 'missing-crucial') {
      samplePayload = {
        masked_sgf_str: '(;GM[1]FF[4]SZ[19]PL[B]AB[da][ab][bb]AW[ea][eb])',
        winning_color: 'B',
        turn_color: 'B',
        black_search_goal: 'TOLIVE',
        white_search_goal: 'TOKILL',
        black_crucial_stone: 'ss',
        white_crucial_stone: 'ea',
        answer_firstmove: 'ca',
      };
    } else {
      samplePayload = {
        masked_sgf_str: '(;GM[1]FF[4]SZ[19]PL[B]AB[da][ab][bb]AW[ea][eb])',
        winning_color: 'B',
        turn_color: 'B',
        black_search_goal: 'TOLIVE',
        white_search_goal: 'TOKILL',
        black_crucial_stone: '',
        white_crucial_stone: 'ea',
        answer_firstmove: 'ca',
      };
    }

    const res = validateStudyLdRzContract(samplePayload, 'strict');
    return {
      valid: res.valid,
      warning: res.warning,
      code: res.code,
      summary: res.summary,
      jsonSample: JSON.stringify(samplePayload, null, 2),
    };
  }, [contractPreset, currentProblem]);

  return (
    <div className="min-h-screen bg-slate-50 text-slate-900 flex flex-col">
      {/* Strict 3-Zone Top Bar Contract (§2) */}
      <header className="sticky top-0 z-30 flex items-center justify-between gap-8 border-b border-slate-200 bg-white px-6 py-3.5">
        {/* Zone 1: Single text element wordmark */}
        <a
          href="#top"
          onClick={(e) => {
            e.preventDefault();
            setActiveTab('workbench');
          }}
          className="text-lg font-bold tracking-tight text-slate-900 whitespace-nowrap shrink-0"
        >
          LDProver
        </a>

        {/* Zone 2: 5 concise single-line text navigation links */}
        <nav className="hidden md:flex items-center gap-6 text-sm font-medium text-slate-600">
          <button
            type="button"
            onClick={() => setActiveTab('workbench')}
            className={`py-1 transition-colors whitespace-nowrap shrink-0 border-b-2 ${
              activeTab === 'workbench'
                ? 'border-slate-900 text-slate-900 font-semibold'
                : 'border-transparent hover:text-slate-900'
            }`}
          >
            求解工作台
          </button>
          <button
            type="button"
            onClick={() => setActiveTab('proof-dag')}
            className={`py-1 transition-colors whitespace-nowrap shrink-0 border-b-2 ${
              activeTab === 'proof-dag'
                ? 'border-slate-900 text-slate-900 font-semibold'
                : 'border-transparent hover:text-slate-900'
            }`}
          >
            证明树与 SGF
          </button>
          <button
            type="button"
            onClick={() => setActiveTab('checker')}
            className={`py-1 transition-colors whitespace-nowrap shrink-0 border-b-2 ${
              activeTab === 'checker'
                ? 'border-slate-900 text-slate-900 font-semibold'
                : 'border-transparent hover:text-slate-900'
            }`}
          >
            独立校验器 (lproof/1)
          </button>
          <button
            type="button"
            onClick={() => setActiveTab('cpp-source')}
            className={`py-1 transition-colors whitespace-nowrap shrink-0 border-b-2 ${
              activeTab === 'cpp-source'
                ? 'border-slate-900 text-slate-900 font-semibold'
                : 'border-transparent hover:text-slate-900'
            }`}
          >
            C++20 源码架构
          </button>
          <button
            type="button"
            onClick={() => setActiveTab('benchmark')}
            className={`py-1 transition-colors whitespace-nowrap shrink-0 border-b-2 ${
              activeTab === 'benchmark'
                ? 'border-slate-900 text-slate-900 font-semibold'
                : 'border-transparent hover:text-slate-900'
            }`}
          >
            批量基准与契约
          </button>
        </nav>

        {/* Zone 3: 1 primary action */}
        <div className="flex items-center shrink-0">
          <button
            type="button"
            onClick={handleRunFullBenchmark}
            className="px-4 py-2 text-xs font-semibold text-white bg-slate-900 rounded-md hover:bg-slate-800 transition-colors whitespace-nowrap shrink-0 cursor-pointer"
          >
            运行全量基准测试
          </button>
        </div>
      </header>

      {/* Mobile Navigation Bar */}
      <div className="flex md:hidden items-center gap-2 overflow-x-auto border-b border-slate-200 bg-white px-4 py-2">
        {(
          [
            ['workbench', '求解工作台'],
            ['proof-dag', '证明树与 SGF'],
            ['checker', '独立校验器'],
            ['cpp-source', 'C++20 源码'],
            ['benchmark', '批量基准'],
          ] as const
        ).map(([key, label]) => (
          <button
            key={key}
            type="button"
            onClick={() => setActiveTab(key)}
            className={`px-3 py-1.5 text-xs font-medium rounded-md whitespace-nowrap shrink-0 ${
              activeTab === key
                ? 'bg-slate-900 text-white'
                : 'text-slate-600 hover:bg-slate-100'
            }`}
          >
            {label}
          </button>
        ))}
      </div>

      {/* Subheader Context Bar (Unboxed metadata per Zero-Pill rule) */}
      <div className="border-b border-slate-200 bg-white px-6 py-3">
        <div className="mx-auto flex max-w-[1440px] flex-wrap items-center justify-between gap-4">
          <div>
            <h1 className="text-base font-semibold text-slate-900">
              C++20 围棋死活精确求解器与形式化证明系统（SRS v1.8 / 设计 v1.9）
            </h1>
            <div className="mt-0.5 flex flex-wrap items-center gap-2 text-xs text-slate-500">
              <span>Google C++ 编码规范</span>
              <span aria-hidden="true">·</span>
              <span>1+ε df-pn 启发式对偶搜索</span>
              <span aria-hidden="true">·</span>
              <span>经典 Benson (1976) UCA 零误判算子</span>
              <span aria-hidden="true">·</span>
              <span>全覆盖 ProofCertificateRZ 重放剪枝</span>
              <span aria-hidden="true">·</span>
              <span>D8 自动对齐真实 study-LD-RZ 题库</span>
              <span aria-hidden="true">·</span>
              <span>lproof/1 叶节点独立终局校验</span>
            </div>
          </div>

          <div className="flex items-center gap-4 text-xs font-mono tabular-nums text-slate-600">
            <span>
              当前结论：
              <strong
                className={
                  solveReport.rootStatus === ProofOutcome.ProvenWin
                    ? 'text-emerald-700'
                    : solveReport.rootStatus === ProofOutcome.ProvenLoss
                    ? 'text-amber-700'
                    : 'text-slate-800'
                }
              >
                {solveReport.rootStatus}
                {solveReport.unknownReason
                  ? ` (${solveReport.unknownReason})`
                  : ''}
              </strong>
            </span>
            <span aria-hidden="true">/</span>
            <span>
              胜着急所：
              <strong className="text-slate-900">
                {coordToHumanLabel(solveReport.bestMove, 19)}
              </strong>
            </span>
            <span aria-hidden="true">/</span>
            <span>
              Checker：
              <strong
                className={
                  verificationReport.passed
                    ? 'text-emerald-700'
                    : 'text-red-700'
                }
              >
                {verificationReport.errorCode}
              </strong>
            </span>
          </div>
        </div>
      </div>

      {/* Main Content Container */}
      <main className="mx-auto w-full max-w-[1440px] flex-1 px-6 py-6">
        {/* TAB 1: WORKBENCH */}
        {activeTab === 'workbench' && (
          <div className="grid grid-cols-1 gap-6 lg:grid-cols-12 items-start">
            {/* Left Column: Problem Selector & GitHub study-LD-RZ Importer (3 cols) */}
            <aside className="lg:col-span-3 border border-slate-200 bg-white rounded-lg p-4">
              <div className="flex items-center justify-between pb-3 border-b border-slate-200">
                <h2 className="text-sm font-semibold text-slate-900">
                  死活题库 (study-LD-RZ & SRS)
                </h2>
                <span className="text-xs font-mono tabular-nums text-slate-500">
                  {filteredProblems.length} / {allProblems.length} 题
                </span>
              </div>

              {/* Dataset Category Segmented Filter */}
              <div className="mt-3 grid grid-cols-3 gap-1 rounded-md bg-slate-100 p-1 text-[11px] font-medium">
                {(
                  [
                    ['all', '全部题目'],
                    ['study-ld-rz', 'study-LD-RZ'],
                    ['srs-benchmark', 'SRS 基准'],
                  ] as const
                ).map(([grp, label]) => (
                  <button
                    key={grp}
                    type="button"
                    onClick={() => setDatasetGroupFilter(grp)}
                    className={`py-1 rounded-xs transition-colors cursor-pointer whitespace-nowrap ${
                      datasetGroupFilter === grp
                        ? 'bg-white text-slate-900 font-semibold shadow-2xs'
                        : 'text-slate-600 hover:text-slate-900'
                    }`}
                  >
                    {label}
                  </button>
                ))}
              </div>

              {/* Live GitHub rlglab/study-LD-RZ Problem Loader */}
              <div className="mt-3 rounded-md border border-slate-200 bg-slate-50 p-2.5">
                <div className="text-[11px] font-semibold text-slate-800">
                  从 rlglab/study-LD-RZ 抓取题目：
                </div>
                <div className="mt-1.5 flex items-center gap-1.5">
                  <select
                    value={githubFilenameInput}
                    onChange={(e) => {
                      setGithubFilenameInput(e.target.value);
                      handleFetchGithubProblem(e.target.value);
                    }}
                    className="min-w-0 flex-1 rounded border border-slate-300 bg-white px-2 py-1 text-xs font-mono text-slate-900 focus:border-slate-900 focus:outline-none"
                  >
                    {AVAILABLE_GITHUB_STUDY_LD_RZ_FILES.map((fn) => (
                      <option key={fn} value={fn}>
                        {fn}
                      </option>
                    ))}
                  </select>
                  <button
                    type="button"
                    disabled={isFetchingGithub}
                    onClick={() => handleFetchGithubProblem()}
                    className="rounded bg-slate-900 px-2.5 py-1 text-xs font-medium text-white hover:bg-slate-800 disabled:opacity-50 cursor-pointer whitespace-nowrap shrink-0"
                  >
                    {isFetchingGithub ? '加载中' : '载入'}
                  </button>
                </div>
              </div>

              <div className="mt-3">
                <input
                  type="text"
                  value={problemFilterText}
                  onChange={(e) => setProblemFilterText(e.target.value)}
                  placeholder="搜索 chao_vol1、手筋类型或题号..."
                  className="w-full rounded-md border border-slate-300 bg-slate-50 px-3 py-1.5 text-xs text-slate-900 placeholder:text-slate-400 focus:border-slate-900 focus:bg-white focus:outline-none"
                />
              </div>

              <div className="mt-3 max-h-[620px] overflow-y-auto divide-y divide-slate-200 pr-0.5">
                {filteredProblems.map((prob) => {
                  const isSelected = prob.id === currentProblem.id;
                  const isDiagnostic = Boolean(prob.failureDiagnosis);
                  return (
                    <button
                      key={prob.id}
                      type="button"
                      onClick={() => handleSelectProblem(prob.id)}
                      className={`w-full py-3 text-left transition-colors cursor-pointer ${
                        isSelected
                          ? 'bg-slate-900/5 px-2.5 rounded-md'
                          : 'hover:bg-slate-50 px-1.5'
                      }`}
                    >
                      <div className="flex items-center justify-between gap-2">
                        <span className="text-xs font-semibold text-slate-900 truncate">
                          {prob.title}
                        </span>
                        <span
                          className={`text-[10px] font-mono font-semibold shrink-0 ${
                            isDiagnostic
                              ? 'text-amber-700'
                              : prob.expectedOutcome === ProofOutcome.ProvenWin
                              ? 'text-emerald-700'
                              : 'text-slate-600'
                          }`}
                        >
                          {isDiagnostic
                            ? '失败诊断'
                            : prob.expectedOutcome === ProofOutcome.ProvenWin
                            ? 'PROVEN'
                            : prob.expectedOutcome}
                        </span>
                      </div>
                      <div className="mt-1 text-[11px] text-slate-600 line-clamp-2">
                        {prob.subtitle}
                      </div>
                      <div className="mt-1.5 flex items-center gap-1.5 text-[11px] font-mono tabular-nums text-slate-500">
                        <span>PL[{prob.turnColor}]</span>
                        <span aria-hidden="true">·</span>
                        <span>
                          {prob.winningColor === 'B'
                            ? prob.blackSearchGoal
                            : prob.whiteSearchGoal}
                        </span>
                        <span aria-hidden="true">·</span>
                        <span className="truncate">
                          关键子:{' '}
                          {prob.winningColor === 'B'
                            ? prob.blackCrucialStone
                            : prob.whiteCrucialStone}
                        </span>
                      </div>
                    </button>
                  );
                })}
              </div>
            </aside>

            {/* Center Column: Interactive Go Board & PV Stepper (5 cols) */}
            <section className="lg:col-span-5 border border-slate-200 bg-white rounded-lg p-5">
              <div className="flex flex-wrap items-center justify-between gap-2 pb-4 border-b border-slate-200">
                <div>
                  <h2 className="text-base font-semibold text-slate-900">
                    {currentProblem.title}
                  </h2>
                  <div className="mt-0.5 flex flex-wrap items-center gap-2 text-xs text-slate-500">
                    <span>{currentProblem.source}</span>
                    <span aria-hidden="true">·</span>
                    <span>{currentProblem.difficulty}</span>
                  </div>
                </div>

                {/* Viewport Toggle */}
                <div className="flex items-center gap-1 rounded-md bg-slate-100 p-1">
                  <button
                    type="button"
                    onClick={() => setShowFullBoard(false)}
                    className={`px-2.5 py-1 text-xs font-medium rounded-xs transition-colors whitespace-nowrap shrink-0 cursor-pointer ${
                      !showFullBoard
                        ? 'bg-white text-slate-900 shadow-2xs'
                        : 'text-slate-600 hover:text-slate-900'
                    }`}
                  >
                    局部死活视窗
                  </button>
                  <button
                    type="button"
                    onClick={() => setShowFullBoard(true)}
                    className={`px-2.5 py-1 text-xs font-medium rounded-xs transition-colors whitespace-nowrap shrink-0 cursor-pointer ${
                      showFullBoard
                        ? 'bg-white text-slate-900 shadow-2xs'
                        : 'text-slate-600 hover:text-slate-900'
                    }`}
                  >
                    19×19 全盘
                  </button>
                </div>
              </div>

              {/* Ground-Truth Comparison Banner for study-LD-RZ problems (strictly gated on verificationReport.passed && manualMoves.length === 0) */}
              {currentProblem.groundTruthFirstMoves &&
                currentProblem.groundTruthFirstMoves.length > 0 && (
                  <div className="mt-3 space-y-1.5 rounded-md border border-slate-200 bg-slate-50 px-3 py-2 text-xs font-mono tabular-nums">
                    <div className="flex flex-wrap items-center justify-between gap-2">
                      <div>
                        <span className="text-slate-500">
                          {solveManualSubposition && manualMoves.length > 0
                            ? '子局面最佳应手：'
                            : '引擎首手：'}
                        </span>
                        <strong className="text-slate-900">
                          {solveReport.bestMoveSgf
                            ? `${solveReport.bestMoveSgf} (${coordToHumanLabel(
                                solveReport.bestMove,
                                19
                              )})`
                            : '无'}
                        </strong>
                      </div>
                      <div>
                        <span className="text-slate-500">
                          JSON answer_firstmove：
                        </span>
                        <strong className="text-slate-900">
                          {currentProblem.groundTruthFirstMoves.join(', ')}
                        </strong>
                      </div>
                      {currentProblem.verifiedGroundTruthFirstMoves &&
                        currentProblem.verifiedGroundTruthFirstMoves.length >
                          0 && (
                          <div>
                            <span className="text-slate-500">
                              rawsgf D8 核验真解：
                            </span>
                            <strong className="text-emerald-800">
                              {currentProblem.verifiedGroundTruthFirstMoves.join(
                                ', '
                              )}
                            </strong>
                          </div>
                        )}
                      <div>
                        {manualMoves.length > 0 ? (
                          solveManualSubposition ? (
                            <span className="font-sans font-semibold text-indigo-700">
                              试下子局面 ({manualMoves.length} 手) 独立证明 · Checker:{' '}
                              {verificationReport.errorCode}
                            </span>
                          ) : (
                            <span className="font-sans font-semibold text-amber-800">
                              手动试下探索态 ({manualMoves.length} 手) · 非初始根局面
                            </span>
                          )
                        ) : (solveReport.rootStatus ===
                            ProofOutcome.ProvenWin ||
                            solveReport.rootStatus ===
                              ProofOutcome.ProvenLoss) &&
                          !verificationReport.passed ? (
                          <span className="font-sans font-semibold text-red-700">
                            独立 Checker 拦截 ({verificationReport.errorCode}) · 证明无效
                          </span>
                        ) : verificationReport.passed &&
                          solveReport.rootStatus === ProofOutcome.ProvenWin &&
                          solveReport.bestMoveSgf &&
                          (currentProblem.verifiedGroundTruthFirstMoves ??
                            currentProblem.groundTruthFirstMoves
                          ).includes(solveReport.bestMoveSgf) ? (
                          <span className="font-sans font-semibold text-emerald-700">
                            形式化证明通过 · 与原谱真解一致
                          </span>
                        ) : (
                          <span className="font-sans font-semibold text-amber-700">
                            可切换下方「原谱参考正解」回放
                          </span>
                        )}
                      </div>
                    </div>
                    {currentProblem.groundTruthNote && (
                      <div className="border-t border-slate-200 pt-1 font-sans text-[11px] font-medium text-amber-800">
                        数据集勘误：{currentProblem.groundTruthNote}
                      </div>
                    )}
                    {currentProblem.d8SymmetryAudit &&
                      !currentProblem.d8SymmetryAudit.isExactBijection && (
                        <div className="border-t border-slate-200 pt-1 font-sans text-[11px] text-slate-700">
                          D8 原谱棋子核对（D8=#{
                            currentProblem.d8SymmetryAudit.d8Index
                          }）：原谱局部匹配{' '}
                          {currentProblem.d8SymmetryAudit.matchedStones}/
                          {currentProblem.d8SymmetryAudit.totalRawStones} 子
                          {currentProblem.d8SymmetryAudit.missingInMaskedSgf
                            .length > 0
                            ? `；masked_sgf 缺失 [${currentProblem.d8SymmetryAudit.missingInMaskedSgf.join(
                                ', '
                              )}]`
                            : ''}
                          {currentProblem.d8SymmetryAudit.extraInMaskedRegion
                            .length > 0
                            ? `；region 内多出 [${currentProblem.d8SymmetryAudit.extraInMaskedRegion.join(
                                ', '
                              )}]`
                            : ''}
                        </div>
                      )}
                  </div>
                )}

              {/* Overlay Mode Segmented Control */}
              <div className="mt-3 flex flex-wrap items-center justify-between gap-2">
                <span className="text-xs font-medium text-slate-600">
                  空间图层渲染：
                </span>
                <div className="flex items-center gap-1 rounded-md bg-slate-100 p-1">
                  {(
                    [
                      ['proof-rz', '证明 RZ (绿)'],
                      ['disproof-rz', '反证 RZ (黄)'],
                      ['benson-uca', 'Benson & 眼位拓扑'],
                      ['none', '纯净棋盘'],
                    ] as const
                  ).map(([mode, label]) => (
                    <button
                      key={mode}
                      type="button"
                      onClick={() => setOverlayMode(mode)}
                      className={`px-2.5 py-1 text-xs font-medium rounded-xs transition-colors whitespace-nowrap shrink-0 cursor-pointer ${
                        overlayMode === mode
                          ? 'bg-white text-slate-900 shadow-2xs'
                          : 'text-slate-600 hover:text-slate-900'
                      }`}
                    >
                      {label}
                    </button>
                  ))}
                </div>
              </div>

              {/* SVG Board */}
              <div className="mt-4">
                <TsumegoBoardView
                  position={displayedPosition}
                  context={proofContext}
                  report={solveReport}
                  viewportRows={currentProblem.viewportRows}
                  viewportCols={currentProblem.viewportCols}
                  showFullBoard={showFullBoard}
                  overlayMode={overlayMode}
                  selectedPvStepIndex={pvStepIndex}
                  onPlayCoord={handleBoardClick}
                />
              </div>

              {statusToast && (
                <div className="mt-3 rounded-md border border-slate-200 bg-slate-50 px-3 py-2 text-xs font-mono text-slate-700">
                  {statusToast}
                </div>
              )}

              {/* Principal Variation & Interactive Controls */}
              <div className="mt-4 pt-4 border-t border-slate-200">
                <div className="flex flex-wrap items-center justify-between gap-2">
                  <div className="text-xs font-medium text-slate-700">
                    轮走方：
                    <strong className="font-mono">
                      {displayedPosition.toPlay === Color.Black
                        ? '黑先 (Black)'
                        : '白先 (White)'}
                    </strong>
                    <span className="mx-2 text-slate-300">|</span>
                    当前状态：
                    <strong className="font-mono text-slate-900">
                      {liveTerminalEval.status} ({liveTerminalEval.evidenceKind})
                    </strong>
                  </div>

                   <div className="flex flex-wrap items-center gap-1.5">
                    <button
                      type="button"
                      onClick={() => {
                        setManualMoves([]);
                        setSolveManualSubposition(false);
                        setPvStepIndex(-1);
                        setStatusToast(null);
                      }}
                      title="回到初始题面"
                      className="inline-flex items-center gap-1 rounded-md border border-slate-300 bg-white px-2.5 py-1.5 text-xs font-medium text-slate-700 hover:bg-slate-50 cursor-pointer whitespace-nowrap shrink-0"
                    >
                      <SkipBack className="h-3.5 w-3.5" />
                      初始
                    </button>
                    <button
                      type="button"
                      onClick={() => {
                        setManualMoves([]);
                        setSolveManualSubposition(false);
                        setPvStepIndex((prev) =>
                          prev === null
                            ? activePvSequence.length - 2
                            : Math.max(-1, prev - 1)
                        );
                      }}
                      title="上一步"
                      className="inline-flex items-center gap-1 rounded-md border border-slate-300 bg-white px-2.5 py-1.5 text-xs font-medium text-slate-700 hover:bg-slate-50 cursor-pointer whitespace-nowrap shrink-0"
                    >
                      <StepBack className="h-3.5 w-3.5" />
                      退一步
                    </button>
                    <button
                      type="button"
                      onClick={() => {
                        setManualMoves([]);
                        setSolveManualSubposition(false);
                        setPvStepIndex((prev) => {
                          const cur = prev === null ? -1 : prev;
                          return Math.min(
                            activePvSequence.length - 1,
                            cur + 1
                          );
                        });
                      }}
                      title="下一步正解"
                      className="inline-flex items-center gap-1 rounded-md border border-slate-900 bg-slate-900 px-3 py-1.5 text-xs font-medium text-white hover:bg-slate-800 cursor-pointer whitespace-nowrap shrink-0"
                    >
                      <StepForward className="h-3.5 w-3.5" />
                      {solveReport.principalVariation.length === 0 ||
                      pvSourceMode === 'reference'
                        ? '演进原谱正解'
                        : '演进正解'}
                    </button>
                    <button
                      type="button"
                      onClick={() => {
                        setManualMoves([]);
                        setSolveManualSubposition(false);
                        setPvStepIndex(activePvSequence.length - 1);
                      }}
                      title="跳至终局叶节点"
                      className="inline-flex items-center gap-1 rounded-md border border-slate-300 bg-white px-2.5 py-1.5 text-xs font-medium text-slate-700 hover:bg-slate-50 cursor-pointer whitespace-nowrap shrink-0"
                    >
                      <SkipForward className="h-3.5 w-3.5" />
                      终局
                    </button>
                    <button
                      type="button"
                      onClick={handlePlayPass}
                      className="inline-flex items-center gap-1 rounded-md border border-slate-300 bg-white px-2.5 py-1.5 text-xs font-medium text-slate-700 hover:bg-slate-50 cursor-pointer whitespace-nowrap shrink-0"
                    >
                      虚手 Pass
                    </button>
                    {manualMoves.length > 0 && !solveManualSubposition && (
                      <button
                        type="button"
                        onClick={() => {
                          setSolveManualSubposition(true);
                          setPvStepIndex(null);
                          setStatusToast(
                            `已对当前试下子局面 (${manualMoves.length} 手后，保留真实 HistorySet 与存活令牌掩码) 执行独立 df-pn 求解与 ProofChecker 复验`
                          );
                        }}
                        className="inline-flex items-center gap-1 rounded-md border border-indigo-600 bg-indigo-600 px-2.5 py-1.5 text-xs font-medium text-white hover:bg-indigo-700 cursor-pointer whitespace-nowrap shrink-0"
                      >
                        <Play className="h-3.5 w-3.5" />
                        求解当前试下子局面
                      </button>
                    )}
                    {manualMoves.length > 0 && (
                      <button
                        type="button"
                        onClick={() => {
                          setManualMoves([]);
                          setSolveManualSubposition(false);
                          setPvStepIndex(null);
                          setStatusToast(null);
                        }}
                        className="inline-flex items-center gap-1 rounded-md border border-amber-300 bg-amber-50 px-2.5 py-1.5 text-xs font-medium text-amber-900 hover:bg-amber-100 cursor-pointer whitespace-nowrap shrink-0"
                      >
                        <RotateCcw className="h-3.5 w-3.5" />
                        清除试下
                      </button>
                    )}
                  </div>
                </div>

                {/* Problem Analysis Prose */}
                <p className="mt-3 text-xs leading-relaxed text-slate-600">
                  {currentProblem.description}
                </p>

                {/* Principal Variation Path List with Engine vs Reference SGF Toggle */}
                <div className="mt-3 pt-3 border-t border-slate-100">
                  <div className="flex flex-wrap items-center justify-between gap-2">
                    <div className="text-xs font-semibold text-slate-900">
                      解题路径回放 ({activePvSequence.length} 手)：
                    </div>

                    {currentProblem.referencePv &&
                      currentProblem.referencePv.length > 0 && (
                        <div className="flex items-center gap-1 rounded-md bg-slate-100 p-0.5 text-[11px]">
                          <button
                            type="button"
                            onClick={() => {
                              setPvSourceMode('engine');
                              setPvStepIndex(null);
                            }}
                            className={`px-2 py-0.5 rounded-xs cursor-pointer ${
                              pvSourceMode === 'engine' &&
                              solveReport.principalVariation.length > 0
                                ? 'bg-white text-slate-900 font-semibold shadow-2xs'
                                : 'text-slate-600'
                            }`}
                          >
                            LDProver 证明主变 ({solveReport.principalVariation.length})
                          </button>
                          <button
                            type="button"
                            onClick={() => {
                              setPvSourceMode('reference');
                              setPvStepIndex(0);
                            }}
                            className={`px-2 py-0.5 rounded-xs cursor-pointer ${
                              pvSourceMode === 'reference' ||
                              solveReport.principalVariation.length === 0
                                ? 'bg-white text-slate-900 font-semibold shadow-2xs'
                                : 'text-slate-600'
                            }`}
                          >
                            题库 rawsgf 原谱正解 ({currentProblem.referencePv.length})
                          </button>
                        </div>
                      )}
                  </div>

                  {activePvSequence.length === 0 ? (
                    <div className="mt-1.5 text-xs text-slate-500 font-mono">
                      当前根命题状态为 {solveReport.rootStatus}{' '}
                      {solveReport.unknownReason
                        ? `(${solveReport.unknownReason}) — 请在右侧开启 allow_ko 查看劫胜路径`
                        : ''}
                    </div>
                  ) : (
                    <div className="mt-2 space-y-1.5">
                      {activePvSequence.map((step, idx) => (
                        <div
                          key={`pv-${idx}`}
                          onClick={() => {
                            if (!solveManualSubposition) {
                              setManualMoves([]);
                            }
                            setPvStepIndex(idx);
                          }}
                          className={`flex items-center justify-between rounded-md px-2.5 py-1.5 text-xs font-mono cursor-pointer transition-colors ${
                            pvStepIndex === idx
                              ? 'bg-slate-900 text-white'
                              : 'bg-slate-50 text-slate-800 hover:bg-slate-100'
                          }`}
                        >
                          <span>
                            #{idx + 1} · {step.comment}
                          </span>
                          <span className="text-[11px] opacity-80">
                            点击定位
                          </span>
                        </div>
                      ))}
                    </div>
                  )}
                </div>
              </div>
            </section>

            {/* Right Column: Solver Config, Failure Diagnosis & Telemetry Readout (4 cols) */}
            <aside className="lg:col-span-4 space-y-6">
              {/* Failure Diagnosis & C++20 Improvement Card (shown when viewing an UNKNOWN diagnostic problem) */}
              {currentProblem.failureDiagnosis && (
                <div className="border border-amber-300 bg-amber-50/60 rounded-lg p-5">
                  <div className="flex items-center justify-between pb-2.5 border-b border-amber-200">
                    <h2 className="text-sm font-semibold text-amber-950">
                      解答失败根因诊断与 C++20 改进方案
                    </h2>
                    <span className="text-[11px] font-mono font-semibold text-amber-800">
                      {currentProblem.failureDiagnosis.estimatedSpeedup}
                    </span>
                  </div>

                  <dl className="mt-3 space-y-2.5 text-xs">
                    <div>
                      <dt className="font-semibold text-amber-950">
                        瓶颈分类 (Failure Taxonomy)
                      </dt>
                      <dd className="mt-0.5 font-mono text-amber-900">
                        {currentProblem.failureDiagnosis.category}
                      </dd>
                    </div>
                    <div>
                      <dt className="font-semibold text-amber-950">
                        技术根因剖析 (Root Cause)
                      </dt>
                      <dd className="mt-0.5 leading-relaxed text-amber-900">
                        {currentProblem.failureDiagnosis.rootCause}
                      </dd>
                    </div>
                    <div>
                      <dt className="font-semibold text-amber-950">
                        后续算法改进方案 (Algorithmic Upgrade)
                      </dt>
                      <dd className="mt-0.5 leading-relaxed text-slate-800 bg-white/80 rounded border border-amber-200 p-2.5">
                        {currentProblem.failureDiagnosis.improvementMethod}
                      </dd>
                    </div>
                    <div className="pt-1 flex items-center justify-between text-[11px] font-mono text-amber-900">
                      <span>目标改造模块：</span>
                      <strong>
                        {currentProblem.failureDiagnosis.targetCppModule}
                      </strong>
                    </div>
                  </dl>
                </div>
              )}

              {/* Engine Result Summary Panel */}
              <div className="border border-slate-200 bg-white rounded-lg p-5">
                <div className="flex items-center justify-between pb-3 border-b border-slate-200">
                  <h2 className="text-sm font-semibold text-slate-900">
                    LDProver 求解定论与证明摘要
                  </h2>
                  <span className="text-xs font-mono tabular-nums text-slate-500">
                    {solveReport.timeMs} ms · {solveReport.numNodes} nodes
                  </span>
                </div>

                <dl className="mt-3 grid grid-cols-2 gap-x-4 gap-y-3 text-xs">
                  <div>
                    <dt className="text-slate-500">根命题定论 (RootStatus)</dt>
                    <dd
                      className={`mt-0.5 font-mono text-sm font-bold tabular-nums ${
                        solveReport.rootStatus === ProofOutcome.ProvenWin
                          ? 'text-emerald-700'
                          : solveReport.rootStatus === ProofOutcome.ProvenLoss
                          ? 'text-amber-700'
                          : 'text-slate-900'
                      }`}
                    >
                      {solveReport.rootStatus}
                    </dd>
                  </div>

                  <div>
                    <dt className="text-slate-500">最佳应手 (BestMove)</dt>
                    <dd className="mt-0.5 font-mono text-sm font-bold text-slate-900 tabular-nums">
                      {coordToHumanLabel(solveReport.bestMove, 19)}
                    </dd>
                  </div>

                  <div>
                    <dt className="text-slate-500">RootPn / RootDn (§4.1)</dt>
                    <dd className="mt-0.5 font-mono text-xs font-semibold text-slate-900 tabular-nums">
                      PN=
                      {solveReport.rootPn >= PN_DN_SATURATION
                        ? 'SAT'
                        : solveReport.rootPn}{' '}
                      / DN=
                      {solveReport.rootDn >= PN_DN_SATURATION
                        ? 'SAT'
                        : solveReport.rootDn}
                    </dd>
                  </div>

                  <div>
                    <dt className="text-slate-500">UnknownReason (FR-4.8)</dt>
                    <dd className="mt-0.5 font-mono text-xs font-semibold text-slate-800">
                      {solveReport.unknownReason ?? 'null (已定论)'}
                    </dd>
                  </div>

                  <div>
                    <dt className="text-slate-500">根证明区域 (RZSizeAtRoot)</dt>
                    <dd className="mt-0.5 font-mono text-xs font-semibold text-slate-900 tabular-nums">
                      {solveReport.rzSizeAtRoot} 格 / 361 格
                    </dd>
                  </div>

                  <div>
                    <dt className="text-slate-500">RZ 外重放剪枝 (FR-5.5)</dt>
                    <dd className="mt-0.5 font-mono text-xs font-semibold text-emerald-700 tabular-nums">
                      {solveReport.prunedOutsideRzCount} 次 (OutsideRZRevalidated)
                    </dd>
                  </div>

                  <div>
                    <dt className="text-slate-500">BoardTT / PatternTT 命中</dt>
                    <dd className="mt-0.5 font-mono text-xs font-semibold text-slate-900 tabular-nums">
                      {solveReport.boardTtHits} / {solveReport.patternTtHits} (可复用:{' '}
                      {solveReport.patternProofReusableHits})
                    </dd>
                  </div>

                  <div>
                    <dt className="text-slate-500">全称证明域 (Region 全集)</dt>
                    <dd className="mt-0.5 font-mono text-xs font-semibold text-slate-900 tabular-nums">
                      {solveReport.regionCoords.length} /{' '}
                      {solveReport.rawRegionPointCount ??
                        solveReport.regionCoords.length}{' '}
                      点 ({solveReport.isFullRegionSearch ? '100% 原题域' : '裁剪域'})
                    </dd>
                  </div>

                  <div>
                    <dt className="text-slate-500">独立 ProofChecker (FR-9)</dt>
                    <dd
                      className={`mt-0.5 font-mono text-xs font-bold ${
                        verificationReport.passed
                          ? 'text-emerald-700'
                          : 'text-red-700'
                      }`}
                    >
                      {verificationReport.errorCode} ({verificationReport.verifiedNodes} 节点)
                    </dd>
                  </div>
                </dl>

                {/* KataGo semeye & Benson UCA Live Readout */}
                <div className="mt-4 pt-3 border-t border-slate-200">
                  <div className="text-xs font-semibold text-slate-900">
                    Benson UCA 与 KataGo semeye 眼位拓扑诊断：
                  </div>
                  <div className="mt-1.5 space-y-1 text-xs font-mono text-slate-600">
                    <div>
                      Benson UCA 活棋子数：{liveTerminalEval.bensonAliveCoords.length} 颗
                    </div>
                    {liveTerminalEval.eyeTopologyRegions.length === 0 ? (
                      <div>封闭眼位区域：无独立小眼区</div>
                    ) : (
                      liveTerminalEval.eyeTopologyRegions.map((reg) => (
                        <div key={reg.regionId} className="flex items-center justify-between">
                          <span>
                            眼区 #{reg.regionId} ({reg.coords.map((c) => coordToSgf(c, 19)).join(',')})
                          </span>
                          <strong
                            className={
                              reg.topology === 'TRUE_EYE'
                                ? 'text-emerald-700'
                                : reg.topology === 'HALF_EYE'
                                ? 'text-amber-700'
                                : 'text-red-700'
                            }
                          >
                            {reg.topology}
                          </strong>
                        </div>
                      ))
                    )}
                  </div>
                </div>
              </div>


              {/* Engine Configuration Panel */}
              <div className="border border-slate-200 bg-white rounded-lg p-5">
                <h2 className="text-sm font-semibold text-slate-900 pb-3 border-b border-slate-200">
                  C++ 引擎求解参数配置 (SolverConfig)
                </h2>

                <div className="mt-3 space-y-3 text-xs">
                  {/* TT Mode */}
                  <div>
                    <label className="block font-medium text-slate-700">
                      置换表模式 (--mode FR-6.1 / FR-6.3)
                    </label>
                    <div className="mt-1 grid grid-cols-2 gap-1 rounded-md bg-slate-100 p-1">
                      <button
                        type="button"
                        onClick={() =>
                          setSolverConfig((c) => ({ ...c, ttMode: 'pattern-tt' }))
                        }
                        className={`py-1.5 font-mono text-xs rounded-xs cursor-pointer ${
                          solverConfig.ttMode === 'pattern-tt'
                            ? 'bg-white text-slate-900 font-semibold shadow-2xs'
                            : 'text-slate-600'
                        }`}
                      >
                        pattern-tt (RadixTree)
                      </button>
                      <button
                        type="button"
                        onClick={() =>
                          setSolverConfig((c) => ({ ...c, ttMode: 'board-tt' }))
                        }
                        className={`py-1.5 font-mono text-xs rounded-xs cursor-pointer ${
                          solverConfig.ttMode === 'board-tt'
                            ? 'bg-white text-slate-900 font-semibold shadow-2xs'
                            : 'text-slate-600'
                        }`}
                      >
                        board-tt (Zobrist)
                      </button>
                    </div>
                  </div>

                  {/* Superko Rule */}
                  <div>
                    <label className="block font-medium text-slate-700">
                      同形禁着规则 (FR-2.2 Canonical HistorySet)
                    </label>
                    <div className="mt-1 grid grid-cols-3 gap-1 rounded-md bg-slate-100 p-1">
                      {(
                        [
                          [KoRule.SituationalSuperko, 'SSK (默认)'],
                          [KoRule.PositionalSuperko, 'PSK (实验)'],
                          [KoRule.SimpleKoOnly, 'SimpleKo'],
                        ] as const
                      ).map(([rule, label]) => (
                        <button
                          key={rule}
                          type="button"
                          onClick={() =>
                            setSolverConfig((c) => ({ ...c, koRule: rule }))
                          }
                          className={`py-1 font-mono text-xs rounded-xs cursor-pointer ${
                            solverConfig.koRule === rule
                              ? 'bg-white text-slate-900 font-semibold shadow-2xs'
                              : 'text-slate-600'
                          }`}
                        >
                          {label}
                        </button>
                      ))}
                    </div>
                  </div>

                  {/* Node Budget Selector */}
                  <div>
                    <label className="block font-medium text-slate-700">
                      最大搜索节点预算 (maxNodes FR-4.7)
                    </label>
                    <div className="mt-1 grid grid-cols-3 gap-1 rounded-md bg-slate-100 p-1">
                      {(
                        [
                          [3500, '3,500 (快速)'],
                          [10000, '10,000 (标准)'],
                          [25000, '25,000 (深搜)'],
                        ] as const
                      ).map(([budget, label]) => (
                        <button
                          key={budget}
                          type="button"
                          onClick={() =>
                            setSolverConfig((c) => ({ ...c, maxNodes: budget }))
                          }
                          className={`py-1 font-mono text-xs rounded-xs cursor-pointer ${
                            solverConfig.maxNodes === budget
                              ? 'bg-white text-slate-900 font-semibold shadow-2xs'
                              : 'text-slate-600'
                          }`}
                        >
                          {label}
                        </button>
                      ))}
                    </div>
                  </div>

                  {/* Checkboxes for algorithmic switches */}
                  <div className="space-y-2 pt-1">
                    <label className="flex items-center justify-between gap-2 cursor-pointer">
                      <span className="text-slate-700">
                        FR-5.5 OutsideRZRevalidated 脱先重放剪枝
                      </span>
                      <input
                        type="checkbox"
                        checked={solverConfig.enableRzPruning}
                        onChange={(e) =>
                          setSolverConfig((c) => ({
                            ...c,
                            enableRzPruning: e.target.checked,
                          }))
                        }
                        className="h-4 w-4 rounded border-slate-300 text-slate-900"
                      />
                    </label>

                    <label className="flex items-center justify-between gap-2 cursor-pointer">
                      <span className="text-slate-700">
                        FR-4.10 FastCapture 确定性提子紧气排序
                      </span>
                      <input
                        type="checkbox"
                        checked={solverConfig.enableFastCaptureOrdering}
                        onChange={(e) =>
                          setSolverConfig((c) => ({
                            ...c,
                            enableFastCaptureOrdering: e.target.checked,
                          }))
                        }
                        className="h-4 w-4 rounded border-slate-300 text-slate-900"
                      />
                    </label>

                    <label className="flex items-center justify-between gap-2 cursor-pointer">
                      <span className="text-slate-700">
                        FR-4.4 渐进拓宽 (Progressive Widening K·2^ℓ)
                      </span>
                      <input
                        type="checkbox"
                        checked={solverConfig.enableProgressiveWidening}
                        onChange={(e) =>
                          setSolverConfig((c) => ({
                            ...c,
                            enableProgressiveWidening: e.target.checked,
                          }))
                        }
                        className="h-4 w-4 rounded border-slate-300 text-slate-900"
                      />
                    </label>

                    <label className="flex items-center justify-between gap-2 cursor-pointer rounded-md bg-amber-50/80 border border-amber-200 px-2.5 py-2">
                      <div>
                        <div className="font-semibold text-amber-950">
                          FR-3.9 / FR-5.7 允许攻方劫胜 (attacker_allow_ko)
                        </div>
                        <div className="text-[11px] text-amber-800">
                          在第 05 题中切换此项可观察 UNKNOWN(ko_dependent) 与 PROVEN_WIN 转换
                        </div>
                      </div>
                      <input
                        type="checkbox"
                        checked={solverConfig.attackerAllowKo}
                        onChange={(e) =>
                          setSolverConfig((c) => ({
                            ...c,
                            attackerAllowKo: e.target.checked,
                          }))
                        }
                        className="h-4 w-4 rounded border-amber-400 text-slate-900"
                      />
                    </label>

                    <label className="flex items-center justify-between gap-2 cursor-pointer rounded-md bg-slate-50 border border-slate-200 px-2.5 py-2">
                      <div>
                        <div className="font-semibold text-slate-900">
                          FR-5.7 允许守方借劫反驳 (defender_allow_ko)
                        </div>
                        <div className="text-[11px] text-slate-600">
                          对齐 study-LD-RZ 题库契约（做活题中杀棋方成劫即破活）
                        </div>
                      </div>
                      <input
                        type="checkbox"
                        checked={solverConfig.defenderAllowKo}
                        onChange={(e) =>
                          setSolverConfig((c) => ({
                            ...c,
                            defenderAllowKo: e.target.checked,
                          }))
                        }
                        className="h-4 w-4 rounded border-slate-300 text-slate-900"
                      />
                    </label>
                  </div>
                </div>
              </div>
            </aside>
          </div>
        )}

        {/* TAB 2: PROOF DAG & SGF */}
        {activeTab === 'proof-dag' && (
          <div className="space-y-6">
            <div className="border border-slate-200 bg-white rounded-lg p-6">
              <div className="flex flex-wrap items-center justify-between gap-4 pb-4 border-b border-slate-200">
                <div>
                  <h2 className="text-base font-semibold text-slate-900">
                    后序拓扑证明图 (lproof/1 Post-Order Proof DAG) — {currentProblem.title}
                  </h2>
                  <p className="mt-0.5 text-xs text-slate-500">
                    符合 FR-8.3 与 §4.1 规范：所有子节点 ID 严格小于父节点 ID（child_id &lt; node_id），Win 绑定 (0, SAT)，Loss 绑定 (SAT, 0)。
                  </p>
                </div>

                <div className="flex items-center gap-2">
                  <button
                    type="button"
                    onClick={() =>
                      handleDownloadFile(
                        `proof_${solveReport.problemId}.json`,
                        solveReport.lproofJson
                      )
                    }
                    className="inline-flex items-center gap-1.5 rounded-md border border-slate-300 bg-white px-3 py-1.5 text-xs font-medium text-slate-800 hover:bg-slate-50 cursor-pointer"
                  >
                    <Download className="h-3.5 w-3.5" />
                    下载 proof_{solveReport.problemId}.json
                  </button>
                  <button
                    type="button"
                    onClick={() =>
                      handleDownloadFile(
                        `uct_tree_${solveReport.problemId}.sgf`,
                        solveReport.sgfContent,
                        'application/x-go-sgf'
                      )
                    }
                    className="inline-flex items-center gap-1.5 rounded-md bg-slate-900 px-3 py-1.5 text-xs font-medium text-white hover:bg-slate-800 cursor-pointer"
                  >
                    <Download className="h-3.5 w-3.5" />
                    下载 uct_tree_{solveReport.problemId}.sgf
                  </button>
                </div>
              </div>

              <div className="mt-4 overflow-x-auto">
                <table className="w-full text-left border-collapse text-xs font-mono tabular-nums">
                  <thead>
                    <tr className="border-b border-slate-200 text-slate-500">
                      <th className="py-2.5 pr-4">NodeID</th>
                      <th className="py-2.5 px-3">State / Hist</th>
                      <th className="py-2.5 px-3">节点类型</th>
                      <th className="py-2.5 px-3">入边落子</th>
                      <th className="py-2.5 px-3 text-right">PN</th>
                      <th className="py-2.5 px-3 text-right">DN</th>
                      <th className="py-2.5 px-3">结论 (Outcome)</th>
                      <th className="py-2.5 px-3">证据 / 剪枝证书 (FR-3.3 / FR-5.5)</th>
                      <th className="py-2.5 pl-3 text-right">子节点 ID</th>
                    </tr>
                  </thead>
                  <tbody className="divide-y divide-slate-200">
                    {solveReport.proofDagNodes.map((n) => (
                      <tr key={n.nodeId} className="hover:bg-slate-50">
                        <td className="py-2 pr-4 font-bold text-slate-900">
                          #{n.nodeId}
                          {n.nodeId === solveReport.rootDagNodeId ? ' (Root)' : ''}
                        </td>
                        <td className="py-2 px-3 text-slate-600">
                          S{n.stateId} / H{n.historyId}
                        </td>
                        <td className="py-2 px-3">
                          {n.isOrNode ? 'OR (攻)' : 'AND (守)'} ·{' '}
                          {n.toPlay === Color.Black ? 'B' : 'W'}
                        </td>
                        <td className="py-2 px-3 font-semibold text-slate-900">
                          {coordToHumanLabel(n.incomingMove, 19)}
                        </td>
                        <td className="py-2 px-3 text-right">
                          {n.pn >= PN_DN_SATURATION ? 'SAT' : n.pn}
                        </td>
                        <td className="py-2 px-3 text-right">
                          {n.dn >= PN_DN_SATURATION ? 'SAT' : n.dn}
                        </td>
                        <td
                          className={`py-2 px-3 font-semibold ${
                            n.outcome === ProofOutcome.ProvenWin
                              ? 'text-emerald-700'
                              : n.outcome === ProofOutcome.ProvenLoss
                              ? 'text-amber-700'
                              : 'text-slate-600'
                          }`}
                        >
                          {n.outcome}
                        </td>
                        <td className="py-2 px-3 text-slate-700">
                          {n.terminalEvidence}
                          {n.prunedCertificate
                            ? ` [srcNode=#${n.prunedCertificate.sourceProofNodeId}, RZ=${n.prunedCertificate.certificateRzCoords.length}]`
                            : ` [RZ=${
                                n.outcome === ProofOutcome.ProvenWin
                                  ? n.proofRzCoords.length
                                  : n.disproofRzCoords.length
                              }]`}
                        </td>
                        <td className="py-2 pl-3 text-right text-slate-500">
                          {n.childNodeIds.length > 0
                            ? n.childNodeIds.map((id) => `#${id}`).join(', ')
                            : 'Leaf'}
                        </td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>

            {/* SGF and Result JSON Split Output */}
            <div className="grid grid-cols-1 gap-6 lg:grid-cols-2 items-stretch">
              <div className="border border-slate-200 bg-white rounded-lg p-5 flex flex-col">
                <div className="flex items-center justify-between pb-3 border-b border-slate-200">
                  <h3 className="text-sm font-semibold text-slate-900">
                    result_{solveReport.problemId}.json (FR-8.1 全量字段契约)
                  </h3>
                  <button
                    type="button"
                    onClick={() =>
                      handleCopyText('resultJson', solveReport.resultJson)
                    }
                    className="inline-flex items-center gap-1 text-xs font-medium text-slate-600 hover:text-slate-900 cursor-pointer"
                  >
                    <Copy className="h-3.5 w-3.5" />
                    {copiedFeedback === 'resultJson' ? '已复制' : '复制 JSON'}
                  </button>
                </div>
                <pre className="mt-3 flex-1 overflow-x-auto rounded-md bg-slate-950 p-4 text-xs font-mono text-slate-100 leading-relaxed">
                  {solveReport.resultJson}
                </pre>
              </div>

              <div className="border border-slate-200 bg-white rounded-lg p-5 flex flex-col">
                <div className="flex items-center justify-between pb-3 border-b border-slate-200">
                  <h3 className="text-sm font-semibold text-slate-900">
                    uct_tree_{solveReport.problemId}.sgf (FR-8.2 解答树与 RZ 标记)
                  </h3>
                  <button
                    type="button"
                    onClick={() =>
                      handleCopyText('sgfContent', solveReport.sgfContent)
                    }
                    className="inline-flex items-center gap-1 text-xs font-medium text-slate-600 hover:text-slate-900 cursor-pointer"
                  >
                    <Copy className="h-3.5 w-3.5" />
                    {copiedFeedback === 'sgfContent' ? '已复制' : '复制 SGF'}
                  </button>
                </div>
                <pre className="mt-3 flex-1 overflow-x-auto whitespace-pre-wrap break-all rounded-md bg-slate-950 p-4 text-xs font-mono text-emerald-300 leading-relaxed">
                  {solveReport.sgfContent}
                </pre>
              </div>
            </div>
          </div>
        )}

        {/* TAB 3: INDEPENDENT PROOF CHECKER (FR-9) */}
        {activeTab === 'checker' && (
          <div className="grid grid-cols-1 gap-6 lg:grid-cols-12 items-start">
            <div className="lg:col-span-7 border border-slate-200 bg-white rounded-lg p-6">
              <div className="flex flex-wrap items-center justify-between gap-4 pb-4 border-b border-slate-200">
                <div>
                  <h2 className="text-base font-semibold text-slate-900">
                    tprover check — 独立 Proof Checker 复验报告 (FR-9.1..FR-9.3)
                  </h2>
                  <p className="mt-0.5 text-xs text-slate-500">
                    零搜索代码共享：从 initialTrace 独立回放 StateTable、SSK/PSK HistorySet、Benson UCA 叶子与 OutsideRZRevalidated 剪枝闭包。
                  </p>
                </div>

                <div
                  className={`px-3 py-1 text-xs font-mono font-bold rounded-md ${
                    verificationReport.passed
                      ? 'bg-emerald-50 text-emerald-800 border border-emerald-200'
                      : 'bg-red-50 text-red-800 border border-red-200'
                  }`}
                >
                  {verificationReport.passed ? 'PASS' : 'FAIL'} ·{' '}
                  {verificationReport.errorCode}
                </div>
              </div>

              {/* Fault Injection Sandbox */}
              <div className="mt-4 rounded-md border border-slate-200 bg-slate-50 p-4">
                <div className="text-xs font-semibold text-slate-900">
                  故障注入对抗验证台（§11.2 / FR-9.2 篡改检测测试）：
                </div>
                <p className="mt-1 text-xs text-slate-600">
                  选择下方注入模式，验证独立 Proof Checker 是否能精准拦截伪造证明、违反 LP-N15 饱和绑定或缺失 QueryState 重放的剪枝节点：
                </p>
                <div className="mt-3 flex flex-wrap gap-1.5">
                  {(
                    [
                      ['none', '正常证明 (无故障基准)'],
                      ['lp-n15-violation', '注入 LP-N15 违反 (篡改 PN/DN 绑定)'],
                      ['lp-t02-topology', '注入 LP-T02 违反 (破坏后序拓扑 ID)'],
                      ['jcs-checksum-tamper', '注入 JCS Checksum 篡改'],
                      ['missing-pruned-cert', '移除 OutsideRZ 重放证书'],
                    ] as const
                  ).map(([mode, label]) => (
                    <button
                      key={mode}
                      type="button"
                      onClick={() => setFaultMode(mode)}
                      className={`px-2.5 py-1.5 text-xs font-medium rounded-md cursor-pointer transition-colors ${
                        faultMode === mode
                          ? 'bg-slate-900 text-white'
                          : 'bg-white border border-slate-300 text-slate-700 hover:bg-slate-100'
                      }`}
                    >
                      {label}
                    </button>
                  ))}
                </div>
              </div>

              {/* 5 Formal Audit Checks */}
              <div className="mt-5 divide-y divide-slate-200">
                {verificationReport.auditChecks.map((chk) => (
                  <div
                    key={chk.checkId}
                    className="py-3.5 flex items-start justify-between gap-4"
                  >
                    <div>
                      <div className="flex items-center gap-2 text-xs font-semibold text-slate-900">
                        <span className="font-mono text-slate-500">
                          [{chk.checkId}]
                        </span>
                        <span>{chk.title}</span>
                        <span className="text-slate-400">·</span>
                        <span className="font-mono text-slate-500">
                          {chk.requirementRef}
                        </span>
                      </div>
                      <div className="mt-1 text-xs font-mono text-slate-600">
                        {chk.detail}
                      </div>
                    </div>
                    <span
                      className={`font-mono text-xs font-bold shrink-0 ${
                        chk.passed ? 'text-emerald-700' : 'text-red-700'
                      }`}
                    >
                      {chk.passed ? 'PASS' : 'FAIL'}
                    </span>
                  </div>
                ))}
              </div>

              <div className="mt-4 pt-4 border-t border-slate-200 text-xs font-mono text-slate-700 space-y-1">
                <div>Checker Message: {verificationReport.message}</div>
                <div className="text-slate-500">
                  RFC 8785 JCS SHA-256: {verificationReport.jcsSha256Checksum}
                </div>
                {standaloneJsonVerification && (
                  <div
                    className={
                      standaloneJsonVerification.passed
                        ? 'text-emerald-700 font-semibold'
                        : 'text-red-700 font-semibold'
                    }
                  >
                    Standalone JSON File Verifier (verifySerializedLProofJson):{' '}
                    {standaloneJsonVerification.passed ? 'PASS' : 'FAIL'} (
                    {standaloneJsonVerification.errorCode})
                  </div>
                )}
              </div>
            </div>

            {/* Right Column: Raw lproof/1 JSON Artifact */}
            <div className="lg:col-span-5 border border-slate-200 bg-white rounded-lg p-5">
              <div className="flex items-center justify-between pb-3 border-b border-slate-200">
                <h3 className="text-sm font-semibold text-slate-900">
                  proof_{solveReport.problemId}.json (Schema: lproof/1)
                </h3>
                <button
                  type="button"
                  onClick={() =>
                    handleCopyText('lproofJson', solveReport.lproofJson)
                  }
                  className="inline-flex items-center gap-1 text-xs font-medium text-slate-600 hover:text-slate-900 cursor-pointer"
                >
                  <Copy className="h-3.5 w-3.5" />
                  {copiedFeedback === 'lproofJson' ? '已复制' : '复制全量 lproof/1'}
                </button>
              </div>
              {solveReport.lproofJson.length > 48000 && (
                <div className="mt-2 rounded border border-slate-200 bg-slate-50 px-2.5 py-1.5 text-[11px] font-mono text-slate-600">
                  预览窗口显示前 48 KB（完整自包含证书共{' '}
                  {(solveReport.lproofJson.length / 1024).toFixed(1)}{' '}
                  KB，点击上方复制或 Tab 2 下载可获取完整无截断文件）
                </div>
              )}
              <pre className="mt-3 max-h-[560px] overflow-y-auto overflow-x-auto rounded-md bg-slate-950 p-4 text-xs font-mono text-slate-100 leading-relaxed">
                {solveReport.lproofJson.length > 48000
                  ? `${solveReport.lproofJson.slice(0, 48000)}\n... [Preview truncated at 48 KB; use Copy/Download for full lproof/1 artifact]`
                  : solveReport.lproofJson}
              </pre>
            </div>
          </div>
        )}

        {/* TAB 4: GOOGLE C++20 SOURCE & ARCHITECTURE */}
        {activeTab === 'cpp-source' && (
          <div className="space-y-6">
            {/* Module Dependency Matrix */}
            <div className="border border-slate-200 bg-white rounded-lg p-6">
              <h2 className="text-base font-semibold text-slate-900">
                LDProver C++20 模块化架构与接口隔离矩阵（Google C++ Style Guide）
              </h2>
              <p className="mt-1 text-xs text-slate-600">
                严格按《LDProver 开发需求说明书 v1.8》NFR-3 / NFR-10 拆分为 6 个独立可复用的静态库模块与 1 个 CLI 可执行程序，头文件包含防护宏、命名空间与依赖方向完全单向解耦：
              </p>

              <div className="mt-4 overflow-x-auto">
                <table className="w-full text-left border-collapse text-xs">
                  <thead>
                    <tr className="border-b border-slate-200 text-slate-500">
                      <th className="py-2 pr-4">CMake Target 模块</th>
                      <th className="py-2 px-3">核心接口类 (Google C++ Style)</th>
                      <th className="py-2 px-3">显式依赖模块</th>
                      <th className="py-2 px-3">追溯 SRS 需求编号</th>
                      <th className="py-2 pl-3">复用与安全隔离职责</th>
                    </tr>
                  </thead>
                  <tbody className="divide-y divide-slate-200 font-mono">
                    <tr>
                      <td className="py-2.5 pr-4 font-bold text-slate-900">
                        ldprover_core
                      </td>
                      <td className="py-2.5 px-3">
                        BitBoard&lt;N&gt;, Position&lt;N&gt;, ProblemContractParser
                      </td>
                      <td className="py-2.5 px-3 text-slate-500">无 (纯标准库)</td>
                      <td className="py-2.5 px-3">FR-1.1..1.3, FR-2.1..2.6, C-7</td>
                      <td className="py-2.5 pl-3 font-sans text-slate-600">
                        增量维护棋块/气、Zobrist、规范 HistorySet (SSK/PSK) 与不可复活目标令牌
                      </td>
                    </tr>
                    <tr>
                      <td className="py-2.5 pr-4 font-bold text-slate-900">
                        ldprover_terminal
                      </td>
                      <td className="py-2.5 px-3">
                        BensonTerminalEvaluator&lt;N&gt;
                      </td>
                      <td className="py-2.5 px-3 text-slate-500">ldprover_core</td>
                      <td className="py-2.5 px-3">FR-3.1..3.9</td>
                      <td className="py-2.5 pl-3 font-sans text-slate-600">
                        Benson UCA 最大不动点迭代、四值终局判定，产出可复验叶证据与叶 RZ
                      </td>
                    </tr>
                    <tr>
                      <td className="py-2.5 pr-4 font-bold text-slate-900">
                        ldprover_rz
                      </td>
                      <td className="py-2.5 px-3">
                        ProofCertificateRZ&lt;N&gt;, RelevanceZoneEngine&lt;N&gt;
                      </td>
                      <td className="py-2.5 px-3 text-slate-500">
                        ldprover_core, ldprover_terminal
                      </td>
                      <td className="py-2.5 px-3">FR-5.1..5.6</td>
                      <td className="py-2.5 pl-3 font-sans text-slate-600">
                        三类掩码强类型隔离、证明/反证明双链 RZ 回传、三重安全闭包
                      </td>
                    </tr>
                    <tr>
                      <td className="py-2.5 pr-4 font-bold text-slate-900">
                        ldprover_tt
                      </td>
                      <td className="py-2.5 px-3">
                        TranspositionStore&lt;N&gt;, RadixNode
                      </td>
                      <td className="py-2.5 px-3 text-slate-500">
                        ldprover_core, ldprover_rz
                      </td>
                      <td className="py-2.5 px-3">FR-6.1..6.9</td>
                      <td className="py-2.5 pl-3 font-sans text-slate-600">
                        BoardTT 全历史比对 + RZS-PT 四叉基数树模式表两级命中 (Heuristic / ProofReuse)
                      </td>
                    </tr>
                    <tr>
                      <td className="py-2.5 pr-4 font-bold text-slate-900">
                        ldprover_dfpn
                      </td>
                      <td className="py-2.5 px-3">DfpnSolver&lt;N&gt;</td>
                      <td className="py-2.5 px-3 text-slate-500">
                        core, terminal, rz, tt
                      </td>
                      <td className="py-2.5 px-3">FR-4.1..4.10, FR-5.5, FR-5.7</td>
                      <td className="py-2.5 pl-3 font-sans text-slate-600">
                        AND/OR 对偶阈值搜索、K·2^ℓ 渐进拓宽、OutsideRZRevalidated 重放剪枝、Ko 屏障
                      </td>
                    </tr>
                    <tr>
                      <td className="py-2.5 pr-4 font-bold text-emerald-800">
                        ldprover_proof
                      </td>
                      <td className="py-2.5 px-3">ProofArtifactManager&lt;N&gt;</td>
                      <td className="py-2.5 px-3 text-emerald-700 font-semibold">
                        core, terminal, rz (严禁依赖 dfpn)
                      </td>
                      <td className="py-2.5 px-3">FR-8.1..8.4, FR-9.1..9.3</td>
                      <td className="py-2.5 pl-3 font-sans text-slate-600">
                        lproof/1 序列化、SGF 导出与零搜索共享的独立 Proof Checker
                      </td>
                    </tr>
                  </tbody>
                </table>
              </div>
            </div>

            {/* Source File Explorer */}
            <div className="grid grid-cols-1 gap-6 lg:grid-cols-12 items-start">
              <aside className="lg:col-span-4 border border-slate-200 bg-white rounded-lg p-4">
                <div className="text-sm font-semibold text-slate-900 pb-3 border-b border-slate-200">
                  C++20 工程文件树 (/cpp/ · 共 {CPP_SOURCE_FILES.length} 个文件)
                </div>
                <div className="mt-2 divide-y divide-slate-100">
                  {CPP_SOURCE_FILES.map((file) => {
                    const active = file.path === currentCppFile.path;
                    return (
                      <button
                        key={file.path}
                        type="button"
                        onClick={() => setSelectedCppPath(file.path)}
                        className={`w-full py-2.5 px-2.5 text-left rounded-md transition-colors cursor-pointer ${
                          active
                            ? 'bg-slate-900 text-white'
                            : 'hover:bg-slate-50 text-slate-800'
                        }`}
                      >
                        <div className="font-mono text-xs font-semibold truncate">
                          {file.path}
                        </div>
                        <div
                          className={`mt-0.5 text-[11px] ${
                            active ? 'text-slate-300' : 'text-slate-500'
                          }`}
                        >
                          {file.moduleName} · {file.srsTracing}
                        </div>
                      </button>
                    );
                  })}
                </div>
              </aside>

              <section className="lg:col-span-8 border border-slate-200 bg-white rounded-lg p-5">
                <div className="flex flex-wrap items-center justify-between gap-2 pb-3 border-b border-slate-200">
                  <div>
                    <h3 className="font-mono text-sm font-bold text-slate-900">
                      {currentCppFile.path}
                    </h3>
                    <p className="mt-0.5 text-xs text-slate-600">
                      {currentCppFile.googleStyleNotes}
                    </p>
                  </div>

                  <div className="flex items-center gap-2">
                    <button
                      type="button"
                      onClick={() =>
                        handleCopyText(
                          currentCppFile.path,
                          currentCppFile.content
                        )
                      }
                      className="inline-flex items-center gap-1 rounded-md border border-slate-300 bg-white px-2.5 py-1.5 text-xs font-medium text-slate-700 hover:bg-slate-50 cursor-pointer"
                    >
                      <Copy className="h-3.5 w-3.5" />
                      {copiedFeedback === currentCppFile.path
                        ? '已复制源码'
                        : '复制源码'}
                    </button>
                    <button
                      type="button"
                      onClick={() =>
                        handleDownloadFile(
                          currentCppFile.path.split('/').pop() || 'source.cc',
                          currentCppFile.content,
                          'text/plain'
                        )
                      }
                      className="inline-flex items-center gap-1 rounded-md bg-slate-900 px-3 py-1.5 text-xs font-medium text-white hover:bg-slate-800 cursor-pointer"
                    >
                      <Download className="h-3.5 w-3.5" />
                      下载此文件
                    </button>
                  </div>
                </div>

                <pre className="mt-4 max-h-[680px] overflow-y-auto overflow-x-auto rounded-md bg-slate-950 p-4 text-xs font-mono text-slate-100 leading-relaxed">
                  {currentCppFile.content}
                </pre>
              </section>
            </div>
          </div>
        )}

        {/* TAB 5: BATCH BENCHMARK & JSON CONTRACT TESTER */}
        {activeTab === 'benchmark' && (
          <div className="space-y-6">
            {/* Batch Benchmark Table */}
            <div className="border border-slate-200 bg-white rounded-lg p-6">
              <div className="flex flex-wrap items-center justify-between gap-4 pb-4 border-b border-slate-200">
                <div>
                  <h2 className="text-base font-semibold text-slate-900">
                    tprover bench — 批量死活题基准测试与独立 Checker 验收表 (FR-10.3 / NFR-11)
                  </h2>
                  <p className="mt-0.5 text-xs text-slate-500">
                    按确定性遍历顺序执行全部基准题集，所有 PROVEN_WIN / PROVEN_LOSS 结果均强制通过独立 Proof Checker 复验（NFR-1 Soundness = 100%）。
                  </p>
                </div>

                <div className="flex items-center gap-2">
                  <button
                    type="button"
                    onClick={handleRunFullBenchmark}
                    className="inline-flex items-center gap-1.5 rounded-md bg-slate-900 px-3.5 py-2 text-xs font-semibold text-white hover:bg-slate-800 cursor-pointer"
                  >
                    <Play className="h-3.5 w-3.5" />
                    重新执行全量基准
                  </button>
                </div>
              </div>

              {batchReports.length === 0 ? (
                <div className="py-10 text-center">
                  <p className="text-sm text-slate-600">
                    尚未生成批量基准表，请点击上方“重新执行全量基准”按钮运行全集求解与独立校验。
                  </p>
                  <button
                    type="button"
                    onClick={handleRunFullBenchmark}
                    className="mt-3 inline-flex items-center gap-1.5 rounded-md bg-slate-900 px-4 py-2 text-xs font-semibold text-white hover:bg-slate-800 cursor-pointer"
                  >
                    立即运行全量 {allProblems.length} 道死活题基准测试
                  </button>
                </div>
              ) : (
                <div className="mt-4 overflow-x-auto">
                  <table className="w-full text-left border-collapse text-xs font-mono tabular-nums">
                    <thead>
                      <tr className="border-b border-slate-200 text-slate-500">
                        <th className="py-2.5 pr-4">Problem ID & 题目</th>
                        <th className="py-2.5 px-3">目标谓词</th>
                        <th className="py-2.5 px-3">RootStatus</th>
                        <th className="py-2.5 px-3">BestMove / 原库答案</th>
                        <th className="py-2.5 px-3 text-right">Nodes</th>
                        <th className="py-2.5 px-3 text-right">RZ Size</th>
                        <th className="py-2.5 px-3 text-right">OutsideRZ 剪枝</th>
                        <th className="py-2.5 pl-3">Checker (lproof/1)</th>
                      </tr>
                    </thead>
                    <tbody className="divide-y divide-slate-200">
                      {batchReports.map(({ problem, report, verification }) => (
                        <tr
                          key={problem.id}
                          onClick={() => {
                            handleSelectProblem(problem.id);
                            setActiveTab('workbench');
                          }}
                          className="hover:bg-slate-50 cursor-pointer"
                        >
                          <td className="py-2.5 pr-4 font-sans font-semibold text-slate-900">
                            {problem.title}
                          </td>
                          <td className="py-2.5 px-3 text-slate-600">
                            {problem.winningColor === 'B'
                              ? problem.blackSearchGoal
                              : problem.whiteSearchGoal}{' '}
                            ({problem.winningColor === 'B'
                              ? problem.blackCrucialStone
                              : problem.whiteCrucialStone})
                          </td>
                          <td
                            className={`py-2.5 px-3 font-bold ${
                              report.rootStatus === ProofOutcome.ProvenWin
                                ? 'text-emerald-700'
                                : report.rootStatus === ProofOutcome.ProvenLoss
                                ? 'text-amber-700'
                                : 'text-slate-700'
                            }`}
                          >
                            {report.rootStatus}
                            {report.unknownReason
                              ? ` (${report.unknownReason})`
                              : ''}
                          </td>
                          <td className="py-2.5 px-3 font-bold text-slate-900">
                            {coordToHumanLabel(report.bestMove, 19)}
                            {problem.groundTruthFirstMoves?.length
                              ? ` (标:${problem.groundTruthFirstMoves.join('/')})`
                              : ''}
                          </td>
                          <td className="py-2.5 px-3 text-right">
                            {report.numNodes}
                          </td>
                          <td className="py-2.5 px-3 text-right">
                            {report.rzSizeAtRoot}
                          </td>
                          <td className="py-2.5 px-3 text-right text-emerald-700 font-semibold">
                            {report.prunedOutsideRzCount}
                          </td>
                          <td
                            className={`py-2.5 pl-3 font-bold ${
                              verification.passed
                                ? 'text-emerald-700'
                                : 'text-amber-700'
                            }`}
                          >
                            {verification.errorCode}
                          </td>
                        </tr>
                      ))}
                    </tbody>
                  </table>
                </div>
              )}
            </div>

            {/* study-LD-RZ Failure Root-Cause Taxonomy & C++20 Engineering Roadmap */}
            <div className="border border-slate-200 bg-white rounded-lg p-6">
              <div className="pb-4 border-b border-slate-200">
                <h2 className="text-base font-semibold text-slate-900">
                  rlglab/study-LD-RZ 解答失败（UNKNOWN）题目根因分类与后续改进方法
                </h2>
                <p className="mt-1 text-xs text-slate-600">
                  针对从 GitHub 抓取的 16 道真实死活题中未能在静态 Benson UCA 阶段收敛的高阶题目，梳理出 4 类核心算法瓶颈与对应的 C++20 架构演进方案：
                </p>
              </div>

              <div className="mt-4 grid grid-cols-1 gap-4 lg:grid-cols-2">
                {STUDY_LD_RZ_FAILURE_TAXONOMY.map((cat) => (
                  <div
                    key={cat.id}
                    className="rounded-lg border border-slate-200 bg-slate-50/70 p-4 flex flex-col justify-between space-y-3"
                  >
                    <div className="space-y-2">
                      <div className="flex items-center justify-between gap-2">
                        <span className="font-mono text-xs font-bold text-slate-900">
                          [{cat.id}] {cat.title}
                        </span>
                        <span className="font-mono text-[11px] text-slate-500 shrink-0">
                          {cat.srsTracing}
                        </span>
                      </div>

                      <div className="text-[11px] font-mono text-amber-800">
                        涉及题号：{cat.affectedProblems.join(', ')}
                      </div>

                      <div className="text-xs text-slate-700 leading-relaxed">
                        <strong className="text-slate-900">现象表现：</strong>
                        {cat.symptom}
                      </div>

                      <div className="text-xs text-slate-700 leading-relaxed">
                        <strong className="text-slate-900">深层根因：</strong>
                        {cat.rootCauseAnalysis}
                      </div>

                      <div className="rounded border border-slate-200 bg-white p-2.5 text-xs text-slate-800 leading-relaxed">
                        <strong className="text-emerald-800">
                          工程改进方法：
                        </strong>
                        {cat.algorithmicSolution}
                      </div>
                    </div>

                    <div className="pt-2 border-t border-slate-200 text-[11px] font-mono text-slate-600 truncate">
                      C++20 接口：{cat.cppInterfaceDesign}
                    </div>
                  </div>
                ))}
              </div>
            </div>

            {/* FR-1.1..1.3 Input Contract Parser Validator */}
            <div className="border border-slate-200 bg-white rounded-lg p-6">
              <h2 className="text-base font-semibold text-slate-900">
                FR-1.1..FR-1.3 题目输入契约与拒题保护测试器 (ProblemContractParser)
              </h2>
              <p className="mt-1 text-xs text-slate-600">
                验证《LDProver 开发需求说明书 v1.8》FR-1.2（禁止以插入虚拟 pass 校正轮走方冲突）与 FR-1.3（禁止 crucial_stone 内混用 &amp; 与 |、禁止静默使用默认值）：
              </p>

              <div className="mt-4 flex flex-wrap gap-2">
                {(
                  [
                    ['valid', '合法契约样本 (FR1-OK)'],
                    ['turn-conflict', '测试 PL 与 turn_color 冲突拒题 (FR-1.2)'],
                    ['mixed-op', '测试 crucial_stone 混用 & 与 | 拒题 (FR-1.3)'],
                    [
                      'missing-crucial',
                      '测试 crucial_stone 不在盘拒题 (FR-1.3)',
                    ],
                    ['empty-crucial', '测试空关键子串恒假告警 (FR-1.3)'],
                  ] as const
                ).map(([preset, label]) => (
                  <button
                    key={preset}
                    type="button"
                    onClick={() => setContractPreset(preset)}
                    className={`px-3 py-1.5 text-xs font-medium rounded-md cursor-pointer transition-colors ${
                      contractPreset === preset
                        ? 'bg-slate-900 text-white'
                        : 'bg-slate-100 text-slate-700 hover:bg-slate-200'
                    }`}
                  >
                    {label}
                  </button>
                ))}
              </div>

              <div className="mt-4 grid grid-cols-1 gap-4 lg:grid-cols-2">
                <pre className="rounded-md bg-slate-950 p-4 text-xs font-mono text-slate-100 overflow-x-auto">
                  {contractTestResult.jsonSample}
                </pre>
                <div className="rounded-md border border-slate-200 bg-slate-50 p-4 flex flex-col justify-between">
                  <div>
                    <div
                      className={`text-xs font-mono font-bold ${
                        !contractTestResult.valid
                          ? 'text-red-700'
                          : contractTestResult.warning
                          ? 'text-amber-700'
                          : 'text-emerald-700'
                      }`}
                    >
                      Validator Status: {contractTestResult.code}
                    </div>
                    <p className="mt-2 text-xs leading-relaxed text-slate-700">
                      {contractTestResult.summary}
                    </p>
                  </div>
                  <div className="mt-4 pt-3 border-t border-slate-200 text-[11px] font-mono text-slate-500">
                    实时执行引擎：validateStudyLdRzContract() ↔ C++ ProblemContractParser&lt;N&gt;::ParseTsumegoJson
                  </div>
                </div>
              </div>
            </div>
          </div>
        )}

      </main>

      {/* Quiet Footer (§1.B) */}
      <footer className="border-t border-slate-200 bg-white px-6 py-4 text-xs text-slate-500">
        <div className="mx-auto flex max-w-[1440px] flex-wrap items-center justify-between gap-4">
          <span>
            LDProver v1.8 · C++20 围棋死活精确求解器与形式化证明校验系统
          </span>
          <span>
            遵循 Google C++ Style Guide 与《LDProver 开发需求说明书 v1.8》
          </span>
        </div>
      </footer>
    </div>
  );
}
