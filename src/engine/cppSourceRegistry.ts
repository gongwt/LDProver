// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Registry of the real C++20 source files in /cpp/ loaded via Vite ?raw imports.

import cmakeListsRaw from '../../cpp/CMakeLists.txt?raw';
import typesHeaderRaw from '../../cpp/include/ldprover/core/types.h?raw';
import positionHeaderRaw from '../../cpp/include/ldprover/core/position.h?raw';
import positionCcRaw from '../../cpp/src/core/position.cc?raw';
import parserHeaderRaw from '../../cpp/include/ldprover/core/problem_parser.h?raw';
import parserCcRaw from '../../cpp/src/core/problem_parser.cc?raw';
import bensonHeaderRaw from '../../cpp/include/ldprover/terminal/benson_uca.h?raw';
import bensonCcRaw from '../../cpp/src/terminal/benson_uca.cc?raw';
import rzHeaderRaw from '../../cpp/include/ldprover/rz/relevance_zone.h?raw';
import rzCcRaw from '../../cpp/src/rz/relevance_zone.cc?raw';
import ttHeaderRaw from '../../cpp/include/ldprover/tt/transposition_table.h?raw';
import ttCcRaw from '../../cpp/src/tt/transposition_table.cc?raw';
import dfpnHeaderRaw from '../../cpp/include/ldprover/search/dfpn_solver.h?raw';
import dfpnCcRaw from '../../cpp/src/search/dfpn_solver.cc?raw';
import checkerHeaderRaw from '../../cpp/include/ldprover/proof/proof_checker.h?raw';
import checkerCcRaw from '../../cpp/src/proof/proof_checker.cc?raw';
import cliMainCcRaw from '../../cpp/src/cli/tprover_main.cc?raw';

export interface CppSourceFileItem {
  path: string;
  moduleName: string;
  srsTracing: string;
  googleStyleNotes: string;
  content: string;
}

export const CPP_SOURCE_FILES: CppSourceFileItem[] = [
  {
    path: 'cpp/CMakeLists.txt',
    moduleName: 'Build & Module Isolation',
    srsTracing: 'NFR-3 / NFR-10',
    googleStyleNotes:
      'CMake >= 3.16, C++20 strict standard, modular static libraries (ldprover_core, ldprover_terminal, ldprover_rz, ldprover_tt, ldprover_dfpn, ldprover_proof) with zero search dependency in ProofChecker.',
    content: cmakeListsRaw,
  },
  {
    path: 'cpp/include/ldprover/core/types.h',
    moduleName: 'ldprover_core (Header)',
    srsTracing: 'FR-2.1..2.6 / C-6 / C-7',
    googleStyleNotes:
      'Header guard LDPROVER_CORE_TYPES_H_, kPascalCase constants, templated BitBoard<N> (N <= 19), CanonicalSnapshot, TargetToken, and ProofContext.',
    content: typesHeaderRaw,
  },
  {
    path: 'cpp/include/ldprover/core/position.h',
    moduleName: 'ldprover_core (Header)',
    srsTracing: 'FR-2.1..2.6',
    googleStyleNotes:
      'Position<N> class interface with snake_case_ private members, PascalCase methods, const-correctness, and explicit constructors.',
    content: positionHeaderRaw,
  },
  {
    path: 'cpp/src/core/position.cc',
    moduleName: 'ldprover_core (Impl)',
    srsTracing: 'FR-2.1..2.6',
    googleStyleNotes:
      'SplitMix64 deterministic Zobrist table, incremental PlayMove/UndoMove, SSK/PSK full BitBoard HistorySet comparison, and non-revivable surviving_target_tokens_mask_.',
    content: positionCcRaw,
  },
  {
    path: 'cpp/include/ldprover/core/problem_parser.h',
    moduleName: 'ldprover_core (Parser Header)',
    srsTracing: 'FR-1.1..1.3',
    googleStyleNotes:
      'Strict tsumego/*.json contract parser interface; forbids synthetic pass insertion on turn_color conflict.',
    content: parserHeaderRaw,
  },
  {
    path: 'cpp/src/core/problem_parser.cc',
    moduleName: 'ldprover_core (Parser Impl)',
    srsTracing: 'FR-1.1..1.3',
    googleStyleNotes:
      'Validates required fields, rejects mixed & and | operators in crucial_stone, and enforces TurnConflictPolicy.',
    content: parserCcRaw,
  },
  {
    path: 'cpp/include/ldprover/terminal/benson_uca.h',
    moduleName: 'ldprover_terminal (Header)',
    srsTracing: 'FR-3.1..3.9',
    googleStyleNotes:
      'BensonTerminalEvaluator<N> interface, StoneChainInfo, EyeSpaceRegion, and verifiable TerminalEvaluationResult.',
    content: bensonHeaderRaw,
  },
  {
    path: 'cpp/src/terminal/benson_uca.cc',
    moduleName: 'ldprover_terminal (Impl)',
    srsTracing: 'FR-3.1..3.9',
    googleStyleNotes:
      'Benson greatest-fixpoint elimination loop, vital eye region verification, double-pass priority over InPath (FR-3.8), and leaf ProofCertificateRZ generation.',
    content: bensonCcRaw,
  },
  {
    path: 'cpp/include/ldprover/rz/relevance_zone.h',
    moduleName: 'ldprover_rz (Header)',
    srsTracing: 'FR-5.1..5.6',
    googleStyleNotes:
      'Type-isolated ProblemSearchMask, NNAttentionMask, ProofCertificateRZ (no implicit conversion), and self-contained PrunedCertificate.',
    content: rzHeaderRaw,
  },
  {
    path: 'cpp/src/rz/relevance_zone.cc',
    moduleName: 'ldprover_rz (Impl)',
    srsTracing: 'FR-5.2..5.5',
    googleStyleNotes:
      'Dual-chain proof/disproof RZ backpropagation: attacker influence closure and defender triple safety closure.',
    content: rzCcRaw,
  },
  {
    path: 'cpp/include/ldprover/tt/transposition_table.h',
    moduleName: 'ldprover_tt (Header)',
    srsTracing: 'FR-6.1..6.9',
    googleStyleNotes:
      'Context-isolated BoardTT and 4-branch Radix-Tree PatternTT (RZS-PT) with HeuristicOnly vs ProofReusable two-grade hit classification.',
    content: ttHeaderRaw,
  },
  {
    path: 'cpp/src/tt/transposition_table.cc',
    moduleName: 'ldprover_tt (Impl)',
    srsTracing: 'FR-6.1..6.9',
    googleStyleNotes:
      'Full canonical HistorySet + surviving_tokens_mask + consecutive_passes comparison after Zobrist bucket lookup; ProofClosureAvailable gate.',
    content: ttCcRaw,
  },
  {
    path: 'cpp/include/ldprover/search/dfpn_solver.h',
    moduleName: 'ldprover_dfpn (Header)',
    srsTracing: 'FR-4.1..4.10 / FR-5.5 / FR-5.7',
    googleStyleNotes:
      'DfpnSolver<N>, SolverConfig, ProofDagNode<N>, and SolveReport<N> structures.',
    content: dfpnHeaderRaw,
  },
  {
    path: 'cpp/src/search/dfpn_solver.cc',
    moduleName: 'ldprover_dfpn (Impl)',
    srsTracing: 'FR-4.1..4.10 / FR-5.5 / FR-5.7',
    googleStyleNotes:
      'AND/OR df-pn frontier aggregation (min-PN / sum-DN + U), implicit child cost 1, progressive widening K*2^l, FastCapture ordering, OutsideRZRevalidated replay, and KoDependent barrier.',
    content: dfpnCcRaw,
  },
  {
    path: 'cpp/include/ldprover/proof/proof_checker.h',
    moduleName: 'ldprover_proof (Header)',
    srsTracing: 'FR-8.1..8.4 / FR-9.1..9.3',
    googleStyleNotes:
      'ProofArtifactManager<N> and VerificationReport; zero search code dependency.',
    content: checkerHeaderRaw,
  },
  {
    path: 'cpp/src/proof/proof_checker.cc',
    moduleName: 'ldprover_proof (Impl)',
    srsTracing: 'FR-8.1..8.4 / FR-9.1..9.3',
    googleStyleNotes:
      'lproof/1 JSON DAG serializer, uct_tree_<problem>.sgf exporter, and independent ProofChecker enforcing LP-N15 (0, SAT)/(SAT, 0) and post-order topology.',
    content: checkerCcRaw,
  },
  {
    path: 'cpp/src/cli/tprover_main.cc',
    moduleName: 'tprover CLI',
    srsTracing: 'FR-10.1..10.3',
    googleStyleNotes:
      'CLI subcommands solve, check, and bench with strict exit code contract (0, 2, 3).',
    content: cliMainCcRaw,
  },
];
