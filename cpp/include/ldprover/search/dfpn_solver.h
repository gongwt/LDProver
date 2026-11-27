// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: include/ldprover/search/dfpn_solver.h
// Description: Depth-First Proof-Number (df-pn) search solver with
// Relevance-Zone backpropagation, OutsideRZRevalidated null-move certificate
// pruning, FastCapture move ordering, Progressive Widening (K * 2^l),
// and KoDependent witness barrier (FR-4.1..FR-4.10, FR-5.5, FR-5.7).

#ifndef LDPROVER_SEARCH_DFPN_SOLVER_H_
#define LDPROVER_SEARCH_DFPN_SOLVER_H_

#include <array>
#include <chrono>
#include <cstdint>
#include <limits>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "ldprover/core/position.h"
#include "ldprover/core/types.h"
#include "ldprover/rz/relevance_zone.h"
#include "ldprover/terminal/benson_uca.h"
#include "ldprover/tt/transposition_table.h"

namespace ldprover {

inline constexpr uint32_t kInvalidDagNodeId =
    std::numeric_limits<uint32_t>::max();

struct SolverConfig {
  uint32_t max_nodes = 10000;
  uint32_t max_depth = 64;
  uint64_t memory_budget_bytes = 512ULL * 1024ULL * 1024ULL;
  // Cooperative wall-clock budget for Solve() in ms (0 = disabled).
  uint64_t time_limit_ms = 0ULL;
  bool enable_rz_pruning = true;
  bool enable_pattern_tt = true;
  bool enable_fast_capture_ordering = true;
  bool enable_progressive_widening = true;
  uint32_t widening_base_k = 8;
  bool deterministic_mode = true;  // FR-7.8, NFR-4
  bool enable_stage_profiling = false;
  bool enable_convergence_trace = false;
  std::vector<std::string> observed_paths;
  bool enable_near_pn_continuation = false;
  // A zero budget disables near-pn continuation (0 claims, 0 extra calls,
  // byte-identical to `enable_near_pn_continuation = false`).
  uint32_t near_pn_continuation_max_calls = 64U;
};

struct ObservedChildSummary {
  std::string move_sgf;
  int16_t move = kPassMove;
  uint32_t rank = 0;
  int32_t tactical_score = 0;
  uint32_t pn = 1;
  uint32_t dn = 1;
  uint32_t dag_node_id = kInvalidDagNodeId;
  bool probed = false;
  bool ko_dependent = false;
  bool in_window = false;
  bool deferred_outside_rz = false;
  bool pruned_outside_rz = false;
  bool has_decisive_dag = false;
  ProofOutcome outcome = ProofOutcome::kUnknown;
};

struct ObservedPathTrace {
  std::string path;
  uint64_t first_enter_node = 0;
  uint64_t visit_count = 0;
  uint64_t first_active_rz_source_node = 0;
  int16_t first_active_rz_source_move = kNullMove;
  std::string first_active_rz_source_move_sgf;
  uint32_t first_active_rz_source_dag_id = kInvalidDagNodeId;
  int first_active_rz_source_size = 0;
  uint64_t first_decisive_child_node = 0;
  int16_t first_decisive_child_move = kNullMove;
  std::string first_decisive_child_move_sgf;
  ProofOutcome first_decisive_child_outcome = ProofOutcome::kUnknown;
  uint32_t max_depth_under_path = 0;
  std::string deepest_line_under_path;

  bool frontier_exists = false;
  bool frontier_erased_on_proof = false;
  bool is_or_node = true;
  uint32_t total_legal_moves = 0;
  uint32_t widening_level = 0;
  uint32_t window_size = 0;
  bool has_active_rz_source = false;
  int16_t representative_move = kNullMove;
  std::string representative_move_sgf;
  int active_rz_size = 0;
  uint32_t closed_proven_win_direct = 0;
  uint32_t closed_proven_win_outside_rz = 0;
  uint32_t closed_proven_loss_direct = 0;
  uint32_t closed_proven_loss_outside_rz = 0;
  uint32_t deferred_outside_rz_count = 0;
  uint32_t ko_barrier_count = 0;
  uint32_t expanded_unknown_count = 0;
  uint32_t unexpanded_unknown_count = 0;
  std::vector<ObservedChildSummary> closed_children;
  std::vector<ObservedChildSummary> top_unclosed_children;
  std::vector<ObservedChildSummary> watched_next_moves;
};

struct RootChildCallStat {
  std::string move_sgf;
  int16_t move = kPassMove;
  uint32_t select_count = 0;
  uint64_t calls_spent = 0;
  uint32_t final_pn = 1;
  uint32_t final_dn = 1;
  ProofOutcome final_outcome = ProofOutcome::kUnknown;
};

struct NearPnContinuationTrace {
  bool enabled = false;
  uint32_t max_extra_calls = 64;
  bool claimed = false;
  std::string claimed_path;
  int16_t claimed_move = kNullMove;
  uint64_t trigger_node = 0;
  uint64_t exit_node = 0;
  uint64_t extra_calls_spent = 0;
  uint32_t orig_th_pn = 0;
  uint32_t boosted_th_pn = 0;
  uint32_t th_dn = 0;
  uint32_t pre_pn = 0;
  uint32_t pre_dn = 0;
  uint32_t return_pn = 0;
  uint32_t return_dn = 0;
  ProofOutcome return_outcome = ProofOutcome::kUnknown;
  uint32_t return_dag_id = kInvalidDagNodeId;
  bool acquired_active_rz_source = false;
  int16_t active_rz_source_move = kNullMove;
  std::string active_rz_source_move_sgf;
  uint32_t active_rz_source_dag_id = kInvalidDagNodeId;
  int active_rz_source_size = 0;
};

struct ConvergenceTraceReport {
  bool enabled = false;
  std::string path_basis = "solve_root_relative";
  std::string initial_trace_path;
  uint64_t first_terminal_leaf_node = 0;
  EvidenceKind first_terminal_leaf_kind = EvidenceKind::kNone;
  std::string first_terminal_leaf_path;
  uint64_t first_non_terminal_subproof_node = 0;
  ProofOutcome first_non_terminal_subproof_outcome = ProofOutcome::kUnknown;
  uint32_t first_non_terminal_subproof_dag_id = kInvalidDagNodeId;
  std::string first_non_terminal_subproof_path;
  uint32_t max_depth_reached = 0;
  std::string deepest_path;
  std::vector<ObservedPathTrace> watched_paths;
  std::vector<RootChildCallStat> root_child_calls;
  NearPnContinuationTrace near_pn_continuation{};
};

enum class RevalCaller : uint8_t {
  kOutsideRz = 0,
  kBoardTt = 1,
  kPatternTt = 2,
};

struct RevalCallerStats {
  uint64_t top_calls = 0;
  uint64_t top_successes = 0;
  uint64_t top_failures = 0;
  uint64_t inclusive_ns = 0;
};

struct SolverStageProfile {
  bool enabled = false;
  uint64_t solve_total_ns = 0;
  TTProfileStats tt{};

  std::array<RevalCallerStats, 3> reval_by_caller{};
  uint64_t outside_rz_candidates_tested = 0;
  uint64_t outside_rz_play_move_ns = 0;
  uint64_t reval_recursive_visits = 0;
  uint64_t reval_cache_hits = 0;
  uint64_t reval_cache_misses = 0;
  uint64_t reval_witness_visits = 0;
  uint64_t reval_witness_play_moves = 0;
  uint64_t reval_universal_visits = 0;
  uint64_t reval_universal_legal_moves = 0;
  uint64_t reval_universal_edge_comparisons = 0;
  uint64_t reval_universal_play_moves = 0;
  uint64_t reval_cache_lookup_ns = 0;
  uint64_t benson_replay_calls = 0;
  uint64_t benson_replay_ns = 0;
  uint64_t reval_witness_play_move_ns = 0;
  uint64_t reval_universal_gen_legal_ns = 0;
  uint64_t reval_universal_edge_scan_ns = 0;
  uint64_t reval_universal_play_move_ns = 0;

  uint64_t benson_main_calls = 0;
  uint64_t benson_main_ns = 0;
  uint64_t new_frontiers = 0;
  uint64_t candidates_generated = 0;
  uint64_t candidates_scored = 0;
  uint64_t candidates_pass_scored = 0;
  uint64_t candidates_outer_moat_skipped = 0;
  uint64_t candidate_scoring_play_moves = 0;
  uint64_t benson_cand_calls = 0;
  uint64_t benson_cand_ns = 0;
  uint64_t frontier_tctx_ns = 0;
  uint64_t frontier_gen_legal_ns = 0;
  uint64_t cand_eval_exclusive_ns = 0;
  uint64_t frontier_sort_init_ns = 0;
  uint64_t main_search_play_moves = 0;
  uint64_t main_play_undo_ns = 0;
  uint64_t rz_compute_ns = 0;

  uint64_t peak_frontiers = 0;
  uint64_t live_frontiers_at_end = 0;
  uint64_t reval_cache_entries = 0;
  uint64_t dag_nodes = 0;
  uint64_t benson_uca_leaves = 0;
  uint64_t tokens_captured_leaves = 0;
  uint64_t double_pass_leaves = 0;
  uint64_t pruned_outside_rz_dag_nodes = 0;
  uint64_t tt_hit_dag_nodes = 0;
  uint64_t estimated_memory_bytes = 0;
};

template <int N = kDefaultBoardSize>
struct ProofDagNode {
  uint32_t node_id = 0;
  uint32_t state_id = 0;
  uint32_t history_id = 0;
  bool is_or_node = true;
  Color to_play = Color::kBlack;
  int16_t incoming_move = kPassMove;
  uint32_t pn = 1;
  uint32_t dn = 1;
  ProofOutcome outcome = ProofOutcome::kUnknown;
  EvidenceKind terminal_evidence = EvidenceKind::kNone;
  bool is_pruned_outside_rz = false;
  bool is_tt_hit = false;
  uint32_t source_proof_node_id = kInvalidDagNodeId;
  ProofCertificateRZ<N> proof_rz{};
  ProofCertificateRZ<N> disproof_rz{};
  std::vector<uint32_t> child_node_ids;
  std::vector<int16_t> child_moves;
};

template <int N = kDefaultBoardSize>
struct SolveReport {
  std::string problem_id;
  uint64_t input_hash = 0;
  std::optional<BitBoard<N>> region_hint;
  ProofOutcome root_status = ProofOutcome::kUnknown;
  UnknownReason unknown_reason = UnknownReason::kNone;
  uint32_t root_pn = 1;
  uint32_t root_dn = 1;
  int16_t best_move = kPassMove;
  uint64_t num_nodes = 0;
  uint64_t board_tt_hits = 0;
  uint64_t pattern_tt_hits = 0;
  uint64_t pattern_proof_reusable = 0;
  uint64_t pruned_outside_rz_count = 0;
  uint64_t widening_upgrades = 0;
  uint64_t cycle_detections = 0;
  int rz_size_at_root = 0;
  bool resource_exhausted = false;
  uint64_t estimated_memory_bytes = 0;
  ProofCertificateRZ<N> root_proof_rz{};
  ProofCertificateRZ<N> root_disproof_rz{};
  std::vector<int16_t> principal_variation;
  std::vector<ProofDagNode<N>> proof_dag_nodes;
  uint32_t root_dag_node_id = kInvalidDagNodeId;
};

template <int N = kDefaultBoardSize>
class DfpnSolver {
 public:
  explicit DfpnSolver(const SolverConfig& config = {}) : config_(config) {}

  SolveReport<N> Solve(const Position<N>& initial_pos,
                       const ProofContext& context,
                       const std::optional<BitBoard<N>>& region_hint =
                           std::nullopt,
                       const std::string& problem_id = "");

  // Heuristic eye-like liberty potential of surviving crucial chains (1:1 parity
  // with TS BensonTerminalEvaluator::estimateHeuristicShapePotential):
  // +2 for fully surrounded empty point (enemy_nbs == 0 && friendly_nbs == deg),
  // +1 for protected tiger's mouth (enemy_nbs == 0 && friendly_nbs >= max(2, deg-1)).
  static int EstimateParentEyeLikeCount(const Position<N>& pos,
                                        const ProofContext& context);

  // Public diagnostic accessor for PASS move tactical ordering score parity.
  int32_t EvaluatePassMoveScore(const Position<N>& pos,
                                const ProofContext& context,
                                bool is_or_node) const;

  const SolverStageProfile& StageProfile() const noexcept {
    return stage_profile_;
  }

  const ConvergenceTraceReport& ConvergenceTrace() const noexcept {
    return convergence_trace_;
  }

 private:
  struct MoveEvalMeta {
    int32_t score = 0;
    bool immediate_win = false;
    bool immediate_loss = false;
    bool in_attention = true;
  };

  struct SearchChild {
    int16_t move = kPassMove;
    int32_t tactical_score = 0;
    uint32_t pn = 1;
    uint32_t dn = 1;
    ProofOutcome outcome = ProofOutcome::kUnknown;
    bool probed = false;
    bool has_decisive_dag = false;
    bool pruned_outside_rz = false;
    bool ko_dependent = false;
    bool move_captured = false;
    bool subtree_has_capture = false;
    uint32_t checked_null_move_dag_id = kInvalidDagNodeId;
    uint32_t dag_node_id = kInvalidDagNodeId;
    uint64_t child_path_id = 0;
    ProofCertificateRZ<N> proof_rz{};
    ProofCertificateRZ<N> disproof_rz{};
  };

  struct CachedNodeFrontier {
    std::vector<SearchChild> children;
    uint32_t widening_level = 0;
    ProofCertificateRZ<N> active_null_move_rz{};
    bool has_null_move_rz = false;
    bool pass_probed = false;
    int16_t representative_move = kPassMove;
    uint32_t representative_dag_id = kInvalidDagNodeId;
    ProofOutcome representative_outcome = ProofOutcome::kUnknown;
  };

  struct NodeTacticalContext {
    std::array<int16_t, N * N> chain_id_at{};
    std::vector<int16_t> chain_libs;
    std::vector<uint8_t> chain_is_immortal;
    std::vector<uint8_t> chain_is_cutting_enemy;
    BitBoard<N> crucial_stone_mask{};
    std::array<uint8_t, N * N> crucial_lib_min_libs{};
    Color target_color = Color::kBlack;
  };

  uint64_t EstimateMemoryBytes(uint32_t active_depth) const noexcept;
  bool IsMemoryBudgetExceeded(uint32_t active_depth) const noexcept;
  bool IsTimeLimitExceeded() const noexcept;

  NodeTacticalContext BuildNodeTacticalContext(
      const Position<N>& pos, const ProofContext& context) const;

  // FR-4.10: Deterministic FastCapture tactical move evaluation with dynamic
  // tactical attention, 1-ply Benson UCA detection, and crucial liberty delta.
  MoveEvalMeta EvaluateCandidateMove(const Position<N>& pos,
                                     const ProofContext& context,
                                     const NodeTacticalContext& tctx,
                                     int16_t move, bool is_or_node,
                                     int parent_eye_like_count) const;

  std::pair<uint32_t, uint32_t> ComputeInitialChildBounds(
      size_t rank_idx, bool is_or_node, const MoveEvalMeta& meta,
      int16_t move) const noexcept;

  void MidSearch(Position<N>& pos, const ProofContext& context,
                 const std::optional<BitBoard<N>>& region_hint,
                 uint32_t th_pn, uint32_t th_dn, uint32_t depth,
                 uint64_t node_path_id,
                 std::unordered_set<uint64_t>& in_path_hashes,
                 uint32_t* out_pn, uint32_t* out_dn,
                 ProofOutcome* out_outcome, bool* out_ko_dependent,
                 bool* out_has_capture,
                 ProofCertificateRZ<N>* out_proof_rz,
                 ProofCertificateRZ<N>* out_disproof_rz,
                 uint32_t* out_dag_node_id,
                 int16_t incoming_move);

  // FR-5.5: Revalidate source proof under QueryState + HistorySet (both witness
  // and full-coverage AND/OR nodes) before materializing OutsideRZRevalidated.
  bool RevalidateSourceProofOnQueryState(
      const Position<N>& query_pos, const ProofContext& context,
      const std::optional<BitBoard<N>>& region_hint,
      uint32_t source_dag_node_id, ProofOutcome expected_outcome,
      uint32_t guard_depth = 0,
      RevalCaller caller = RevalCaller::kOutsideRz) const;

  bool RevalidateSourceProofOnQueryStateImpl(
      const Position<N>& query_pos, const ProofContext& context,
      const std::optional<BitBoard<N>>& region_hint,
      uint32_t source_dag_node_id, ProofOutcome expected_outcome,
      uint32_t guard_depth) const;

  void FinalizeObservedFrontier(
      const CachedNodeFrontier& frontier, bool is_or_node, uint32_t depth,
      const std::optional<BitBoard<N>>& region_hint,
      bool erased_on_proof, ObservedPathTrace* out) const;

  SolverConfig config_;
  BensonTerminalEvaluator<N> terminal_eval_;
  RelevanceZoneEngine<N> rz_engine_;
  TranspositionStore<N> tt_store_;
  SolveReport<N> report_;
  std::optional<BitBoard<N>> attention_mask_;
  std::vector<bool> dag_has_capture_;
  std::unordered_map<uint64_t, CachedNodeFrontier> node_frontier_cache_;
  mutable std::unordered_map<std::string, bool> reval_cache_;
  uint64_t next_path_id_ = 1ULL;
  uint64_t live_frontier_children_cap_ = 0ULL;
  uint64_t live_dag_child_edges_ = 0ULL;
  size_t base_trace_len_ = 0;
  bool near_pn_continuation_claimed_ = false;
  uint64_t active_continuation_cap_nodes_ = 0ULL;
  bool has_time_limit_ = false;
  std::chrono::steady_clock::time_point solve_deadline_{};
  mutable bool time_limit_hit_ = false;
  mutable bool memory_budget_hit_ = false;
  mutable uint64_t reval_deadline_check_counter_ = 0ULL;
  mutable SolverStageProfile stage_profile_{};
  mutable ConvergenceTraceReport convergence_trace_{};
};

}  // namespace ldprover

#endif  // LDPROVER_SEARCH_DFPN_SOLVER_H_
