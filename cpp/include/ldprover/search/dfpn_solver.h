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

#include <cstdint>
#include <limits>
#include <string>
#include <unordered_map>
#include <unordered_set>
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
  bool enable_rz_pruning = true;
  bool enable_pattern_tt = true;
  bool enable_fast_capture_ordering = true;
  bool enable_progressive_widening = true;
  uint32_t widening_base_k = 8;
  bool deterministic_mode = true;  // FR-7.8, NFR-4
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

 private:
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
    std::vector<int> crucial_lib_bonus;
    std::vector<int> enemy_min_lib;
    std::vector<int> friendly_min_lib;
    BitBoard<N> target_coords{};
  };

  bool IsMemoryBudgetExceeded(uint32_t active_depth) const noexcept;

  NodeTacticalContext BuildNodeTacticalContext(
      const Position<N>& pos, const ProofContext& context) const;

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

  // FR-4.10: Deterministic FastCapture tactical move ordering.
  int32_t ScoreMoveFastCapture(const Position<N>& pos,
                               const ProofContext& context,
                               const NodeTacticalContext& tctx,
                               int16_t move, bool is_or_node) const;

  // FR-5.5: Revalidate source proof under QueryState + HistorySet (both witness
  // and full-coverage AND/OR nodes) before materializing OutsideRZRevalidated.
  bool RevalidateSourceProofOnQueryState(
      const Position<N>& query_pos, const ProofContext& context,
      const std::optional<BitBoard<N>>& region_hint,
      uint32_t source_dag_node_id, ProofOutcome expected_outcome,
      uint32_t guard_depth = 0) const;

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
};

}  // namespace ldprover

#endif  // LDPROVER_SEARCH_DFPN_SOLVER_H_
