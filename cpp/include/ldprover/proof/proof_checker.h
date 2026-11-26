// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: include/ldprover/proof/proof_checker.h
// Description: Independent lproof/1 Proof DAG serializer, SGF variation tree
// generator (uct_tree_<problem>.sgf), and zero-search-shared ProofChecker
// (FR-8.1..FR-8.4, FR-9.1..FR-9.3).

#ifndef LDPROVER_PROOF_PROOF_CHECKER_H_
#define LDPROVER_PROOF_PROOF_CHECKER_H_

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "ldprover/core/position.h"
#include "ldprover/core/problem_parser.h"
#include "ldprover/core/types.h"
#include "ldprover/search/dfpn_solver.h"

namespace ldprover {

enum class VerificationScope : uint8_t {
  kOriginalRoot = 0,
  kTracedWithinRules = 1,
  kFreeExploration = 2,
};

enum class SubproofBindingPolicy : uint8_t {
  kStrictWhenRootProven = 0,
  kRequireBoundRootEdge = 1,
  kSemanticReplayOnly = 2,
};

struct VerificationReport {
  bool passed = false;
  std::string schema_version = "lproof/1";
  std::string jcs_sha256_checksum;
  std::string canonical_dag_checksum;
  std::string encoding_mode;
  std::string verified_scope;
  std::string verified_root_kind;
  std::string edge_binding_status = "not_applicable";
  bool edge_bound_to_root_dag = false;
  int32_t recorded_edge_dag_node_id = -1;
  std::string source_edge_binding_status = "not_applicable";
  bool source_edge_bound_to_root_dag = false;
  int32_t source_recorded_edge_dag_node_id = -1;
  bool semantic_replay_passed = false;
  bool trace_outside_region = false;
  bool trace_has_restricted_ko_capture = false;
  uint32_t verified_nodes = 0;
  uint32_t verified_states = 0;
  uint32_t verified_histories = 0;
  uint32_t replayed_pruned_certificates = 0;
  int32_t failed_node_id = -1;
  std::string error_code;
  std::string message;
};

template <int N = kDefaultBoardSize>
class ProofArtifactManager {
 public:
  ProofArtifactManager() = default;

  // FR-8.3: Serialize SolveReport into self-contained canonical lproof/1 JSON
  // DAG with post-order node IDs and RFC 8785 JCS FIPS 180-4 SHA-256 checksum.
  std::string SerializeLProofJson(const Position<N>& initial_pos,
                                  const ProofContext& context,
                                  const SolveReport<N>& report,
                                  std::string* out_checksum = nullptr) const;

  // FR-8.2: Generate SGF solution tree with RZ annotations.
  std::string ExportSolutionTreeSgf(const Position<N>& initial_pos,
                                    const ProofContext& context,
                                    const SolveReport<N>& report) const;

  // FR-9.1, FR-9.2, FR-9.3: Zero-trust Independent Proof Checker.
  // Replays every reachable state transition from `initial_pos`, verifies
  // SSK/PSK HistorySet, Benson UCA / token capture terminal evidence at leaves,
  // complete legal-move coverage at universal nodes, declared region membership
  // on every proof edge, top-level bestMove binding, and full recursive semantic
  // replay of OutsideRZRevalidated / TT certificates.
  VerificationReport VerifyProofDag(
      const Position<N>& initial_pos, const ProofContext& context,
      const SolveReport<N>& report,
      std::optional<VerificationScope> scope_override = std::nullopt) const;

  // Standalone process-independent verifier reconstructing initial Position<N>
  // (including traced sub-positions via zero-trust move replay), ProofContext,
  // full optional StateTable/HistoryTable/SnapshotPool, and SolveReport<N>
  // strictly from a serialized `.lproof.json` text payload, validating its
  // RFC 8785 JCS SHA-256 checksum, optional external problem binding
  // (`expected_problem`), explicit proposition scope (`scope_override`), and
  // full proof DAG.
  VerificationReport VerifyLProofJsonString(
      const std::string& json_text,
      const ParsedProblem<N>* expected_problem = nullptr,
      std::optional<VerificationScope> scope_override = std::nullopt) const;

  // Read-only zero-trust verification of subproof `target_dag_node_id` at
  // `rel_path_moves` from `solve_root_pos`. Does not mutate `report`.
  // Distinguishes original root-DAG edge ownership (`edge_bound_to_root_dag`,
  // `recorded_edge_dag_node_id`) from query-position semantic replay
  // (`semantic_replay_passed`):
  // - `kStrictWhenRootProven` (default): enforces recorded root-DAG edge
  //   identity when `report.root_status != kUnknown`; allows unbound semantic
  //   replay (`edge_binding_status = "unbound_unknown_root"`) on UNKNOWN roots.
  // - `kRequireBoundRootEdge`: fails if the original root DAG cannot bind the
  //   exact edge (`LP-U01` on UNKNOWN root, `LP-R02` on missing/mismatched edge).
  // - `kSemanticReplayOnly`: skips root-edge ownership enforcement to test
  //   whether `target_dag_node_id` proves `sub_pos`, setting
  //   `edge_bound_to_root_dag = false` and `"unbound_replay_only"`.
  VerificationReport VerifySubproofAtPath(
      const Position<N>& solve_root_pos, const ProofContext& context,
      const SolveReport<N>& report,
      const std::vector<int16_t>& rel_path_moves, uint32_t target_dag_node_id,
      SubproofBindingPolicy binding_policy =
          SubproofBindingPolicy::kStrictWhenRootProven) const;

  // Read-only verification of sibling RZ reuse: validates source proof at
  // `parent_rel_moves + source_move` (`source_dag_node_id`) according to
  // `source_binding_policy`, then replays `source_dag_node_id` semantically
  // against sibling `parent_rel_moves + query_move`.
  // Preserves source provenance separately (`source_edge_binding_status`,
  // `source_edge_bound_to_root_dag`, `source_recorded_edge_dag_node_id`) from
  // query-side replay (`edge_bound_to_root_dag = false`, `"unbound_replay_only"`):
  // - `kRequireBoundRootEdge` (default): requires proven root-DAG ownership
  //   of `source_move -> source_dag_node_id` (returns `LP-U01` on UNKNOWN root).
  // - `kStrictWhenRootProven` / `kSemanticReplayOnly`: allows explicit semantic
  //   diagnostics on UNKNOWN roots while keeping source provenance unbound.
  VerificationReport VerifySiblingQueryReplay(
      const Position<N>& solve_root_pos, const ProofContext& context,
      const SolveReport<N>& report,
      const std::vector<int16_t>& parent_rel_moves, int16_t source_move,
      uint32_t source_dag_node_id, int16_t query_move,
      SubproofBindingPolicy source_binding_policy =
          SubproofBindingPolicy::kRequireBoundRootEdge) const;
};

}  // namespace ldprover

#endif  // LDPROVER_PROOF_PROOF_CHECKER_H_
