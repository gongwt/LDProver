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

struct VerificationReport {
  bool passed = false;
  std::string schema_version = "lproof/1";
  std::string jcs_sha256_checksum;
  std::string canonical_dag_checksum;
  std::string encoding_mode;
  std::string verified_scope;
  std::string verified_root_kind;
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
  VerificationReport VerifyProofDag(const Position<N>& initial_pos,
                                    const ProofContext& context,
                                    const SolveReport<N>& report) const;

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
};

}  // namespace ldprover

#endif  // LDPROVER_PROOF_PROOF_CHECKER_H_
