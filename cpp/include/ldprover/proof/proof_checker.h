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
#include <string>
#include <vector>

#include "ldprover/core/position.h"
#include "ldprover/core/types.h"
#include "ldprover/search/dfpn_solver.h"

namespace ldprover {

struct VerificationReport {
  bool passed = false;
  std::string schema_version = "lproof/1";
  std::string jcs_sha256_checksum;
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

  // FR-8.3: Serialize SolveReport into canonical lproof/1 JSON DAG with
  // stateTable, historyTable, rzTable, post-order node IDs, and JCS checksum.
  std::string SerializeLProofJson(const Position<N>& initial_pos,
                                  const ProofContext& context,
                                  const SolveReport<N>& report,
                                  std::string* out_checksum = nullptr) const;

  // FR-8.2: Generate SGF solution tree with RZ color annotations
  // (Green = proof RZ, Red = winning move, Yellow = disproof RZ, Gray = pruned).
  std::string ExportSolutionTreeSgf(const Position<N>& initial_pos,
                                    const ProofContext& context,
                                    const SolveReport<N>& report) const;

  // FR-9.1, FR-9.2, FR-9.3: Independent Proof Checker.
  // Replays initialTrace, verifies every state transition, SSK/PSK HistorySet,
  // Benson UCA / token capture terminal evidence, AND full response coverage,
  // and OutsideRZRevalidated certificates without invoking search code.
  VerificationReport VerifyProofDag(const Position<N>& initial_pos,
                                    const ProofContext& context,
                                    const SolveReport<N>& report) const;
};

}  // namespace ldprover

#endif  // LDPROVER_PROOF_PROOF_CHECKER_H_
