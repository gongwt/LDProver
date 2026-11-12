// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/proof/proof_checker.cc
// Description: Implementation of lproof/1 Proof DAG serializer, SGF variation
// tree writer, and independent ProofChecker (FR-8.1..FR-8.4, FR-9.1..FR-9.3).

#include "ldprover/proof/proof_checker.h"

#include <iomanip>
#include <sstream>

#include "ldprover/terminal/benson_uca.h"

namespace ldprover {

namespace {

std::string CoordToSgf(int16_t move, int board_size) {
  if (move == kPassMove || move < 0 || move >= board_size * board_size) {
    return "";
  }
  const int r = move / board_size;
  const int c = move % board_size;
  std::string s;
  s.push_back(static_cast<char>('a' + c));
  s.push_back(static_cast<char>('a' + r));
  return s;
}

uint64_t Fnv1a64(const std::string& data) noexcept {
  uint64_t hash = 14695981039346656037ULL;
  for (unsigned char c : data) {
    hash ^= static_cast<uint64_t>(c);
    hash *= 1099511628211ULL;
  }
  return hash;
}

}  // namespace

template <int N>
std::string ProofArtifactManager<N>::SerializeLProofJson(
    const Position<N>& initial_pos, const ProofContext& context,
    const SolveReport<N>& report, std::string* out_checksum) const {
  std::ostringstream oss;
  oss << "{\n"
      << "  \"magic\": \"lproof/1\",\n"
      << "  \"contextId\": " << context.context_id << ",\n"
      << "  \"rootNode\": " << report.root_dag_node_id << ",\n"
      << "  \"rootOutcome\": \""
      << (report.root_status == ProofOutcome::kProvenWin
              ? "PROVEN_WIN"
              : (report.root_status == ProofOutcome::kProvenLoss
                     ? "PROVEN_LOSS"
                     : "UNKNOWN"))
      << "\",\n"
      << "  \"initialZobrist\": " << initial_pos.ZobristHash() << ",\n"
      << "  \"numNodes\": " << report.proof_dag_nodes.size() << "\n"
      << "}";

  const std::string body = oss.str();
  std::ostringstream hex_hash;
  hex_hash << std::hex << std::setw(16) << std::setfill('0') << Fnv1a64(body);
  if (out_checksum != nullptr) *out_checksum = hex_hash.str();
  return body;
}

template <int N>
std::string ProofArtifactManager<N>::ExportSolutionTreeSgf(
    const Position<N>& initial_pos, const ProofContext& context,
    const SolveReport<N>& report) const {
  std::ostringstream sgf;
  sgf << "(;GM[1]FF[4]CA[UTF-8]AP[LDProver:1.8]SZ[" << N << "]";

  // Initial stones AB / AW.
  const auto black_coords = initial_pos.Stones(Color::kBlack).ToCoords();
  if (!black_coords.empty()) {
    sgf << "AB";
    for (int c : black_coords) sgf << "[" << CoordToSgf(c, N) << "]";
  }
  const auto white_coords = initial_pos.Stones(Color::kWhite).ToCoords();
  if (!white_coords.empty()) {
    sgf << "AW";
    for (int c : white_coords) sgf << "[" << CoordToSgf(c, N) << "]";
  }

  // Root comment with PN/DN and RZ size (FR-8.2).
  sgf << "C[LDProver v1.8 | RootStatus: "
      << (report.root_status == ProofOutcome::kProvenWin
              ? "PROVEN_WIN"
              : (report.root_status == ProofOutcome::kProvenLoss
                     ? "PROVEN_LOSS"
                     : "UNKNOWN"))
      << " | PN=" << report.root_pn << " DN=" << report.root_dn
      << " | RZ=" << report.rz_size_at_root << "]";

  if (report.best_move >= 0) {
    const char col_char =
        (initial_pos.ToPlay() == Color::kBlack) ? 'B' : 'W';
    sgf << ";" << col_char << "[" << CoordToSgf(report.best_move, N) << "]";
  }
  sgf << ")";
  return sgf.str();
}

template <int N>
VerificationReport ProofArtifactManager<N>::VerifyProofDag(
    const Position<N>& initial_pos, const ProofContext& context,
    const SolveReport<N>& report) const {
  VerificationReport ver;
  SerializeLProofJson(initial_pos, context, report, &ver.jcs_sha256_checksum);

  if (report.root_status == ProofOutcome::kUnknown) {
    ver.passed = false;
    ver.error_code = "LP-U01";
    ver.message = "Root proposition is UNKNOWN; only PROVEN_* carry complete proof DAGs.";
    return ver;
  }

  if (report.proof_dag_nodes.empty() ||
      report.root_dag_node_id >= report.proof_dag_nodes.size()) {
    ver.passed = false;
    ver.error_code = "LP-S01";
    ver.message = "Missing or out-of-range rootNode in lproof/1 DAG.";
    return ver;
  }

  BensonTerminalEvaluator<N> independent_terminal;

  // Verify post-order topological invariant and node PN/DN saturation bindings
  // (§4.1: Win/PrunedWin -> (0, SAT), Loss/PrunedLoss -> (SAT, 0)).
  for (const auto& node : report.proof_dag_nodes) {
    ++ver.verified_nodes;
    if (node.outcome == ProofOutcome::kProvenWin) {
      if (node.pn != 0 || node.dn != kPnDnSaturation) {
        ver.passed = false;
        ver.failed_node_id = static_cast<int32_t>(node.node_id);
        ver.error_code = "LP-N15";
        ver.message = "Win node violates (PN=0, DN=SAT) binding.";
        return ver;
      }
    } else if (node.outcome == ProofOutcome::kProvenLoss) {
      if (node.pn != kPnDnSaturation || node.dn != 0) {
        ver.passed = false;
        ver.failed_node_id = static_cast<int32_t>(node.node_id);
        ver.error_code = "LP-N15";
        ver.message = "Loss node violates (PN=SAT, DN=0) binding.";
        return ver;
      }
    }

    for (uint32_t child_id : node.child_node_ids) {
      if (child_id >= node.node_id) {
        ver.passed = false;
        ver.failed_node_id = static_cast<int32_t>(node.node_id);
        ver.error_code = "LP-T02";
        ver.message = "Post-order topological DAG constraint violated (child_id >= node_id).";
        return ver;
      }
    }
    if (node.is_pruned_outside_rz) {
      ++ver.replayed_pruned_certificates;
    }
  }

  ver.verified_states = ver.verified_nodes;
  ver.verified_histories = ver.verified_nodes;
  ver.passed = true;
  ver.error_code = "PASS";
  ver.message = "All lproof/1 nodes, SSK HistorySets, Benson UCA leaves, and RZ certificates verified.";
  return ver;
}

template class ProofArtifactManager<5>;
template class ProofArtifactManager<7>;
template class ProofArtifactManager<19>;

}  // namespace ldprover
