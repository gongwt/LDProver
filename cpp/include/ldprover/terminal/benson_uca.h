// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: include/ldprover/terminal/benson_uca.h
// Description: Benson Unconditional Alive (UCA) theorem solver and four-valued
// TerminalEvaluator (FR-3.1..FR-3.9). Produces verifiable TerminalEvidence and
// leaf ProofCertificateRZ without static seki or surround-kill shortcuts.

#ifndef LDPROVER_TERMINAL_BENSON_UCA_H_
#define LDPROVER_TERMINAL_BENSON_UCA_H_

#include <cstdint>
#include <string>
#include <vector>

#include "ldprover/core/position.h"
#include "ldprover/core/types.h"

namespace ldprover {

template <int N = kDefaultBoardSize>
struct StoneChainInfo {
  uint16_t chain_id = 0;
  Color color = Color::kBlack;
  BitBoard<N> stones{};
  BitBoard<N> liberties{};
  std::vector<uint16_t> vital_eye_region_ids;
  bool is_uca_alive = false;
};

template <int N = kDefaultBoardSize>
struct EyeSpaceRegion {
  uint16_t region_id = 0;
  Color enclosing_color = Color::kBlack;
  BitBoard<N> empty_points{};
  BitBoard<N> enemy_stones{};
  std::vector<uint16_t> boundary_chain_ids;
  bool is_small_enclosed = false;
};

enum class EvidenceKind : uint8_t {
  kNone = 0,
  kBensonUca = 1,
  kTokensCaptured = 2,
  kDoublePassResolution = 3,
  kEmptyTargetConstantFalse = 4,
};

template <int N = kDefaultBoardSize>
struct TerminalEvaluationResult {
  TerminalStatus status = TerminalStatus::kNonTerminal;
  EvidenceKind evidence_kind = EvidenceKind::kNone;
  BitBoard<N> leaf_certificate_rz{};
  BitBoard<N> benson_alive_stones{};
  std::vector<uint16_t> proven_uca_chain_ids;
  std::string diagnostic_note;
};

template <int N = kDefaultBoardSize>
class BensonTerminalEvaluator {
 public:
  BensonTerminalEvaluator() = default;

  // FR-3.1: Runs Benson's greatest-fixpoint elimination for `color`.
  BitBoard<N> ComputeUnconditionalAlive(
      const Position<N>& pos, Color color,
      std::vector<StoneChainInfo<N>>* out_chains = nullptr,
      std::vector<EyeSpaceRegion<N>>* out_regions = nullptr,
      BitBoard<N>* out_vital_rz = nullptr) const;

  // FR-3.2, FR-3.3, FR-3.8: Unified four-valued terminal evaluation.
  // Evaluates relative to root proposition (attacker_goal) and generates
  // verifiable evidence + leaf ProofCertificateRZ.
  TerminalEvaluationResult<N> EvaluateTerminal(
      const Position<N>& pos, const ProofContext& context) const;
};

}  // namespace ldprover

#endif  // LDPROVER_TERMINAL_BENSON_UCA_H_
