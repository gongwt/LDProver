// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: include/ldprover/rz/relevance_zone.h
// Description: Type-isolated Relevance-Zone (RZ) mechanisms (FR-5.1..FR-5.7):
// ProblemSearchMask, NNAttentionMask, ProofCertificateRZ, dual-chain
// proof/disproof RZ backpropagation, and OutsideRZRevalidated null-move
// pruning certificate verification.

#ifndef LDPROVER_RZ_RELEVANCE_ZONE_H_
#define LDPROVER_RZ_RELEVANCE_ZONE_H_

#include <cstdint>
#include <string>
#include <vector>

#include "ldprover/core/position.h"
#include "ldprover/core/types.h"

namespace ldprover {

// FR-5.1: Strongly-typed spatial masks; implicit conversion is forbidden.
template <int N = kDefaultBoardSize>
class ProblemSearchMask {
 public:
  explicit constexpr ProblemSearchMask(const BitBoard<N>& bits = {}) noexcept
      : bits_(bits) {}
  const BitBoard<N>& Bits() const noexcept { return bits_; }

 private:
  BitBoard<N> bits_;
};

template <int N = kDefaultBoardSize>
class NNAttentionMask {
 public:
  explicit constexpr NNAttentionMask(const BitBoard<N>& bits = {}) noexcept
      : bits_(bits) {}
  const BitBoard<N>& Bits() const noexcept { return bits_; }

 private:
  BitBoard<N> bits_;
};

template <int N = kDefaultBoardSize>
class ProofCertificateRZ {
 public:
  explicit constexpr ProofCertificateRZ(const BitBoard<N>& bits = {}) noexcept
      : bits_(bits) {}
  const BitBoard<N>& Bits() const noexcept { return bits_; }
  bool Contains(int coord) const noexcept {
    if (coord < 0 || coord >= N * N) return false;
    return bits_.Get(coord);
  }
  int Size() const noexcept { return bits_.Count(); }

  // FR-5.4: Monotonic union update.
  void UnionWith(const ProofCertificateRZ<N>& other) noexcept {
    bits_ |= other.bits_;
  }
  void UnionBits(const BitBoard<N>& more_bits) noexcept { bits_ |= more_bits; }

 private:
  BitBoard<N> bits_;
};

// FR-5.5, FR-5.6: Self-contained PrunedCertificate requiring QueryState +
// HistorySet source proof replay revalidation ("OutsideRZRevalidated").
template <int N = kDefaultBoardSize>
struct PrunedCertificate {
  uint32_t query_state_id = 0;
  uint32_t query_history_id = 0;
  uint32_t source_state_id = 0;
  uint32_t source_history_id = 0;
  uint32_t source_proof_node_id = 0;
  uint64_t context_id = 0;
  int16_t pruned_move = kPassMove;
  int16_t representative_move = kPassMove;
  ProofCertificateRZ<N> certificate_rz{};
  std::string reason = "OutsideRZRevalidated";
};

template <int N = kDefaultBoardSize>
class RelevanceZoneEngine {
 public:
  RelevanceZoneEngine() = default;

  // FR-5.2 (A) & FR-5.3 (B'): Proving-side / Disproving-side single winning
  // witness move influence closure (intersection expansion, liberty closure,
  // shared liberties of adjacent chains).
  ProofCertificateRZ<N> ComputeSingleWitnessRZ(
      const Position<N>& parent_pos, int16_t witness_move,
      const ProofCertificateRZ<N>& child_rz) const;

  // FR-5.2 (B) & FR-5.3 (A'): Opponent all-moves union + triple safety closure
  // (suicide prevention, opponent boundary liberties, superko legalization).
  ProofCertificateRZ<N> ComputeAllChildrenUnionRZ(
      const Position<N>& parent_pos,
      const std::vector<ProofCertificateRZ<N>>& children_rzs) const;

  // FR-5.5: Candidate filter: move is outside certificate_rz.
  // Note: Outside RZ is strictly a candidate condition; actual Pruned*
  // conclusion requires QueryState + HistorySet replay verification.
  bool IsOutsideRZCandidate(int16_t move,
                            const ProofCertificateRZ<N>& cert_rz) const noexcept {
    if (move == kPassMove) return false;
    return !cert_rz.Contains(move);
  }
};

}  // namespace ldprover

#endif  // LDPROVER_RZ_RELEVANCE_ZONE_H_
