// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/rz/relevance_zone.cc
// Description: Dual-chain proof/disproof Relevance-Zone backpropagation
// (attacker influence closure + defender triple safety closure) per FR-5.2..FR-5.4.

#include "ldprover/rz/relevance_zone.h"

namespace ldprover {

template <int N>
ProofCertificateRZ<N> RelevanceZoneEngine<N>::ComputeSingleWitnessRZ(
    const Position<N>& parent_pos, int16_t witness_move,
    const ProofCertificateRZ<N>& child_rz) const {
  BitBoard<N> rz = child_rz.Bits();
  if (witness_move >= 0 && witness_move < N * N) {
    rz.Set(witness_move, true);
    for (int nb : parent_pos.OrthogonalNeighbors(witness_move)) {
      if (!parent_pos.ImmortalWall().Get(nb) &&
          parent_pos.StoneAt(nb) != Color::kEmpty &&
          (rz.Get(nb) || parent_pos.StoneAt(nb) != Color::kEmpty)) {
        BitBoard<N> libs;
        BitBoard<N> chain = parent_pos.FloodFillChain(nb, &libs);
        if ((chain & parent_pos.ImmortalWall()).None() &&
            (chain.Intersects(rz) || libs.Get(witness_move))) {
          rz |= chain | libs;
        }
      }
    }
  }

  // Expand non-immortal chains intersecting current RZ with their immediate liberties.
  BitBoard<N> expanded = rz;
  for (int coord : rz.ToCoords()) {
    if (parent_pos.StoneAt(coord) != Color::kEmpty &&
        !parent_pos.ImmortalWall().Get(coord)) {
      BitBoard<N> libs;
      BitBoard<N> chain = parent_pos.FloodFillChain(coord, &libs);
      if ((chain & parent_pos.ImmortalWall()).None()) {
        expanded |= chain | libs;
      }
    }
  }
  return ProofCertificateRZ<N>(expanded);
}

template <int N>
ProofCertificateRZ<N> RelevanceZoneEngine<N>::ComputeAllChildrenUnionRZ(
    const Position<N>& parent_pos,
    const std::vector<ProofCertificateRZ<N>>& children_rzs) const {
  BitBoard<N> union_bits;
  for (const auto& crz : children_rzs) {
    union_bits |= crz.Bits();
  }

  // Triple safety closure (FR-5.2), excluding immortal outer boundary walls:
  // 1. Include all non-immortal chains intersecting union_bits and their liberties.
  // 2. Include low-liberty orthogonal boundary chains adjacent to union_bits.
  // 3. Include active simple ko point if present.
  BitBoard<N> closed = union_bits;
  for (int coord : union_bits.ToCoords()) {
    if (parent_pos.StoneAt(coord) != Color::kEmpty &&
        !parent_pos.ImmortalWall().Get(coord)) {
      BitBoard<N> libs;
      BitBoard<N> chain = parent_pos.FloodFillChain(coord, &libs);
      if ((chain & parent_pos.ImmortalWall()).None()) {
        closed |= chain | libs;
      }
    }
    for (int nb : parent_pos.OrthogonalNeighbors(coord)) {
      if (parent_pos.StoneAt(nb) != Color::kEmpty &&
          !parent_pos.ImmortalWall().Get(nb)) {
        BitBoard<N> libs;
        BitBoard<N> nb_chain = parent_pos.FloodFillChain(nb, &libs);
        if ((nb_chain & parent_pos.ImmortalWall()).None() && libs.Count() <= 2) {
          closed |= nb_chain | libs;
        }
      }
    }
  }
  if (parent_pos.KoPoint() >= 0 && parent_pos.KoPoint() < N * N) {
    closed.Set(parent_pos.KoPoint(), true);
  }
  return ProofCertificateRZ<N>(closed);
}

template class RelevanceZoneEngine<5>;
template class RelevanceZoneEngine<7>;
template class RelevanceZoneEngine<19>;

}  // namespace ldprover
