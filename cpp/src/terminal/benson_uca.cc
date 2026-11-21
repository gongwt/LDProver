// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/terminal/benson_uca.cc
// Description: Implementation of Benson's Unconditional Alive (UCA) algorithm
// and unified four-valued EvaluateTerminal() (FR-3.1..FR-3.9).

#include "ldprover/terminal/benson_uca.h"

#include <algorithm>
#include <queue>
#include <set>

namespace ldprover {

template <int N>
BitBoard<N> BensonTerminalEvaluator<N>::ComputeUnconditionalAlive(
    const Position<N>& pos, Color color,
    std::vector<StoneChainInfo<N>>* out_chains,
    std::vector<EyeSpaceRegion<N>>* out_regions,
    BitBoard<N>* out_vital_rz,
    const BitBoard<N>* target_anchor_mask) const {
  std::vector<StoneChainInfo<N>> chains;
  std::vector<EyeSpaceRegion<N>> regions;
  BitBoard<N> visited_stones;

  // Step 1: Extract all stone chains of `color`.
  for (int coord = 0; coord < N * N; ++coord) {
    if (pos.StoneAt(coord) == color && !visited_stones.Get(coord)) {
      BitBoard<N> libs;
      BitBoard<N> stones = pos.FloodFillChain(coord, &libs);
      visited_stones |= stones;
      StoneChainInfo<N> info;
      info.chain_id = static_cast<uint16_t>(chains.size());
      info.color = color;
      info.stones = stones;
      info.liberties = libs;
      chains.push_back(info);
    }
  }

  std::vector<bool> is_immortal_chain(chains.size(), false);
  for (size_t i = 0; i < chains.size(); ++i) {
    is_immortal_chain[i] = (chains[i].stones & pos.ImmortalWall()).Any();
  }

  // Step 2: Partition complement of `color` stones into connected regions.
  BitBoard<N> visited_complement = pos.Stones(color);
  for (int coord = 0; coord < N * N; ++coord) {
    if (visited_complement.Get(coord)) continue;
    EyeSpaceRegion<N> reg;
    reg.region_id = static_cast<uint16_t>(regions.size());
    reg.enclosing_color = color;

    std::queue<int> q;
    q.push(coord);
    visited_complement.Set(coord, true);
    std::set<uint16_t> boundary_chains;

    while (!q.empty()) {
      const int cur = q.front();
      q.pop();
      if (pos.StoneAt(cur) == Color::kEmpty) {
        reg.empty_points.Set(cur, true);
      } else {
        reg.enemy_stones.Set(cur, true);
      }

      for (int nb : pos.OrthogonalNeighbors(cur)) {
        if (pos.StoneAt(nb) == color) {
          for (const auto& ch : chains) {
            if (ch.stones.Get(nb)) {
              boundary_chains.insert(ch.chain_id);
              break;
            }
          }
        } else if (!visited_complement.Get(nb)) {
          visited_complement.Set(nb, true);
          q.push(nb);
        }
      }
    }

    reg.boundary_chain_ids.assign(boundary_chains.begin(),
                                  boundary_chains.end());
    const bool touches_immortal_enemy =
        (reg.enemy_stones & pos.ImmortalWall()).Any();
    bool touches_tactical_chain = false;
    for (uint16_t cid : reg.boundary_chain_ids) {
      if (!is_immortal_chain[cid]) {
        touches_tactical_chain = true;
        break;
      }
    }

    // Pure Classic Benson (1976) under Local Tsumego Boundary Axiom:
    // region cannot contain immortal outer-wall enemy stones (`ImmortalWall`)
    // and contributes at most 1 vital region when enclosed by active chains.
    reg.is_small_enclosed = !touches_immortal_enemy &&
                            touches_tactical_chain &&
                            reg.empty_points.Any() &&
                            !reg.boundary_chain_ids.empty();
    regions.push_back(reg);
  }

  // Step 3: Classic Benson (1976) greatest-fixpoint elimination loop.
  std::set<uint16_t> active_chains;
  std::set<uint16_t> active_regions;
  for (const auto& ch : chains) active_chains.insert(ch.chain_id);
  for (const auto& reg : regions) {
    if (reg.is_small_enclosed) active_regions.insert(reg.region_id);
  }

  bool changed = true;
  while (changed) {
    changed = false;

    // 3a. Eliminate regions whose boundary chains are not all active.
    std::vector<uint16_t> regions_to_drop;
    for (uint16_t rid : active_regions) {
      const auto& reg = regions[rid];
      for (uint16_t cid : reg.boundary_chain_ids) {
        if (active_chains.find(cid) == active_chains.end()) {
          regions_to_drop.push_back(rid);
          break;
        }
      }
    }
    for (uint16_t rid : regions_to_drop) {
      active_regions.erase(rid);
      changed = true;
    }

    // 3b. Recompute vital regions for each non-immortal active chain; drop if < 2.
    std::vector<uint16_t> chains_to_drop;
    for (uint16_t cid : active_chains) {
      if (is_immortal_chain[cid]) continue;
      auto& ch = chains[cid];
      ch.vital_eye_region_ids.clear();
      for (uint16_t rid : active_regions) {
        const auto& reg = regions[rid];
        // A region R is vital to chain X iff every empty point in R is an
        // orthogonal liberty of X (strictly 1 vital eye contribution per region).
        if (reg.empty_points.IsSubsetOf(ch.liberties)) {
          ch.vital_eye_region_ids.push_back(rid);
        }
      }
      if (ch.vital_eye_region_ids.size() < 2) {
        chains_to_drop.push_back(cid);
      }
    }
    for (uint16_t cid : chains_to_drop) {
      active_chains.erase(cid);
      changed = true;
    }
  }

  BitBoard<N> uca_stones;
  BitBoard<N> vital_rz;
  for (uint16_t cid : active_chains) {
    chains[cid].is_uca_alive = true;
    uca_stones |= chains[cid].stones;
  }

  // Minimal target-anchored vital_rz (excludes unrelated alive chains & outer immortal walls).
  std::vector<uint16_t> rz_queue;
  std::vector<bool> visited_rz_chain(chains.size(), false);
  if (target_anchor_mask != nullptr && target_anchor_mask->Any()) {
    for (uint16_t cid : active_chains) {
      if ((chains[cid].stones & *target_anchor_mask).Any() &&
          !visited_rz_chain[cid]) {
        visited_rz_chain[cid] = true;
        rz_queue.push_back(cid);
      }
    }
  }
  if (rz_queue.empty()) {
    for (uint16_t cid : active_chains) {
      if (!is_immortal_chain[cid] && !visited_rz_chain[cid]) {
        visited_rz_chain[cid] = true;
        rz_queue.push_back(cid);
      }
    }
  }

  for (size_t q_idx = 0; q_idx < rz_queue.size(); ++q_idx) {
    const uint16_t cid = rz_queue[q_idx];
    if (!is_immortal_chain[cid]) {
      vital_rz |= chains[cid].stones;
    }
    for (uint16_t rid : chains[cid].vital_eye_region_ids) {
      const auto& reg = regions[rid];
      vital_rz |= reg.empty_points;
      vital_rz |= reg.enemy_stones;
      const BitBoard<N> reg_area = reg.empty_points | reg.enemy_stones;
      for (uint16_t bcid : reg.boundary_chain_ids) {
        if (!is_immortal_chain[bcid]) {
          if (!visited_rz_chain[bcid]) {
            visited_rz_chain[bcid] = true;
            rz_queue.push_back(bcid);
          }
        } else {
          // Include only immortal boundary stones directly adjacent to the vital region.
          for (int pt : reg_area.ToCoords()) {
            for (int nb : pos.OrthogonalNeighbors(pt)) {
              if (chains[bcid].stones.Get(nb)) {
                vital_rz.Set(nb, true);
              }
            }
          }
        }
      }
    }
  }

  if (out_chains != nullptr) *out_chains = std::move(chains);
  if (out_regions != nullptr) *out_regions = std::move(regions);
  if (out_vital_rz != nullptr) *out_vital_rz = vital_rz;
  return uca_stones;
}

template <int N>
TerminalEvaluationResult<N> BensonTerminalEvaluator<N>::EvaluateTerminal(
    const Position<N>& pos, const ProofContext& context) const {
  TerminalEvaluationResult<N> res;

  // FR-1.3: Empty target token specification evaluates to constant false.
  if (context.initial_tokens.empty()) {
    res.status = (context.attacker_goal == SearchGoal::kToLive)
                     ? TerminalStatus::kLoss
                     : TerminalStatus::kWin;
    res.evidence_kind = EvidenceKind::kEmptyTargetConstantFalse;
    res.diagnostic_note = "Empty crucial_stone expression evaluates to false";
    return res;
  }

  // Pre-check surviving target tokens and 2-liberty Benson precondition before full UCA.
  const uint64_t surviving_mask = pos.SurvivingTargetTokensMask();
  uint8_t max_group = 0;
  for (const auto& tok : context.initial_tokens) {
    max_group = std::max(max_group, tok.group_index);
  }

  std::vector<bool> group_has_surviving_token(max_group + 1, false);
  std::vector<bool> group_has_two_lib_token(max_group + 1, false);
  BitBoard<N> target_chains_rz;
  BitBoard<N> target_anchor_mask;

  for (size_t i = 0; i < context.initial_tokens.size() && i < 64; ++i) {
    const auto& tok = context.initial_tokens[i];
    if ((surviving_mask & (1ULL << i)) != 0 &&
        pos.StoneAt(tok.initial_coord) == tok.stone_color) {
      group_has_surviving_token[tok.group_index] = true;
      target_anchor_mask.Set(tok.initial_coord, true);
      BitBoard<N> libs;
      BitBoard<N> ch = pos.FloodFillChain(tok.initial_coord, &libs);
      target_chains_rz |= ch | libs;
      if (libs.Count() >= 2 || pos.ImmortalWall().Get(tok.initial_coord)) {
        group_has_two_lib_token[tok.group_index] = true;
      }
    } else {
      target_chains_rz.Set(tok.initial_coord, true);
    }
  }

  bool target_all_captured = false;
  bool can_satisfy_benson = false;
  if (context.crucial_stone_op == LogicalOp::kConjunction) {
    target_all_captured = false;
    can_satisfy_benson = true;
    for (uint8_t g = 0; g <= max_group; ++g) {
      if (!group_has_surviving_token[g]) target_all_captured = true;
      if (!group_has_two_lib_token[g]) can_satisfy_benson = false;
    }
  } else {
    target_all_captured = true;
    can_satisfy_benson = false;
    for (uint8_t g = 0; g <= max_group; ++g) {
      if (group_has_surviving_token[g]) target_all_captured = false;
      if (group_has_two_lib_token[g]) can_satisfy_benson = true;
    }
  }

  // O(1) fast path: captured crucial tokens cannot satisfy Benson UCA.
  if (target_all_captured) {
    res.status = (context.attacker_goal == SearchGoal::kToLive)
                     ? TerminalStatus::kLoss
                     : TerminalStatus::kWin;
    res.evidence_kind = EvidenceKind::kTokensCaptured;
    res.leaf_certificate_rz = target_chains_rz;
    res.diagnostic_note = "Target crucial_stone tokens captured";
    return res;
  }

  const Color target_color = context.initial_tokens.front().stone_color;
  std::vector<StoneChainInfo<N>> chains;
  std::vector<EyeSpaceRegion<N>> regions;
  BitBoard<N> vital_rz;
  BitBoard<N> uca_stones;
  if (can_satisfy_benson) {
    uca_stones = ComputeUnconditionalAlive(
        pos, target_color, &chains, &regions, &vital_rz, &target_anchor_mask);
  }
  res.benson_alive_stones = uca_stones;

  std::vector<bool> group_has_uca_token(max_group + 1, false);
  if (uca_stones.Any()) {
    for (size_t i = 0; i < context.initial_tokens.size() && i < 64; ++i) {
      const auto& tok = context.initial_tokens[i];
      if ((surviving_mask & (1ULL << i)) != 0 &&
          pos.StoneAt(tok.initial_coord) == tok.stone_color &&
          uca_stones.Get(tok.initial_coord)) {
        group_has_uca_token[tok.group_index] = true;
      }
    }
  }

  bool target_uca_satisfied = false;
  if (context.crucial_stone_op == LogicalOp::kConjunction) {
    target_uca_satisfied = true;
    for (uint8_t g = 0; g <= max_group; ++g) {
      if (!group_has_uca_token[g]) target_uca_satisfied = false;
    }
  } else {
    target_uca_satisfied = false;
    for (uint8_t g = 0; g <= max_group; ++g) {
      if (group_has_uca_token[g]) target_uca_satisfied = true;
    }
  }

  // Case 1: Target stones achieved Classic Benson UCA.
  if (target_uca_satisfied) {
    res.status = (context.attacker_goal == SearchGoal::kToLive)
                     ? TerminalStatus::kWin
                     : TerminalStatus::kLoss;
    res.evidence_kind = EvidenceKind::kBensonUca;
    res.leaf_certificate_rz = vital_rz | target_chains_rz;
    for (const auto& ch : chains) {
      if (ch.is_uca_alive) res.proven_uca_chain_ids.push_back(ch.chain_id);
    }
    res.diagnostic_note = "Classic Benson (1976) UCA greatest-fixpoint satisfied";
    return res;
  }

  // Case 2: Target tokens irreversibly captured (FR-2.6, FR-3.2).
  if (target_all_captured) {
    res.status = (context.attacker_goal == SearchGoal::kToLive)
                     ? TerminalStatus::kLoss
                     : TerminalStatus::kWin;
    res.evidence_kind = EvidenceKind::kTokensCaptured;
    res.leaf_certificate_rz = target_chains_rz;
    res.diagnostic_note = "Target crucial_stone tokens captured";
    return res;
  }

  // Case 3: FR-3.8 Double-pass terminal resolution (strictly checks UCA!).
  if (pos.IsAtDoublePass()) {
    const bool live_holds = target_uca_satisfied;
    if (context.attacker_goal == SearchGoal::kToLive) {
      res.status = live_holds ? TerminalStatus::kWin : TerminalStatus::kLoss;
    } else {
      res.status = live_holds ? TerminalStatus::kLoss : TerminalStatus::kWin;
    }
    res.evidence_kind = EvidenceKind::kDoublePassResolution;
    res.leaf_certificate_rz = target_chains_rz;
    res.diagnostic_note = "Double-pass terminal resolution";
    return res;
  }

  res.status = TerminalStatus::kNonTerminal;
  res.leaf_certificate_rz = target_chains_rz;
  return res;
}

template class BensonTerminalEvaluator<5>;
template class BensonTerminalEvaluator<7>;
template class BensonTerminalEvaluator<19>;

}  // namespace ldprover
