// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/core/problem_parser.cc
// Description: Implementation of strict tsumego/*.json contract parser (FR-1.1..FR-1.3).

#include "ldprover/core/problem_parser.h"

namespace ldprover {

template <int N>
ParsedProblem<N> ProblemContractParser<N>::ParseTsumegoJson(
    const std::string& problem_id, const std::string& masked_sgf_str,
    const std::string& winning_color, const std::string& black_search_goal,
    const std::string& white_search_goal,
    const std::string& black_crucial_stone,
    const std::string& white_crucial_stone, const std::string& turn_color,
    TurnConflictPolicy conflict_policy) const {
  ParsedProblem<N> out;
  out.problem_id = problem_id;

  if (masked_sgf_str.empty() || winning_color.empty()) {
    out.valid = false;
    out.error_code = "FR1-MISSING-REQUIRED";
    out.error_message = "Required fields masked_sgf_str or winning_color missing.";
    return out;
  }

  // FR-1.3: Reject mixed '&' and '|' in crucial_stone expressions.
  const std::string& target_expr =
      (winning_color == "B") ? black_crucial_stone : white_crucial_stone;
  if (target_expr.find('&') != std::string::npos &&
      target_expr.find('|') != std::string::npos) {
    out.valid = false;
    out.error_code = "FR1-MIXED-LOGICAL-OP";
    out.error_message =
        "Mixed '&' and '|' operators inside crucial_stone are forbidden (FR-1.3).";
    return out;
  }

  // Determine SGF PL property (FR-1.2: never insert pass to fix turn conflict).
  Color sgf_pl = Color::kBlack;
  if (masked_sgf_str.find("PL[W]") != std::string::npos) {
    sgf_pl = Color::kWhite;
  } else if (masked_sgf_str.find("PL[B]") != std::string::npos) {
    sgf_pl = Color::kBlack;
  }

  if (!turn_color.empty()) {
    const Color meta_turn = (turn_color == "W") ? Color::kWhite : Color::kBlack;
    if (meta_turn != sgf_pl) {
      if (conflict_policy == TurnConflictPolicy::kRejectStrict) {
        out.valid = false;
        out.error_code = "FR1-TURN-CONFLICT";
        out.error_message =
            "turn_color conflicts with SGF PL; rejected under strict policy (FR-1.2).";
        return out;
      }
      out.warning_message =
          "turn_color conflicts with SGF PL; using SGF PL under warn_ignore.";
    }
  }

  out.proof_context.root_attacker =
      (winning_color == "W") ? Color::kWhite : Color::kBlack;
  const std::string& active_goal =
      (winning_color == "W") ? white_search_goal : black_search_goal;
  out.proof_context.attacker_goal =
      (active_goal == "TOKILL") ? SearchGoal::kToKill : SearchGoal::kToLive;

  if (target_expr.find('&') != std::string::npos) {
    out.proof_context.crucial_stone_op = LogicalOp::kConjunction;
  } else if (target_expr.find('|') != std::string::npos) {
    out.proof_context.crucial_stone_op = LogicalOp::kDisjunction;
  } else {
    out.proof_context.crucial_stone_op = LogicalOp::kSingle;
  }

  out.initial_position.Clear(out.proof_context);
  out.initial_position.FinalizeInitialPosition(sgf_pl);
  out.valid = true;
  return out;
}

template class ProblemContractParser<5>;
template class ProblemContractParser<7>;
template class ProblemContractParser<19>;

}  // namespace ldprover
