// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: include/ldprover/core/problem_parser.h
// Description: Strict tsumego/*.json contract parser (FR-1.1..FR-1.3).
// Rejects malformed inputs with structured error codes; never silently defaults.

#ifndef LDPROVER_CORE_PROBLEM_PARSER_H_
#define LDPROVER_CORE_PROBLEM_PARSER_H_

#include <optional>
#include <string>

#include "ldprover/core/position.h"
#include "ldprover/core/types.h"

namespace ldprover {

enum class TurnConflictPolicy : uint8_t {
  kRejectStrict = 0,  // Default (FR-1.2): reject if turn_color != SGF PL
  kWarnIgnore = 1,    // turn_conflict_policy=warn_ignore: use SGF PL + warning
};

template <int N = kDefaultBoardSize>
struct ParsedProblem {
  bool valid = false;
  std::string error_code;
  std::string error_message;
  std::string warning_message;
  std::string problem_id;
  Position<N> initial_position{};
  ProofContext proof_context{};
  std::optional<BitBoard<N>> region_search_mask;
};

template <int N = kDefaultBoardSize>
class ProblemContractParser {
 public:
  ProblemContractParser() = default;

  // FR-1.1, FR-1.2, FR-1.3: Parse masked_sgf_str, winning_color, search_goal,
  // crucial_stone, and optional turn_color / ko_rule / region.
  // Never inserts synthetic pass moves on turn_color conflict.
  ParsedProblem<N> ParseTsumegoJson(
      const std::string& problem_id, const std::string& masked_sgf_str,
      const std::string& winning_color, const std::string& black_search_goal,
      const std::string& white_search_goal,
      const std::string& black_crucial_stone,
      const std::string& white_crucial_stone,
      const std::string& turn_color = "",
      TurnConflictPolicy conflict_policy =
          TurnConflictPolicy::kRejectStrict) const;
};

}  // namespace ldprover

#endif  // LDPROVER_CORE_PROBLEM_PARSER_H_
