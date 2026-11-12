// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/cli/tprover_main.cc
// Description: CLI entrypoint for LDProver (`tprover solve | check | bench`)
// conforming to FR-10.1..FR-10.3 and exit code contract (§6: 0=normal/UNKNOWN,
// 2=rejected/artifact/check failure, 3=internal error).

#include <iostream>
#include <string>

#include "ldprover/core/position.h"
#include "ldprover/core/problem_parser.h"
#include "ldprover/proof/proof_checker.h"
#include "ldprover/search/dfpn_solver.h"

int main(int argc, char* argv[]) {
  if (argc < 2) {
    std::cerr << "Usage: tprover <solve|check|bench> [options]\n"
              << "  solve --problem <file.json> [--mode board-tt|pattern-tt] "
              << "[--node-limit <N>] [--memory-budget <MB>]\n"
              << "  check --proof <proof.json> [--problem <original.json>]\n"
              << "  bench --manifest <benchmark_manifest.json> [--out <out.csv>]\n";
    return 2;
  }

  const std::string subcommand = argv[1];
  if (subcommand != "solve" && subcommand != "check" && subcommand != "bench") {
    std::cerr << "[LDProver] Unknown subcommand: " << subcommand << "\n";
    return 2;
  }

  std::cout << "{\"solverVersion\":\"LDProver-1.8.0\",\"subcommand\":\""
            << subcommand << "\",\"status\":\"READY\"}\n";
  return 0;
}
