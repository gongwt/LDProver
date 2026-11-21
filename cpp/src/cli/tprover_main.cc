// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/cli/tprover_main.cc
// Description: CLI entrypoint for LDProver (`tprover solve | check | bench`)
// conforming to FR-10.1..FR-10.3 and exit code contract (§6: 0=normal/UNKNOWN,
// 2=rejected/missing file/artifact/check failure, 3=internal error).

#include <cctype>
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>
#include <vector>

#include "ldprover/core/position.h"
#include "ldprover/core/problem_parser.h"
#include "ldprover/proof/proof_checker.h"
#include "ldprover/search/dfpn_solver.h"

namespace {

bool ReadEntireFile(const std::string& path, std::string* out) {
  std::ifstream ifs(path, std::ios::in | std::ios::binary);
  if (!ifs.is_open()) return false;
  std::ostringstream ss;
  ss << ifs.rdbuf();
  if (ifs.bad()) return false;
  *out = ss.str();
  return true;
}

bool WriteEntireFile(const std::string& path, const std::string& content) {
  std::ofstream ofs(path, std::ios::out | std::ios::binary | std::ios::trunc);
  if (!ofs.is_open()) return false;
  ofs << content;
  return ofs.good();
}

std::string BasenameStem(const std::string& path) {
  const size_t slash = path.find_last_of("/\\");
  std::string name = (slash == std::string::npos) ? path : path.substr(slash + 1U);
  const size_t dot = name.find_last_of('.');
  if (dot != std::string::npos) name = name.substr(0U, dot);
  return name.empty() ? "problem" : name;
}

int DetectBoardSizeFromProofJson(const std::string& json_text) {
  const std::string key = "\"boardSize\"";
  const size_t pos = json_text.find(key);
  if (pos == std::string::npos) return 19;
  size_t cur = pos + key.size();
  while (cur < json_text.size() &&
         (std::isspace(static_cast<unsigned char>(json_text[cur])) ||
          json_text[cur] == ':')) {
    ++cur;
  }
  int val = 0;
  while (cur < json_text.size() &&
         std::isdigit(static_cast<unsigned char>(json_text[cur]))) {
    val = val * 10 + static_cast<int>(json_text[cur] - '0');
    ++cur;
  }
  return (val == 5 || val == 7 || val == 19) ? val : -1;
}

std::vector<std::string> ParseJsonStringArray(const std::string& json_text) {
  std::vector<std::string> items;
  size_t cur = 0;
  while (cur < json_text.size() && json_text[cur] != '[') ++cur;
  if (cur >= json_text.size()) return items;
  ++cur;
  while (cur < json_text.size()) {
    while (cur < json_text.size() &&
           (std::isspace(static_cast<unsigned char>(json_text[cur])) ||
            json_text[cur] == ',')) {
      ++cur;
    }
    if (cur >= json_text.size() || json_text[cur] == ']') break;
    if (json_text[cur] != '"') return {};
    ++cur;
    std::string s;
    while (cur < json_text.size() && json_text[cur] != '"') {
      if (json_text[cur] == '\\' && cur + 1U < json_text.size()) {
        ++cur;
      }
      s.push_back(json_text[cur++]);
    }
    if (cur >= json_text.size() || json_text[cur] != '"') return {};
    ++cur;
    items.push_back(s);
  }
  return items;
}

std::string OutcomeLabel(ldprover::ProofOutcome outcome) {
  if (outcome == ldprover::ProofOutcome::kProvenWin) return "PROVEN_WIN";
  if (outcome == ldprover::ProofOutcome::kProvenLoss) return "PROVEN_LOSS";
  return "UNKNOWN";
}

std::string UnknownReasonLabel(ldprover::UnknownReason reason) {
  switch (reason) {
    case ldprover::UnknownReason::kNone:
      return "none";
    case ldprover::UnknownReason::kTimeout:
      return "timeout";
    case ldprover::UnknownReason::kKoDependent:
      return "ko_dependent";
    case ldprover::UnknownReason::kCycle:
      return "cycle";
    case ldprover::UnknownReason::kNodeLimit:
      return "node_limit";
    case ldprover::UnknownReason::kDepthLimit:
      return "depth_limit";
    case ldprover::UnknownReason::kMemoryBudget:
      return "memory_budget";
    case ldprover::UnknownReason::kWideningStalled:
      return "widening_stalled";
    case ldprover::UnknownReason::kInternalError:
      return "internal_error";
  }
  return "none";
}

bool ParseStrictPositiveDouble(const char* raw, double* out_val) {
  if (raw == nullptr || *raw == '\0') return false;
  char* endptr = nullptr;
  const double v = std::strtod(raw, &endptr);
  if (endptr == raw || *endptr != '\0') return false;
  if (!std::isfinite(v) || v <= 0.0) return false;
  *out_val = v;
  return true;
}

bool ParseStrictPositiveU32(const char* raw, uint32_t* out_val) {
  if (raw == nullptr || *raw == '\0' || raw[0] == '-') return false;
  char* endptr = nullptr;
  const unsigned long v = std::strtoul(raw, &endptr, 10);
  if (endptr == raw || *endptr != '\0' || v == 0UL || v > 0xFFFFFFFFUL) {
    return false;
  }
  *out_val = static_cast<uint32_t>(v);
  return true;
}

int RunSolveCommand(int argc, char* argv[]) {
  std::string problem_path;
  std::string out_proof_path;
  std::string out_sgf_path;
  ldprover::SolverConfig config;

  for (int i = 2; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--problem" && i + 1 < argc) {
      problem_path = argv[++i];
    } else if (arg == "--out-proof" && i + 1 < argc) {
      out_proof_path = argv[++i];
    } else if (arg == "--out-sgf" && i + 1 < argc) {
      out_sgf_path = argv[++i];
    } else if (arg == "--mode" && i + 1 < argc) {
      const std::string mode = argv[++i];
      if (mode == "board-tt") {
        config.enable_pattern_tt = false;
      } else if (mode == "pattern-tt") {
        config.enable_pattern_tt = true;
      } else {
        std::cerr << "[LDProver] Invalid --mode: " << mode << "\n";
        return 2;
      }
    } else if (arg == "--node-limit" && i + 1 < argc) {
      if (!ParseStrictPositiveU32(argv[++i], &config.max_nodes)) {
        std::cerr << "[LDProver] Invalid positive integer for --node-limit\n";
        return 2;
      }
    } else if (arg == "--max-depth" && i + 1 < argc) {
      if (!ParseStrictPositiveU32(argv[++i], &config.max_depth)) {
        std::cerr << "[LDProver] Invalid positive integer for --max-depth\n";
        return 2;
      }
    } else if (arg == "--widening-base-k" && i + 1 < argc) {
      if (!ParseStrictPositiveU32(argv[++i], &config.widening_base_k)) {
        std::cerr
            << "[LDProver] Invalid positive integer for --widening-base-k\n";
        return 2;
      }
    } else if (arg == "--memory-budget" && i + 1 < argc) {
      double mb = 0.0;
      if (!ParseStrictPositiveDouble(argv[++i], &mb)) {
        std::cerr << "[LDProver] Invalid positive number (MiB) for "
                     "--memory-budget\n";
        return 2;
      }
      const double bytes_d = std::floor(mb * 1024.0 * 1024.0);
      config.memory_budget_bytes =
          (bytes_d < 1.0) ? 1ULL : static_cast<uint64_t>(bytes_d);
    } else {
      std::cerr << "[LDProver] Unknown or incomplete solve option: " << arg
                << "\n";
      return 2;
    }
  }

  if (problem_path.empty()) {
    std::cerr << "[LDProver] Missing required --problem <file.json>\n";
    return 2;
  }

  std::string raw_json;
  if (!ReadEntireFile(problem_path, &raw_json)) {
    std::cerr << "[LDProver] Cannot read problem file: " << problem_path << "\n";
    return 2;
  }

  ldprover::ProblemContractParser<19> parser;
  const std::string prob_id = BasenameStem(problem_path);
  const auto parsed = parser.ParseTsumegoJsonObject(prob_id, raw_json);
  if (!parsed.valid) {
    std::cerr << "{\"problemId\":\"" << prob_id << "\",\"valid\":false,"
              << "\"errorCode\":\"" << parsed.error_code << "\","
              << "\"message\":\"" << parsed.error_message << "\"}\n";
    return 2;
  }

  ldprover::DfpnSolver<19> solver(config);
  const auto report = solver.Solve(parsed.initial_position, parsed.proof_context,
                                   parsed.region_search_mask, prob_id);

  ldprover::ProofArtifactManager<19> artifacts;
  std::string checker_code = "SKIPPED_UNKNOWN";
  if (report.root_status != ldprover::ProofOutcome::kUnknown) {
    const auto ver = artifacts.VerifyProofDag(
        parsed.initial_position, parsed.proof_context, report);
    checker_code = ver.error_code;
    if (!ver.passed) {
      std::cerr << "[LDProver] Proof verification failed (" << ver.error_code
                << "): " << ver.message << "\n";
      return 2;
    }
  }

  std::string checksum;
  const std::string proof_json = artifacts.SerializeLProofJson(
      parsed.initial_position, parsed.proof_context, report, &checksum);

  if (!out_proof_path.empty() && !WriteEntireFile(out_proof_path, proof_json)) {
    std::cerr << "[LDProver] Failed to write proof file: " << out_proof_path
              << "\n";
    return 2;
  }
  if (!out_sgf_path.empty()) {
    const std::string sgf = artifacts.ExportSolutionTreeSgf(
        parsed.initial_position, parsed.proof_context, report);
    if (!WriteEntireFile(out_sgf_path, sgf)) {
      std::cerr << "[LDProver] Failed to write SGF file: " << out_sgf_path
                << "\n";
      return 2;
    }
  }

  std::cout << "{\"solverVersion\":\"LDProver-1.8.2\",\"problemId\":\""
            << prob_id << "\",\"rootStatus\":\""
            << OutcomeLabel(report.root_status)
            << "\",\"unknownReason\":\""
            << UnknownReasonLabel(report.unknown_reason)
            << "\",\"bestMove\":" << report.best_move
            << ",\"numNodes\":" << report.num_nodes
            << ",\"prunedOutsideRz\":" << report.pruned_outside_rz_count
            << ",\"checker\":\"" << checker_code
            << "\",\"proofChecksum\":\"" << checksum << "\"}\n";
  return 0;
}

template <int N>
int ExecuteCheckForBoardSize(
    const std::string& proof_json, const std::string& problem_path,
    std::optional<ldprover::VerificationScope> scope_override,
    ldprover::VerificationReport* out_ver) {
  ldprover::ProofArtifactManager<N> mgr;
  if (!problem_path.empty()) {
    std::string raw_problem_json;
    if (!ReadEntireFile(problem_path, &raw_problem_json)) {
      std::cerr << "[LDProver] Cannot read --problem file: " << problem_path
                << "\n";
      return 2;
    }
    ldprover::ProblemContractParser<N> parser;
    const std::string pid = BasenameStem(problem_path);
    const auto parsed = parser.ParseTsumegoJsonObject(pid, raw_problem_json);
    if (!parsed.valid) {
      std::cerr << "{\"problemId\":\"" << pid << "\",\"valid\":false,"
                << "\"errorCode\":\"" << parsed.error_code << "\","
                << "\"message\":\"" << parsed.error_message << "\"}\n";
      return 2;
    }
    *out_ver = mgr.VerifyLProofJsonString(proof_json, &parsed, scope_override);
    return 0;
  }
  *out_ver = mgr.VerifyLProofJsonString(proof_json, nullptr, scope_override);
  return 0;
}

int RunCheckCommand(int argc, char* argv[]) {
  std::string proof_path;
  std::string problem_path;
  bool allow_subposition = false;
  bool free_exploration = false;
  for (int i = 2; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--proof" && i + 1 < argc) {
      proof_path = argv[++i];
    } else if (arg == "--problem" && i + 1 < argc) {
      problem_path = argv[++i];
    } else if (arg == "--allow-subposition") {
      allow_subposition = true;
    } else if (arg == "--free-exploration") {
      free_exploration = true;
    } else {
      std::cerr << "[LDProver] Unknown or incomplete check option: " << arg
                << "\n";
      return 2;
    }
  }

  if (allow_subposition && free_exploration) {
    std::cerr << "[LDProver] --allow-subposition and --free-exploration are "
                 "mutually exclusive.\n";
    return 2;
  }
  std::optional<ldprover::VerificationScope> scope_override;
  if (allow_subposition) {
    scope_override = ldprover::VerificationScope::kTracedWithinRules;
  } else if (free_exploration) {
    scope_override = ldprover::VerificationScope::kFreeExploration;
  }

  if (proof_path.empty()) {
    std::cerr << "[LDProver] Missing required --proof <proof.json>\n";
    return 2;
  }

  std::string proof_json;
  if (!ReadEntireFile(proof_path, &proof_json)) {
    std::cerr << "[LDProver] Cannot read proof file: " << proof_path << "\n";
    return 2;
  }

  const int bs = DetectBoardSizeFromProofJson(proof_json);
  ldprover::VerificationReport ver;
  int prep_rc = 0;
  if (bs == 5) {
    prep_rc = ExecuteCheckForBoardSize<5>(proof_json, problem_path,
                                          scope_override, &ver);
  } else if (bs == 7) {
    prep_rc = ExecuteCheckForBoardSize<7>(proof_json, problem_path,
                                          scope_override, &ver);
  } else if (bs == 19) {
    prep_rc = ExecuteCheckForBoardSize<19>(proof_json, problem_path,
                                           scope_override, &ver);
  } else {
    std::cerr << "[LDProver] Unsupported boardSize in proof JSON.\n";
    return 2;
  }
  if (prep_rc != 0) return prep_rc;

  std::cout << "{\"passed\":" << (ver.passed ? "true" : "false")
            << ",\"errorCode\":\"" << ver.error_code
            << "\",\"message\":\"" << ver.message
            << "\",\"verifiedNodes\":" << ver.verified_nodes
            << ",\"verifiedStates\":" << ver.verified_states
            << ",\"replayedPrunedCertificates\":"
            << ver.replayed_pruned_certificates
            << ",\"encodingMode\":\"" << ver.encoding_mode
            << "\",\"verifiedScope\":\"" << ver.verified_scope
            << "\",\"verifiedRootKind\":\"" << ver.verified_root_kind
            << "\",\"traceOutsideRegion\":"
            << (ver.trace_outside_region ? "true" : "false")
            << ",\"traceHasRestrictedKoCapture\":"
            << (ver.trace_has_restricted_ko_capture ? "true" : "false")
            << ",\"checksum\":\"" << ver.jcs_sha256_checksum
            << "\",\"canonicalDagChecksum\":\"" << ver.canonical_dag_checksum
            << "\"}\n";
  return ver.passed ? 0 : 2;
}

int RunBenchCommand(int argc, char* argv[]) {
  std::string manifest_path;
  std::string out_csv_path;
  ldprover::SolverConfig config;
  config.max_nodes = 2500;

  for (int i = 2; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--manifest" && i + 1 < argc) {
      manifest_path = argv[++i];
    } else if (arg == "--out" && i + 1 < argc) {
      out_csv_path = argv[++i];
    } else if (arg == "--node-limit" && i + 1 < argc) {
      config.max_nodes =
          static_cast<uint32_t>(std::strtoul(argv[++i], nullptr, 10));
    } else {
      std::cerr << "[LDProver] Unknown or incomplete bench option: " << arg
                << "\n";
      return 2;
    }
  }

  if (manifest_path.empty()) {
    std::cerr << "[LDProver] Missing required --manifest <manifest.json>\n";
    return 2;
  }

  std::string manifest_json;
  if (!ReadEntireFile(manifest_path, &manifest_json)) {
    std::cerr << "[LDProver] Cannot read manifest file: " << manifest_path
              << "\n";
    return 2;
  }

  const auto problem_files = ParseJsonStringArray(manifest_json);
  if (problem_files.empty()) {
    std::cerr << "[LDProver] Manifest must be a non-empty JSON array of problem "
                 "file paths.\n";
    return 2;
  }

  std::ostringstream csv;
  csv << "problem_id,root_status,best_move,num_nodes,pruned_outside_rz,checker\n";

  ldprover::ProblemContractParser<19> parser;
  ldprover::ProofArtifactManager<19> checker;
  uint32_t proven_count = 0;

  for (const std::string& pfile : problem_files) {
    std::string raw_json;
    if (!ReadEntireFile(pfile, &raw_json)) {
      std::cerr << "[LDProver] Cannot read benchmark problem: " << pfile << "\n";
      return 2;
    }
    const std::string pid = BasenameStem(pfile);
    const auto parsed = parser.ParseTsumegoJsonObject(pid, raw_json);
    if (!parsed.valid) {
      std::cerr << "[LDProver] Contract error in " << pid << ": "
                << parsed.error_code << "\n";
      return 2;
    }
    ldprover::DfpnSolver<19> solver(config);
    const auto rep = solver.Solve(parsed.initial_position, parsed.proof_context,
                                  parsed.region_search_mask);
    std::string chk_status = "UNKNOWN_BARRIER";
    if (rep.root_status != ldprover::ProofOutcome::kUnknown) {
      const auto ver = checker.VerifyProofDag(parsed.initial_position,
                                              parsed.proof_context, rep);
      if (!ver.passed) {
        std::cerr << "[LDProver] Benchmark proof check FAILED on " << pid
                  << " (" << ver.error_code << ")\n";
        return 2;
      }
      chk_status = "PASS";
      ++proven_count;
    }
    csv << pid << "," << OutcomeLabel(rep.root_status) << "," << rep.best_move
        << "," << rep.num_nodes << "," << rep.pruned_outside_rz_count << ","
        << chk_status << "\n";
  }

  if (!out_csv_path.empty() && !WriteEntireFile(out_csv_path, csv.str())) {
    std::cerr << "[LDProver] Cannot write CSV output: " << out_csv_path << "\n";
    return 2;
  }

  std::cout << "{\"subcommand\":\"bench\",\"totalProblems\":"
            << problem_files.size() << ",\"provenAndVerified\":" << proven_count
            << "}\n";
  return 0;
}

}  // namespace

int main(int argc, char* argv[]) {
  if (argc < 2) {
    std::cerr << "Usage: tprover <solve|check|bench> [options]\n"
              << "  solve --problem <file.json> [--out-proof <proof.json>] "
              << "[--mode board-tt|pattern-tt] [--node-limit <N>] "
              << "[--memory-budget <MiB>]\n"
              << "  check --proof <proof.json> [--problem <original.json>] "
              << "[--allow-subposition | --free-exploration]\n"
              << "  bench --manifest <benchmark_manifest.json> [--out <out.csv>]\n";
    return 2;
  }

  try {
    const std::string subcommand = argv[1];
    if (subcommand == "solve") return RunSolveCommand(argc, argv);
    if (subcommand == "check") return RunCheckCommand(argc, argv);
    if (subcommand == "bench") return RunBenchCommand(argc, argv);

    std::cerr << "[LDProver] Unknown subcommand: " << subcommand << "\n";
    return 2;
  } catch (const std::exception& e) {
    std::cerr << "[LDProver] Internal error: " << e.what() << "\n";
    return 3;
  }
}
