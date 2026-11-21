// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: tests/r5_regression_test.cc
// Description: Versioned R5 native C++20 regression suite covering:
//   1. R5 §1 P1: Native df-pn PASS scheduling with RZ enabled on p003 & p004.
//   2. R5 §2 P1: Memory & JSON verification scope parity (original_root,
//      traced_within_rules, free_exploration) for in-region, out-of-region,
//      restricted-ko traces, and contradictory initial+trace payloads.
//   3. R5 §3 P1: Full-state-table cross-table DAG-to-state binding (LP-N10 on
//      p001 ba leaf pointing to root stateId=0; PASS on valid full_state_table).

#include <cstdint>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

#include "ldprover/core/position.h"
#include "ldprover/core/problem_parser.h"
#include "ldprover/core/types.h"
#include "ldprover/proof/proof_checker.h"
#include "ldprover/search/dfpn_solver.h"

namespace {

using ldprover::BitBoard;
using ldprover::DfpnSolver;
using ldprover::ParsedProblem;
using ldprover::Position;
using ldprover::ProblemContractParser;
using ldprover::ProofArtifactManager;
using ldprover::ProofOutcome;
using ldprover::SolveReport;
using ldprover::SolverConfig;
using ldprover::TurnConflictPolicy;
using ldprover::UnknownReason;
using ldprover::VerificationReport;
using ldprover::VerificationScope;

int g_total = 0;
int g_passed = 0;

void Check(bool cond, const std::string& label,
           const std::string& detail = "") {
  ++g_total;
  if (cond) {
    ++g_passed;
  } else {
    std::cerr << "  [FAIL] " << label;
    if (!detail.empty()) {
      std::cerr << " -- " << detail;
    }
    std::cerr << "\n";
  }
}

SolverConfig DefaultConfig(uint32_t max_nodes = 3500U) {
  SolverConfig cfg;
  cfg.max_nodes = max_nodes;
  cfg.max_depth = 64U;
  cfg.memory_budget_bytes = 256ULL * 1024ULL * 1024ULL;
  cfg.enable_rz_pruning = true;
  cfg.enable_pattern_tt = true;
  cfg.enable_fast_capture_ordering = true;
  cfg.enable_progressive_widening = true;
  cfg.widening_base_k = 8U;
  cfg.deterministic_mode = true;
  return cfg;
}

ParsedProblem<19> BuildP001() {
  ProblemContractParser<19> parser;
  ParsedProblem<19> prob = parser.ParseTsumegoJson(
      "p001_straight_three_live",
      "(;GM[1]FF[4]SZ[19]PL[B]AB[da][ab][bb][cb][db]"
      "AW[ea][eb][ac][bc][cc][dc][ec])",
      "B", "TOLIVE", "TOKILL", "bb", "cb", "B",
      TurnConflictPolicy::kRejectStrict, "aa,ba,ca", false, true);
  prob.initial_position.SetImmortalWall(
      prob.initial_position.Stones(ldprover::Color::kWhite));
  return prob;
}

ParsedProblem<19> BuildP003() {
  ProblemContractParser<19> parser;
  ParsedProblem<19> prob = parser.ParseTsumegoJson(
      "p003_false_eye_poke_kill",
      "(;GM[1]FF[4]SZ[19]PL[W]AB[ba][da][ab][bb][cb]"
      "AW[ea][eb][ac][bc][cc][dc][ec])",
      "W", "TOLIVE", "TOKILL", "bb", "bb", "W",
      TurnConflictPolicy::kRejectStrict, "aa,ca,db", false, true);
  prob.initial_position.SetImmortalWall(
      prob.initial_position.Stones(ldprover::Color::kWhite));
  return prob;
}

ParsedProblem<19> BuildP004() {
  ProblemContractParser<19> parser;
  ParsedProblem<19> prob = parser.ParseTsumegoJson(
      "p004_outside_rz_pruning",
      "(;GM[1]FF[4]SZ[19]PL[W]AB[ba][ab][bb][da][db][eb][fb][fa][cc]"
      "AW[ga][gb][ac][bc][dc][ec][fc][gc])",
      "B", "TOLIVE", "TOKILL", "bb", "ac", "W",
      TurnConflictPolicy::kRejectStrict, "aa,ca,cb,ea,ed,fd,ee,fe", false,
      true);
  prob.initial_position.SetImmortalWall(
      prob.initial_position.Stones(ldprover::Color::kWhite));
  return prob;
}

ParsedProblem<19> BuildP005(bool attacker_allow_ko) {
  ProblemContractParser<19> parser;
  ParsedProblem<19> prob = parser.ParseTsumegoJson(
      "p005_ko_dependent_barrier",
      "(;GM[1]FF[4]SZ[19]PL[B]AB[aa][ab][bb]AW[ba][da][cb][db])", "B",
      "TOKILL", "TOLIVE", "ba", "ba", "B", TurnConflictPolicy::kRejectStrict,
      "ca", attacker_allow_ko, true);
  // Match benchmark immortal outer wall: B[aa,ab,bb] + W[da,cb,db]
  BitBoard<19> wall;
  wall.Set(Position<19>::CoordFromRowCol(0, 0), true);
  wall.Set(Position<19>::CoordFromRowCol(1, 0), true);
  wall.Set(Position<19>::CoordFromRowCol(1, 1), true);
  wall.Set(Position<19>::CoordFromRowCol(0, 3), true);
  wall.Set(Position<19>::CoordFromRowCol(1, 2), true);
  wall.Set(Position<19>::CoordFromRowCol(1, 3), true);
  prob.initial_position.SetImmortalWall(wall);
  return prob;
}

void VerifyTracedScenario(const std::string& label,
                          const ParsedProblem<19>& prob,
                          const std::vector<int16_t>& trace_moves,
                          const std::string& expected_original_code,
                          const std::string& expected_traced_code,
                          const std::string& expected_free_code,
                          bool expected_outside_region,
                          bool expected_restricted_ko) {
  Position<19> sub_pos = prob.initial_position;
  for (int16_t mv : trace_moves) {
    bool is_ko = false;
    const bool legal = sub_pos.PlayMove(mv, &is_ko);
    Check(legal, label + " manual move legal");
  }

  DfpnSolver<19> solver(DefaultConfig(3500U));
  const SolveReport<19> rep = solver.Solve(
      sub_pos, prob.proof_context, prob.region_search_mask, prob.problem_id);
  Check(rep.root_status == ProofOutcome::kProvenWin ||
            rep.root_status == ProofOutcome::kProvenLoss,
        label + " reached decisive outcome");

  ProofArtifactManager<19> checker;
  const std::string json_payload =
      checker.SerializeLProofJson(sub_pos, prob.proof_context, rep);

  struct ScopeCase {
    VerificationScope scope;
    std::string name;
    std::string expected_code;
  };
  const std::vector<ScopeCase> cases = {
      {VerificationScope::kOriginalRoot, "original_root",
       expected_original_code},
      {VerificationScope::kTracedWithinRules, "traced_within_rules",
       expected_traced_code},
      {VerificationScope::kFreeExploration, "free_exploration",
       expected_free_code},
  };

  for (const ScopeCase& sc : cases) {
    const VerificationReport mem = checker.VerifyProofDag(
        sub_pos, prob.proof_context, rep, sc.scope);
    const VerificationReport file =
        checker.VerifyLProofJsonString(json_payload, &prob, sc.scope);
    Check(mem.error_code == sc.expected_code &&
              file.error_code == sc.expected_code,
          label + " [" + sc.name + "] mem & file error_code == " +
              sc.expected_code,
          "mem=" + mem.error_code + ", file=" + file.error_code);
    Check(mem.passed == (sc.expected_code == "PASS") &&
              file.passed == (sc.expected_code == "PASS"),
          label + " [" + sc.name + "] mem & file passed parity");
    Check(mem.verified_root_kind == "traced_subposition" &&
              file.verified_root_kind == "traced_subposition",
          label + " [" + sc.name + "] verified_root_kind == traced_subposition");
    if (sc.scope != VerificationScope::kOriginalRoot) {
      Check(mem.trace_outside_region == expected_outside_region &&
                file.trace_outside_region == expected_outside_region,
            label + " [" + sc.name + "] trace_outside_region match");
      Check(mem.trace_has_restricted_ko_capture == expected_restricted_ko &&
                file.trace_has_restricted_ko_capture == expected_restricted_ko,
            label + " [" + sc.name + "] trace_has_restricted_ko_capture match");
    }
  }
}

void TestSection1SearchRegression() {
  std::cout << "\n=== 1. R5 §1 Native Search Regression (p001, p003, p004, p005) ===\n";
  ProofArtifactManager<19> checker;

  // p001
  {
    const ParsedProblem<19> p001 = BuildP001();
    Check(p001.valid, "p001 parsed cleanly");
    DfpnSolver<19> solver(DefaultConfig(3500U));
    const SolveReport<19> rep = solver.Solve(
        p001.initial_position, p001.proof_context, p001.region_search_mask,
        p001.problem_id);
    Check(rep.root_status == ProofOutcome::kProvenWin, "p001 PROVEN_WIN");
    const VerificationReport mem = checker.VerifyProofDag(
        p001.initial_position, p001.proof_context, rep,
        VerificationScope::kOriginalRoot);
    const std::string json =
        checker.SerializeLProofJson(p001.initial_position, p001.proof_context, rep);
    const VerificationReport file = checker.VerifyLProofJsonString(
        json, &p001, VerificationScope::kOriginalRoot);
    Check(mem.passed && file.passed, "p001 mem & file verification PASS",
          "mem=" + mem.error_code + ", file=" + file.error_code);
  }

  // p003 with RZ ON (R5 §1 regression check)
  {
    const ParsedProblem<19> p003 = BuildP003();
    Check(p003.valid, "p003 parsed cleanly");
    DfpnSolver<19> solver(DefaultConfig(3500U));
    const SolveReport<19> rep = solver.Solve(
        p003.initial_position, p003.proof_context, p003.region_search_mask,
        p003.problem_id);
    Check(rep.root_status == ProofOutcome::kProvenWin,
          "p003 RZ-on PROVEN_WIN",
          "nodes=" + std::to_string(rep.num_nodes));
    Check(rep.num_nodes <= 50U,
          "p003 RZ-on solves within 50 nodes (no PASS spin-loop)",
          "nodes=" + std::to_string(rep.num_nodes));
    const VerificationReport mem = checker.VerifyProofDag(
        p003.initial_position, p003.proof_context, rep,
        VerificationScope::kOriginalRoot);
    const std::string json =
        checker.SerializeLProofJson(p003.initial_position, p003.proof_context, rep);
    const VerificationReport file = checker.VerifyLProofJsonString(
        json, &p003, VerificationScope::kOriginalRoot);
    Check(mem.passed && file.passed, "p003 RZ-on mem & file verification PASS",
          "mem=" + mem.error_code + ", file=" + file.error_code);
  }

  // p004 with RZ ON (R5 §1 regression check + OutsideRZRevalidated pruning)
  {
    const ParsedProblem<19> p004 = BuildP004();
    Check(p004.valid, "p004 parsed cleanly");
    DfpnSolver<19> solver(DefaultConfig(3500U));
    const SolveReport<19> rep = solver.Solve(
        p004.initial_position, p004.proof_context, p004.region_search_mask,
        p004.problem_id);
    Check(rep.root_status == ProofOutcome::kProvenWin,
          "p004 RZ-on PROVEN_WIN",
          "nodes=" + std::to_string(rep.num_nodes));
    Check(rep.num_nodes <= 50U,
          "p004 RZ-on solves within 50 nodes (no PASS spin-loop)",
          "nodes=" + std::to_string(rep.num_nodes));
    Check(rep.pruned_outside_rz_count > 0U,
          "p004 RZ-on triggers OutsideRZRevalidated pruning",
          "pruned=" + std::to_string(rep.pruned_outside_rz_count));
    const VerificationReport mem = checker.VerifyProofDag(
        p004.initial_position, p004.proof_context, rep,
        VerificationScope::kOriginalRoot);
    const std::string json =
        checker.SerializeLProofJson(p004.initial_position, p004.proof_context, rep);
    const VerificationReport file = checker.VerifyLProofJsonString(
        json, &p004, VerificationScope::kOriginalRoot);
    Check(mem.passed && file.passed, "p004 RZ-on mem & file verification PASS",
          "mem=" + mem.error_code + ", file=" + file.error_code);
  }

  // p005 default allow_ko=false -> UNKNOWN(kKoDependent), allow_ko=true -> PROVEN_WIN
  {
    const ParsedProblem<19> p005_strict = BuildP005(false);
    Check(p005_strict.valid, "p005 strict parsed cleanly");
    DfpnSolver<19> solver_strict(DefaultConfig(3500U));
    const SolveReport<19> rep_strict = solver_strict.Solve(
        p005_strict.initial_position, p005_strict.proof_context,
        p005_strict.region_search_mask, p005_strict.problem_id);
    Check(rep_strict.root_status == ProofOutcome::kUnknown &&
              rep_strict.unknown_reason == UnknownReason::kKoDependent,
          "p005 allow_ko=false returns UNKNOWN(kKoDependent)");

    const ParsedProblem<19> p005_ko = BuildP005(true);
    DfpnSolver<19> solver_ko(DefaultConfig(3500U));
    const SolveReport<19> rep_ko = solver_ko.Solve(
        p005_ko.initial_position, p005_ko.proof_context,
        p005_ko.region_search_mask, p005_ko.problem_id);
    Check(rep_ko.root_status == ProofOutcome::kProvenWin,
          "p005 allow_ko=true returns PROVEN_WIN");
    const VerificationReport mem = checker.VerifyProofDag(
        p005_ko.initial_position, p005_ko.proof_context, rep_ko,
        VerificationScope::kOriginalRoot);
    Check(mem.passed, "p005 allow_ko=true mem verification PASS",
          mem.error_code);
  }
}

void TestSection2ScopeParity() {
  std::cout << "\n=== 2. R5 §2 Memory & File Verification Scope Parity ===\n";
  const ParsedProblem<19> p001 = BuildP001();
  const ParsedProblem<19> p005 = BuildP005(false);

  // Case A: p001 legal in-region trace [aa (0)]
  VerifyTracedScenario("p001 in-region [aa]", p001,
                       {static_cast<int16_t>(Position<19>::CoordFromRowCol(0, 0))},
                       "LP-P02", "PASS", "PASS", false, false);

  // Case B: p001 out-of-region trace [fa (5)]
  VerifyTracedScenario("p001 out-of-region [fa]", p001,
                       {static_cast<int16_t>(Position<19>::CoordFromRowCol(0, 5))},
                       "LP-P02", "LP-S11", "PASS", true, false);

  // Case C: p005 restricted-side ko capture [ca (2)]
  VerifyTracedScenario("p005 restricted-ko [ca]", p005,
                       {static_cast<int16_t>(Position<19>::CoordFromRowCol(0, 2))},
                       "LP-P02", "LP-S12", "PASS", false, true);
}

void TestSection3FullStateBindingAndContradictoryRoot() {
  std::cout << "\n=== 3. R5 §3 Full-State StateId Binding & Contradictory Initial+Trace ===\n";
  ProofArtifactManager<19> checker;
  const ParsedProblem<19> p001 = BuildP001();

  // Real TS-exported p001 full_state_table lproof/1 (valid JCS SHA-256)
  static const std::string kValidFullStateJson = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":1,"toPlay":2,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"012424dc168fb64a","blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":1}],"snapshotPool":[{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":1,"zobristHex":"06fe8925c3232e8b"},{"blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":2,"zobristHex":"012424dc168fb64a"}],"historySnapshotIds":[[0],[0,1]],"nodes":[{"nodeId":0,"stateId":1,"historyId":1,"parentStateId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:73ce0ce6fe2c595f76798f0c72cf3067c4e46a61998955665f944cbee3a40c2a"})json";

  // R5 §3 critical mutation: ba leaf nodeId=0 points stateId to 0 (root state), re-signed
  static const std::string kMutatedBaLeafState0Json = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":1,"toPlay":2,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"012424dc168fb64a","blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":1}],"snapshotPool":[{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":1,"zobristHex":"06fe8925c3232e8b"},{"blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":2,"zobristHex":"012424dc168fb64a"}],"historySnapshotIds":[[0],[0,1]],"nodes":[{"nodeId":0,"stateId":0,"historyId":1,"parentStateId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:542accd7fcf7709d2ebb116c03122b85a59ee75b10565465a5073e18b0345a8a"})json";

  // R5 §2 contradictory rootKind="initial" + non-empty initialTraceMoves=[1], re-signed
  static const std::string kContradictoryInitialTraceJson = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true,"initialTraceMoves":[1]},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":1,"toPlay":2,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"012424dc168fb64a","blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":1}],"snapshotPool":[{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":1,"zobristHex":"06fe8925c3232e8b"},{"blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":2,"zobristHex":"012424dc168fb64a"}],"historySnapshotIds":[[0],[0,1]],"nodes":[{"nodeId":0,"stateId":1,"historyId":1,"parentStateId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:e8fb0cdacc52965f0700de34d33ac3b3831145957f9247e3c5aace34859c9c21"})json";

  const VerificationReport valid_ver = checker.VerifyLProofJsonString(
      kValidFullStateJson, &p001, VerificationScope::kOriginalRoot);
  Check(valid_ver.passed && valid_ver.error_code == "PASS",
        "Valid TS full_state_table p001 passes native C++ checker",
        "code=" + valid_ver.error_code + ", msg=" + valid_ver.message);

  const VerificationReport bad_state_ver = checker.VerifyLProofJsonString(
      kMutatedBaLeafState0Json, &p001, VerificationScope::kOriginalRoot);
  Check(!bad_state_ver.passed && bad_state_ver.error_code == "LP-N10",
        "Mutated full_state_table ba leaf stateId=0 rejected with LP-N10",
        "passed=" + std::string(bad_state_ver.passed ? "true" : "false") +
            ", code=" + bad_state_ver.error_code);

  const VerificationReport contra_default =
      checker.VerifyLProofJsonString(kContradictoryInitialTraceJson);
  const VerificationReport contra_free = checker.VerifyLProofJsonString(
      kContradictoryInitialTraceJson, nullptr,
      VerificationScope::kFreeExploration);
  Check(!contra_default.passed && contra_default.error_code == "LP-P02",
        "Contradictory initial + initialTraceMoves rejected (default) -> LP-P02",
        "code=" + contra_default.error_code);
  Check(!contra_free.passed && contra_free.error_code == "LP-P02",
        "Contradictory initial + initialTraceMoves rejected (free_exploration) -> LP-P02",
        "code=" + contra_free.error_code);
}

}  // namespace

int main() {
  TestSection1SearchRegression();
  TestSection2ScopeParity();
  TestSection3FullStateBindingAndContradictoryRoot();

  const int failed = g_total - g_passed;
  std::cout << "\n========================================\n"
            << "R5 C++20 Regression Summary: " << g_passed << "/" << g_total
            << " passed, " << failed << " failed.\n"
            << "========================================\n";
  return failed == 0 ? 0 : 1;
}
