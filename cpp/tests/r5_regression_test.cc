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

#include <algorithm>
#include <cstdint>
#include <iostream>
#include <optional>
#include <string>
#include <type_traits>
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

const std::string& CommonChaoRegion19() {
  static const std::string kCommonRegion =
      "as,bs,cs,ds,es,fs,gs,hs,is,js,ks,ls,ms,ns,os,ps,qs,rs,ss,"
      "ar,br,cr,dr,er,fr,gr,hr,ir,jr,kr,lr,mr,nr,or,pr,qr,rr,sr,"
      "aq,bq,cq,dq,eq,fq,gq,hq,iq,jq,kq,lq,mq,nq,oq,pq,qq,rq,sq,"
      "jp,kp,lp,mp,np,op,pp,qp,rp,sp,jo,ko,lo,mo,no,oo,po,qo,ro,so,"
      "jn,kn,ln,mn,nn,on,pn,qn,rn,sn,jm,km,lm,mm,nm,om,pm,qm,rm,sm,"
      "jl,kl,ll,ml,nl,ol,pl,ql,rl,sl,jk,kk,lk,mk,nk,ok,pk,qk,rk,sk,"
      "kj,lj,mj,nj,oj,pj,qj,rj,sj,qi,ri,si,qh,rh,sh,qg,rg,sg,qf,rf,sf,"
      "qe,re,se,qd,rd,sd,qc,rc,sc,qb,rb,sb,qa,ra,sa";
  return kCommonRegion;
}

ParsedProblem<19> BuildP031() {
  ProblemContractParser<19> parser;
  const std::string p031_json =
      std::string(
          R"json({"masked_sgf_str":"(;FF[4]CA[UTF-8]SZ[19]KM[14]AB[or][pr][qr][rr][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[lq][mq][nq][oq][pq][qq][rq][ap][bp][cp][dp][ep][fp][gp][hp][ip][io][ro][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[or]MA[as][bs][cs][ds][es][fs][gs][hs][is][js][ks][ls][ms][ns][os][ps][qs][rs][ss][ar][br][cr][dr][er][fr][gr][hr][ir][jr][kr][lr][mr][nr][or][pr][qr][rr][sr][aq][bq][cq][dq][eq][fq][gq][hq][iq][jq][kq][lq][mq][nq][oq][pq][qq][rq][sq][jp][kp][lp][mp][np][op][pp][qp][rp][sp][jo][ko][lo][mo][no][oo][po][qo][ro][so][jn][kn][ln][mn][nn][on][pn][qn][rn][sn][jm][km][lm][mm][nm][om][pm][qm][rm][sm][jl][kl][ll][ml][nl][ol][pl][ql][rl][sl][jk][kk][lk][mk][nk][ok][pk][qk][rk][sk][kj][lj][mj][nj][oj][pj][qj][rj][sj][qi][ri][si][qh][rh][sh][qg][rg][sg][qf][rf][sf][qe][re][se][qd][rd][sd][qc][rc][sc][qb][rb][sb][qa][ra][sa])","winning_color":"b","turn_color":"b","black_crucial_stone":"or","white_crucial_stone":"","black_search_goal":"TOLIVE","white_search_goal":"TOKILL","black_ko_rule":"disallow_ko","white_ko_rule":"allow_ko","region":")json") +
      CommonChaoRegion19() + "\"}";
  return parser.ParseTsumegoJsonObject("chao_vol1_p031", p031_json,
                                       TurnConflictPolicy::kRejectStrict);
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

  // R6 §3 mutations on ba leaf: historyId=0 -> LP-S10, parentStateId=-1 -> LP-S10, missing historyId -> LP-J02
  static const std::string kMutatedBaLeafHistory0Json = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":1,"toPlay":2,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"012424dc168fb64a","blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":1}],"snapshotPool":[{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":1,"zobristHex":"06fe8925c3232e8b"},{"blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":2,"zobristHex":"012424dc168fb64a"}],"historySnapshotIds":[[0],[0,1]],"nodes":[{"nodeId":0,"stateId":1,"historyId":0,"parentStateId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:7674fe298eec27b0dd73db1229d085a0dc4639aff4edf8793134b74ea8ff0840"})json";

  static const std::string kMutatedBaLeafParentNeg1Json = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":1,"toPlay":2,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"012424dc168fb64a","blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":1}],"snapshotPool":[{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":1,"zobristHex":"06fe8925c3232e8b"},{"blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":2,"zobristHex":"012424dc168fb64a"}],"historySnapshotIds":[[0],[0,1]],"nodes":[{"nodeId":0,"stateId":1,"historyId":1,"parentStateId":-1,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:a0992abe5be23892e244f5d9111ba82fb68fc74335e6784f6242a5065aa1ecf8"})json";

  static const std::string kDeletedBaLeafHistoryJson = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":1,"toPlay":2,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"012424dc168fb64a","blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":1}],"snapshotPool":[{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":1,"zobristHex":"06fe8925c3232e8b"},{"blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":2,"zobristHex":"012424dc168fb64a"}],"historySnapshotIds":[[0],[0,1]],"nodes":[{"nodeId":0,"stateId":1,"parentStateId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:742e6ce7a5e71878a885bba4357994be4abe117da5f40e6c1c8a39c2cf759c4d"})json";

  // R6 §4 extra non-semantic top-level JSON field -> re-signed -> PASS with shared canonical_dag_checksum
  static const std::string kExtraFieldFullStateJson = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":1,"toPlay":2,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"012424dc168fb64a","blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":1}],"snapshotPool":[{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":1,"zobristHex":"06fe8925c3232e8b"},{"blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":2,"zobristHex":"012424dc168fb64a"}],"historySnapshotIds":[[0],[0,1]],"nodes":[{"nodeId":0,"stateId":1,"historyId":1,"parentStateId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"extraNonSemanticTag":"r6-audit-metadata","checksum":"sha256-jcs:7fc7b0f71d73d0c59c82bf25c921f7a7d94b02b541085aca797735877f78799f"})json";

  static const std::string kExpectedCanonicalDagChecksum =
      "sha256-jcs:a002fe4896c1c728d06c9700518bf86bdb9e5a0b8c8dc58a8e3ecf7ef9d669d6";

  const VerificationReport valid_ver = checker.VerifyLProofJsonString(
      kValidFullStateJson, &p001, VerificationScope::kOriginalRoot);
  Check(valid_ver.passed && valid_ver.error_code == "PASS",
        "Valid TS full_state_table p001 passes native C++ checker",
        "code=" + valid_ver.error_code + ", msg=" + valid_ver.message);
  Check(valid_ver.canonical_dag_checksum == kExpectedCanonicalDagChecksum,
        "R6 §4 Valid TS full_state_table canonical_dag_checksum matches TS exactly",
        "got=" + valid_ver.canonical_dag_checksum);

  const VerificationReport extra_ver = checker.VerifyLProofJsonString(
      kExtraFieldFullStateJson, &p001, VerificationScope::kOriginalRoot);
  Check(extra_ver.passed && extra_ver.error_code == "PASS",
        "R6 §4 Extra-field full_state_table passes native C++ checker",
        "code=" + extra_ver.error_code);
  Check(extra_ver.jcs_sha256_checksum ==
            "sha256-jcs:7fc7b0f71d73d0c59c82bf25c921f7a7d94b02b541085aca797735877f78799f",
        "R6 §4 Extra-field jcs_sha256_checksum preserves input file digest",
        "got=" + extra_ver.jcs_sha256_checksum);
  Check(extra_ver.canonical_dag_checksum == kExpectedCanonicalDagChecksum,
        "R6 §4 Extra-field canonical_dag_checksum stays identical to TS & baseline",
        "got=" + extra_ver.canonical_dag_checksum);

  const VerificationReport bad_state_ver = checker.VerifyLProofJsonString(
      kMutatedBaLeafState0Json, &p001, VerificationScope::kOriginalRoot);
  Check(!bad_state_ver.passed && bad_state_ver.error_code == "LP-N10",
        "Mutated full_state_table ba leaf stateId=0 rejected with LP-N10",
        "passed=" + std::string(bad_state_ver.passed ? "true" : "false") +
            ", code=" + bad_state_ver.error_code);

  const VerificationReport bad_hist_ver = checker.VerifyLProofJsonString(
      kMutatedBaLeafHistory0Json, &p001, VerificationScope::kOriginalRoot);
  Check(!bad_hist_ver.passed && bad_hist_ver.error_code == "LP-S10",
        "R6 §3 Mutated full_state_table ba leaf historyId=0 rejected with LP-S10",
        "code=" + bad_hist_ver.error_code);

  const VerificationReport bad_par_ver = checker.VerifyLProofJsonString(
      kMutatedBaLeafParentNeg1Json, &p001, VerificationScope::kOriginalRoot);
  Check(!bad_par_ver.passed && bad_par_ver.error_code == "LP-S10",
        "R6 §3 Mutated full_state_table ba leaf parentStateId=-1 rejected with LP-S10",
        "code=" + bad_par_ver.error_code);

  const VerificationReport del_hist_ver = checker.VerifyLProofJsonString(
      kDeletedBaLeafHistoryJson, &p001, VerificationScope::kOriginalRoot);
  Check(!del_hist_ver.passed && del_hist_ver.error_code == "LP-J02",
        "R6 §3 Deleted full_state_table ba leaf historyId rejected with LP-J02",
        "code=" + del_hist_ver.error_code);

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

void TestSection4R7ProtocolEdgeCases() {
  std::cout << "\n=== 4. R7 Protocol Edge Cases (§2 Empty Region, §3 NULL_MOVE, §4 Unicode) ===\n";
  ProofArtifactManager<19> checker;
  const ParsedProblem<19> p001 = BuildP001();

  // --- R7 §2 P1: Native solve -> serialize -> independent verify with explicit empty BitBoard<19>{} ---
  {
    const std::optional<BitBoard<19>> explicit_empty_region = BitBoard<19>{};
    DfpnSolver<19> solver(DefaultConfig(3500U));
    const SolveReport<19> rep = solver.Solve(
        p001.initial_position, p001.proof_context, explicit_empty_region,
        p001.problem_id);
    Check(rep.root_status == ProofOutcome::kProvenLoss && rep.num_nodes <= 5U,
          "R7 §2 Native p001 explicit empty region (PASS-only) solves to PROVEN_LOSS in <= 5 nodes",
          "nodes=" + std::to_string(rep.num_nodes));

    const VerificationReport mem = checker.VerifyProofDag(
        p001.initial_position, p001.proof_context, rep,
        VerificationScope::kOriginalRoot);
    Check(mem.passed && mem.error_code == "PASS",
          "R7 §2 Native p001 explicit empty region passes memory verification",
          "code=" + mem.error_code);

    const std::string serialized =
        checker.SerializeLProofJson(p001.initial_position, p001.proof_context, rep);
    Check(serialized.find("\"hasRegionHint\": true") != std::string::npos &&
              serialized.find("\"regionCoords\": []") != std::string::npos,
          "R7 §2 Native serialized lproof/1 preserves hasRegionHint=true and regionCoords=[]");

    const VerificationReport file = checker.VerifyLProofJsonString(serialized);
    Check(file.passed && file.error_code == "PASS",
          "R7 §2 Native p001 explicit empty region round-trips solve->serialize->check PASS",
          "code=" + file.error_code + ", msg=" + file.message);
    Check(file.canonical_dag_checksum == mem.canonical_dag_checksum,
          "R7 §2 Native explicit empty region memory & file canonical_dag_checksum match");
  }

  // Reverse witness: p001 ba with hasRegionHint=true, regionCoords=[] -> LP-R02
  static const std::string kReverseEmptyRegionCompactJson = R"json({"magic":"lproof/1","encodingMode":"compact_dag","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[],"rawRegionPointCount":0,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","nodes":[{"nodeId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:c8d662ba04cad3d079ff20ce3b92f86065772403d34826e57541768fde36fa15"})json";
  const VerificationReport rev_ver =
      checker.VerifyLProofJsonString(kReverseEmptyRegionCompactJson);
  Check(!rev_ver.passed && rev_ver.error_code == "LP-R02",
        "R7 §2 Reverse witness (p001 ba with hasRegionHint=true, regionCoords=[]) rejected -> LP-R02",
        "code=" + rev_ver.error_code);

  // Contradictory hasRegionHint=false + non-empty regionCoords=[0,1,2] -> LP-J02
  static const std::string kContradictoryRegionJson = R"json({"magic":"lproof/1","encodingMode":"compact_dag","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":false,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","nodes":[{"nodeId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:5e6d4d88b624014f4c559e49f9f426672050119d431040bb100bca1017a1db14"})json";
  const VerificationReport contra_reg_ver =
      checker.VerifyLProofJsonString(kContradictoryRegionJson);
  Check(!contra_reg_ver.passed && contra_reg_ver.error_code == "LP-J02",
        "R7 §2 Contradictory hasRegionHint=false with non-empty regionCoords rejected -> LP-J02",
        "code=" + contra_reg_ver.error_code);

  // --- R7 §3 P2: PROVEN_LOSS with NULL_MOVE (-2) & bestMoveSgf="" vs null vs mismatched ---
  static const std::string kExpectedEmptyLossCanon =
      "sha256-jcs:f83cc46ec4ce760c9652c1767556ab8b0d79ece0fb982c286f0f5a2d8f882c03";
  static const std::string kEmptyLossFullEmptySgfJson = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[],"rawRegionPointCount":0,"isFullRegionSearch":true},"rootNode":2,"rootOutcome":"PROVEN_LOSS","rootPn":"SAT","rootDn":0,"bestMove":-2,"bestMoveSgf":"","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":-1,"toPlay":2,"koPoint":-2,"consecutivePasses":1,"survivingTokensMask":1,"zobristHex":"521a242be549b09e","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":1},{"stateId":2,"parentStateId":1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":2,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":2}],"snapshotPool":[{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":1,"zobristHex":"06fe8925c3232e8b"},{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":2,"zobristHex":"521a242be549b09e"}],"historySnapshotIds":[[0],[0,1],[0,1,0]],"nodes":[{"nodeId":0,"stateId":2,"historyId":2,"parentStateId":1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"DOUBLE_PASS_RESOLUTION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":1,"historyId":1,"parentStateId":0,"isOrNode":false,"toPlay":"W","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[0],"childMoves":[-1],"prunedCertificate":null},{"nodeId":2,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[1],"childMoves":[-1],"prunedCertificate":null}],"checksum":"sha256-jcs:45e0d2056a775a1319ff19e9c491a4e6dd6a5fb308704eaa7663da59c1ca6804"})json";
  static const std::string kEmptyLossCompactEmptySgfJson = R"json({"magic":"lproof/1","encodingMode":"compact_dag","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[],"rawRegionPointCount":0,"isFullRegionSearch":true},"rootNode":2,"rootOutcome":"PROVEN_LOSS","rootPn":"SAT","rootDn":0,"bestMove":-2,"bestMoveSgf":"","nodes":[{"nodeId":0,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"DOUBLE_PASS_RESOLUTION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"isOrNode":false,"toPlay":"W","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[0],"childMoves":[-1],"prunedCertificate":null},{"nodeId":2,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[1],"childMoves":[-1],"prunedCertificate":null}],"checksum":"sha256-jcs:f83cc46ec4ce760c9652c1767556ab8b0d79ece0fb982c286f0f5a2d8f882c03"})json";
  static const std::string kEmptyLossCompactNullSgfJson = R"json({"magic":"lproof/1","encodingMode":"compact_dag","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[],"rawRegionPointCount":0,"isFullRegionSearch":true},"rootNode":2,"rootOutcome":"PROVEN_LOSS","rootPn":"SAT","rootDn":0,"bestMove":-2,"bestMoveSgf":null,"nodes":[{"nodeId":0,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"DOUBLE_PASS_RESOLUTION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"isOrNode":false,"toPlay":"W","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[0],"childMoves":[-1],"prunedCertificate":null},{"nodeId":2,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[1],"childMoves":[-1],"prunedCertificate":null}],"checksum":"sha256-jcs:af29aa57f169dc58867b638c038f00f62d001806927863db2958e99e8430caf9"})json";
  static const std::string kEmptyLossCompactBadSgfJson = R"json({"magic":"lproof/1","encodingMode":"compact_dag","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[],"rawRegionPointCount":0,"isFullRegionSearch":true},"rootNode":2,"rootOutcome":"PROVEN_LOSS","rootPn":"SAT","rootDn":0,"bestMove":-2,"bestMoveSgf":"pass","nodes":[{"nodeId":0,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"DOUBLE_PASS_RESOLUTION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"isOrNode":false,"toPlay":"W","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[0],"childMoves":[-1],"prunedCertificate":null},{"nodeId":2,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":"SAT","dn":0,"outcome":"PROVEN_LOSS","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[],"disproofRzCoords":[0,1,2,3,19,20,21,22],"childNodeIds":[1],"childMoves":[-1],"prunedCertificate":null}],"checksum":"sha256-jcs:0e8b049fa2e2818624f4ce860efb6e446f3225e1b7b7aeefb91d9af5a0b508ea"})json";

  const VerificationReport full_empty_sgf_ver =
      checker.VerifyLProofJsonString(kEmptyLossFullEmptySgfJson);
  const VerificationReport compact_empty_sgf_ver =
      checker.VerifyLProofJsonString(kEmptyLossCompactEmptySgfJson);
  const VerificationReport compact_null_sgf_ver =
      checker.VerifyLProofJsonString(kEmptyLossCompactNullSgfJson);
  const VerificationReport compact_bad_sgf_ver =
      checker.VerifyLProofJsonString(kEmptyLossCompactBadSgfJson);

  Check(full_empty_sgf_ver.passed && compact_empty_sgf_ver.passed &&
            compact_null_sgf_ver.passed,
        "R7 §3 PROVEN_LOSS bestMove=-2 with bestMoveSgf=\"\" and null PASS in full & compact encodings",
        "full=" + full_empty_sgf_ver.error_code +
            ", compact=" + compact_empty_sgf_ver.error_code +
            ", null=" + compact_null_sgf_ver.error_code);
  Check(full_empty_sgf_ver.canonical_dag_checksum == kExpectedEmptyLossCanon &&
            compact_empty_sgf_ver.canonical_dag_checksum ==
                kExpectedEmptyLossCanon &&
            compact_null_sgf_ver.canonical_dag_checksum ==
                kExpectedEmptyLossCanon,
        "R7 §3 PROVEN_LOSS bestMove=-2 canonical_dag_checksum matches TS verbatim across encodings");
  Check(!compact_bad_sgf_ver.passed &&
            compact_bad_sgf_ver.error_code == "LP-R02",
        "R7 §3 PROVEN_LOSS bestMove=-2 with bestMoveSgf=\"pass\" rejected -> LP-R02",
        "code=" + compact_bad_sgf_ver.error_code);

  // --- R7 §4 P2: UTF-16 Surrogate Pair Equivalence ("围棋🎯" vs "围棋\ud83c\udfaf") & Lone Surrogates ---
  static const std::string kExpectedUniDigest =
      "sha256-jcs:498b7de47533b5e7cd387836c0e5fa3e5e1963bd02dbea68dd48eab92952d599";
  static const std::string kUniUtf8Json = R"json({"magic":"lproof/1","encodingMode":"compact_dag","problemId":"p001_straight_three_live","context":{"contextId":"围棋🎯","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","nodes":[{"nodeId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:498b7de47533b5e7cd387836c0e5fa3e5e1963bd02dbea68dd48eab92952d599"})json";
  static const std::string kUniEscapedJson = R"json({"magic":"lproof/1","encodingMode":"compact_dag","problemId":"p001_straight_three_live","context":{"contextId":"围棋\ud83c\udfaf","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","nodes":[{"nodeId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:498b7de47533b5e7cd387836c0e5fa3e5e1963bd02dbea68dd48eab92952d599"})json";
  static const std::string kUniLoneHighJson = R"json({"magic":"lproof/1","encodingMode":"compact_dag","problemId":"p001_straight_three_live","context":{"contextId":"围棋\ud83c","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","nodes":[{"nodeId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:498b7de47533b5e7cd387836c0e5fa3e5e1963bd02dbea68dd48eab92952d599"})json";
  static const std::string kUniLoneLowJson = R"json({"magic":"lproof/1","encodingMode":"compact_dag","problemId":"p001_straight_three_live","context":{"contextId":"围棋\udfaf","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","nodes":[{"nodeId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:498b7de47533b5e7cd387836c0e5fa3e5e1963bd02dbea68dd48eab92952d599"})json";

  const VerificationReport uni_utf8_ver = checker.VerifyLProofJsonString(
      kUniUtf8Json, &p001, VerificationScope::kOriginalRoot);
  const VerificationReport uni_esc_ver = checker.VerifyLProofJsonString(
      kUniEscapedJson, &p001, VerificationScope::kOriginalRoot);
  Check(uni_utf8_ver.passed && uni_esc_ver.passed &&
            uni_utf8_ver.jcs_sha256_checksum == kExpectedUniDigest &&
            uni_esc_ver.jcs_sha256_checksum == kExpectedUniDigest &&
            uni_utf8_ver.canonical_dag_checksum == kExpectedUniDigest &&
            uni_esc_ver.canonical_dag_checksum == kExpectedUniDigest,
        "R7 §4 Literal UTF-8 \"围棋🎯\" and surrogate-escaped \"围棋\\ud83c\\udfaf\" both PASS with identical JCS & canonical digests",
        "utf8=" + uni_utf8_ver.error_code + ", esc=" + uni_esc_ver.error_code);

  const VerificationReport lone_high_ver =
      checker.VerifyLProofJsonString(kUniLoneHighJson);
  const VerificationReport lone_low_ver =
      checker.VerifyLProofJsonString(kUniLoneLowJson);
  Check(!lone_high_ver.passed && lone_high_ver.error_code == "LP-J01" &&
            !lone_low_ver.passed && lone_low_ver.error_code == "LP-J01",
        "R7 §4 Lone UTF-16 high/low surrogates rejected -> LP-J01",
        "high=" + lone_high_ver.error_code + ", low=" + lone_low_ver.error_code);
}

void TestSection5R8ProblemContractAndConsistency() {
  std::cout << "\n=== 5. R8 Problem Contract, Reverse-Witness & Type Safety ===\n";
  ProblemContractParser<19> parser;
  ProofArtifactManager<19> checker;

  static const std::string kTwoStoneAbsentJson =
      R"json({"masked_sgf_str":"(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa])","winning_color":"B","turn_color":"B","black_search_goal":"TOKILL","white_search_goal":"TOLIVE","black_crucial_stone":"aa","white_crucial_stone":"aa","black_ko_rule":"allow_ko","white_ko_rule":"allow_ko"})json";
  static const std::string kTwoStoneEmptyJson =
      R"json({"masked_sgf_str":"(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa])","winning_color":"B","turn_color":"B","black_search_goal":"TOKILL","white_search_goal":"TOLIVE","black_crucial_stone":"aa","white_crucial_stone":"aa","black_ko_rule":"allow_ko","white_ko_rule":"allow_ko","region":""})json";
  static const std::string kTwoStoneMaJson =
      R"json({"masked_sgf_str":"(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa]MA[aa][ab][ba])","winning_color":"B","turn_color":"B","black_search_goal":"TOKILL","white_search_goal":"TOLIVE","black_crucial_stone":"aa","white_crucial_stone":"aa","black_ko_rule":"allow_ko","white_ko_rule":"allow_ko"})json";
  static const std::string kTwoStoneExplicitJson =
      R"json({"masked_sgf_str":"(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa])","winning_color":"B","turn_color":"B","black_search_goal":"TOKILL","white_search_goal":"TOLIVE","black_crucial_stone":"aa","white_crucial_stone":"aa","black_ko_rule":"allow_ko","white_ko_rule":"allow_ko","region":"aa,ab,ba"})json";
  static const std::string kTwoStoneInvalidRegionJson =
      R"json({"masked_sgf_str":"(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa])","winning_color":"B","turn_color":"B","black_search_goal":"TOKILL","white_search_goal":"TOLIVE","black_crucial_stone":"aa","white_crucial_stone":"aa","black_ko_rule":"allow_ko","white_ko_rule":"allow_ko","region":"aa,zz"})json";

  const ParsedProblem<19> p_absent = parser.ParseTsumegoJsonObject(
      "r8_two_stone_absent", kTwoStoneAbsentJson,
      TurnConflictPolicy::kRejectStrict);
  const ParsedProblem<19> p_empty = parser.ParseTsumegoJsonObject(
      "r8_two_stone_empty", kTwoStoneEmptyJson,
      TurnConflictPolicy::kRejectStrict);
  const ParsedProblem<19> p_ma = parser.ParseTsumegoJsonObject(
      "r8_two_stone_ma", kTwoStoneMaJson, TurnConflictPolicy::kRejectStrict);
  const ParsedProblem<19> p_explicit = parser.ParseTsumegoJsonObject(
      "r8_two_stone_explicit", kTwoStoneExplicitJson,
      TurnConflictPolicy::kRejectStrict);
  const ParsedProblem<19> p_invalid = parser.ParseTsumegoJsonObject(
      "r8_two_stone_invalid", kTwoStoneInvalidRegionJson,
      TurnConflictPolicy::kRejectStrict);

  Check(p_absent.valid && !p_absent.region_search_mask.has_value() &&
            !p_absent.initial_position.ImmortalWall().Any(),
        "R8 §1 absent region -> unrestricted, empty immortal wall");
  Check(p_empty.valid && !p_empty.region_search_mask.has_value() &&
            !p_empty.initial_position.ImmortalWall().Any(),
        "R8 §1 empty region=\"\" -> unrestricted, empty immortal wall");
  Check(p_ma.valid && p_ma.region_search_mask.has_value() &&
            p_ma.region_search_mask->ToCoords() == std::vector<int>({0, 1, 19}) &&
            !p_ma.initial_position.ImmortalWall().Any(),
        "R8 §1 SGF MA[aa][ab][ba] -> region={0,1,19}, empty immortal wall");
  Check(p_explicit.valid && p_explicit.region_search_mask.has_value() &&
            p_explicit.region_search_mask->ToCoords() ==
                std::vector<int>({0, 1, 19}) &&
            !p_explicit.initial_position.ImmortalWall().Any(),
        "R8 §1 explicit region=\"aa,ab,ba\" -> region={0,1,19}, empty immortal wall");
  Check(!p_invalid.valid && p_invalid.error_code == "FR1-INVALID-REGION-COORD",
        "R8 §1 invalid region coordinate \"zz\" rejected -> FR1-INVALID-REGION-COORD",
        "code=" + p_invalid.error_code);

  struct TwoStoneCase {
    std::string label;
    const ParsedProblem<19>* prob;
  };
  const std::vector<TwoStoneCase> variants = {
      {"absent", &p_absent},
      {"empty", &p_empty},
      {"MA", &p_ma},
      {"explicit", &p_explicit},
  };
  for (const auto& vc : variants) {
    DfpnSolver<19> solver(DefaultConfig(200U));
    const SolveReport<19> rep = solver.Solve(
        vc.prob->initial_position, vc.prob->proof_context,
        vc.prob->region_search_mask, vc.prob->problem_id);
    Check(rep.root_status == ProofOutcome::kProvenWin && rep.best_move == 1 &&
              rep.proof_dag_nodes.size() == 2U,
          "R8 §1 native two-stone (" + vc.label +
              ") proves PROVEN_WIN best_move=ba(1) in 2 DAG nodes",
          "best=" + std::to_string(rep.best_move) + ", dag=" +
              std::to_string(rep.proof_dag_nodes.size()));
    const VerificationReport mem = checker.VerifyProofDag(
        vc.prob->initial_position, vc.prob->proof_context, rep,
        VerificationScope::kOriginalRoot);
    const std::string json = checker.SerializeLProofJson(
        vc.prob->initial_position, vc.prob->proof_context, rep);
    const VerificationReport file = checker.VerifyLProofJsonString(
        json, vc.prob, VerificationScope::kOriginalRoot);
    Check(mem.passed && file.passed &&
              mem.canonical_dag_checksum == file.canonical_dag_checksum,
          "R8 §1 native two-stone (" + vc.label +
              ") passes memory & external-bound file check",
          "mem=" + mem.error_code + ", file=" + file.error_code);
  }

  // R8 §1 Cross-engine check: exact TS-generated full_state_table proof for the
  // absent-region two-stone JSON must PASS C++ external binding on absent & empty,
  // and FAIL with LP-P01 when bound against explicit region.
  static const std::string kTwoStoneTsFullJson = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"r8_two_stone_absent","context":{"contextId":"ctx_r8_two_stone_absent_SSK_TOKILL_ako1_dko1","rootAttacker":"B","attackerGoal":"TOKILL","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":true,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":0,"groupIndex":0,"stoneColor":"W"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"e322fbc46ef60882","inputHash":"e322fbc46ef60882","blackInitialCoords":[19],"whiteInitialCoords":[0],"immortalWallCoords":[],"hasRegionHint":false,"regionCoords":[],"rawRegionPointCount":0,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"e322fbc46ef60882","blackCoords":[19],"whiteCoords":[0],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":1,"toPlay":2,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":0,"zobristHex":"58276c71cdd50290","blackCoords":[1,19],"whiteCoords":[],"historyId":1}],"snapshotPool":[{"blackCoords":[19],"whiteCoords":[0],"toPlay":1,"zobristHex":"e322fbc46ef60882"},{"blackCoords":[1,19],"whiteCoords":[],"toPlay":2,"zobristHex":"58276c71cdd50290"}],"historySnapshotIds":[[0],[0,1]],"nodes":[{"nodeId":0,"stateId":1,"historyId":1,"parentStateId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"TOKENS_CAPTURED","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:9062b66a10cf7ac2f743948aa742503b671b4a04b1033f2703cc8f0980658007"})json";
  static const std::string kExpectedTwoStoneCanon =
      "sha256-jcs:983f2e13180e0ffca139ab2d2b1199b8a6d91f62a9afb95e40c11ea122604f2b";

  const VerificationReport ts_bind_absent = checker.VerifyLProofJsonString(
      kTwoStoneTsFullJson, &p_absent, VerificationScope::kOriginalRoot);
  const VerificationReport ts_bind_empty = checker.VerifyLProofJsonString(
      kTwoStoneTsFullJson, &p_empty, VerificationScope::kOriginalRoot);
  const VerificationReport ts_bind_explicit = checker.VerifyLProofJsonString(
      kTwoStoneTsFullJson, &p_explicit, VerificationScope::kOriginalRoot);

  Check(ts_bind_absent.passed && ts_bind_empty.passed &&
            ts_bind_absent.canonical_dag_checksum == kExpectedTwoStoneCanon &&
            !ts_bind_explicit.passed && ts_bind_explicit.error_code == "LP-P01",
        "R8 §1 TS two-stone absent-region proof cross-verifies against C++ absent/empty (PASS + canonical match) and rejects explicit (LP-P01)",
        "absent=" + ts_bind_absent.error_code +
            ", empty=" + ts_bind_empty.error_code +
            ", explicit=" + ts_bind_explicit.error_code);

  // R8 §2: full_state_table reverse witness (p001 ba with hasRegionHint=true, regionCoords=[]) -> LP-R02
  static const std::string kReverseEmptyRegionFullJson = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":true,"regionCoords":[],"rawRegionPointCount":0,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":1,"toPlay":2,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"012424dc168fb64a","blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":1}],"snapshotPool":[{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":1,"zobristHex":"06fe8925c3232e8b"},{"blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":2,"zobristHex":"012424dc168fb64a"}],"historySnapshotIds":[[0],[0,1]],"nodes":[{"nodeId":0,"stateId":1,"historyId":1,"parentStateId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:5310134b5d32ec2db4edcf0d43b54016ce2d60dd3ef1a78094144b7f6deff1f4"})json";
  const VerificationReport rev_full_ver =
      checker.VerifyLProofJsonString(kReverseEmptyRegionFullJson);
  Check(!rev_full_ver.passed && rev_full_ver.error_code == "LP-R02",
        "R8 §2 full_state_table reverse witness (p001 ba with hasRegionHint=true, regionCoords=[]) -> LP-R02",
        "code=" + rev_full_ver.error_code);

  // R8 §3: Non-boolean problemSetup.hasRegionHint ("false") rejected -> LP-J02
  static const std::string kBadTypeHasRegionHintJson = R"json({"magic":"lproof/1","encodingMode":"full_state_table","problemId":"p001_straight_three_live","context":{"contextId":"ctx_p001_straight_three_live_SSK_TOLIVE_ako0_dko1","rootAttacker":"B","attackerGoal":"TOLIVE","crucialStoneOp":"SINGLE","koRule":"SSK","attackerAllowKo":false,"defenderAllowKo":true,"initialTokens":[{"tokenId":0,"initialCoord":20,"groupIndex":0,"stoneColor":"B"}]},"problemSetup":{"boardSize":19,"rootKind":"initial","firstToPlay":"B","koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","inputHash":"06fe8925c3232e8b","blackInitialCoords":[3,19,20,21,22],"whiteInitialCoords":[4,23,38,39,40,41,42],"immortalWallCoords":[4,23,38,39,40,41,42],"hasRegionHint":"false","regionCoords":[0,1,2],"rawRegionPointCount":3,"isFullRegionSearch":true},"rootNode":1,"rootOutcome":"PROVEN_WIN","rootPn":0,"rootDn":"SAT","bestMove":1,"bestMoveSgf":"ba","stateTable":[{"stateId":0,"parentStateId":-1,"moveFromParent":-1,"toPlay":1,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"06fe8925c3232e8b","blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":0},{"stateId":1,"parentStateId":0,"moveFromParent":1,"toPlay":2,"koPoint":-2,"consecutivePasses":0,"survivingTokensMask":1,"zobristHex":"012424dc168fb64a","blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"historyId":1}],"snapshotPool":[{"blackCoords":[3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":1,"zobristHex":"06fe8925c3232e8b"},{"blackCoords":[1,3,19,20,21,22],"whiteCoords":[4,23,38,39,40,41,42],"toPlay":2,"zobristHex":"012424dc168fb64a"}],"historySnapshotIds":[[0],[0,1]],"nodes":[{"nodeId":0,"stateId":1,"historyId":1,"parentStateId":0,"isOrNode":false,"toPlay":"W","incomingMove":1,"incomingMoveSgf":"ba","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"BENSON_UCA","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[],"childMoves":[],"prunedCertificate":null},{"nodeId":1,"stateId":0,"historyId":0,"parentStateId":-1,"isOrNode":true,"toPlay":"B","incomingMove":-1,"incomingMoveSgf":"pass","pn":0,"dn":"SAT","outcome":"PROVEN_WIN","terminalEvidence":"INTERNAL_AGGREGATION","isPrunedOutsideRz":false,"isTtHit":false,"isKoDependentBarrier":false,"sourceProofNodeId":null,"proofRzCoords":[0,1,2,3,19,20,21,22],"disproofRzCoords":[],"childNodeIds":[0],"childMoves":[1],"prunedCertificate":null}],"checksum":"sha256-jcs:c20fe69021ba3702513c0eeebffd5980e4617db03f56b4a62b3d9ad96cc8bdda"})json";
  const VerificationReport bad_type_ver =
      checker.VerifyLProofJsonString(kBadTypeHasRegionHintJson);
  Check(!bad_type_ver.passed && bad_type_ver.error_code == "LP-J02",
        "R8 §3 Non-boolean problemSetup.hasRegionHint=\"false\" rejected -> LP-J02",
        "code=" + bad_type_ver.error_code);
}

void TestSection6RealProblemSolverBreakthrough() {
  std::cout << "\n=== 6. Real Study-LD-RZ Solver Breakthrough (p042 & p031) ===\n";
  ProblemContractParser<19> parser;
  ProofArtifactManager<19> checker;

  const std::string& kCommonRegion = CommonChaoRegion19();

  const std::string p042_json =
      std::string(
          R"json({"masked_sgf_str":"(;FF[4]CA[UTF-8]SZ[19]KM[6]AB[or][pr][qr][rr][rq][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[lr][nr][nq][oq][pq][qq][ap][bp][cp][dp][ep][fp][gp][hp][ip][rp][io][qo][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[or]MA[as][bs][cs][ds][es][fs][gs][hs][is][js][ks][ls][ms][ns][os][ps][qs][rs][ss][ar][br][cr][dr][er][fr][gr][hr][ir][jr][kr][lr][mr][nr][or][pr][qr][rr][sr][aq][bq][cq][dq][eq][fq][gq][hq][iq][jq][kq][lq][mq][nq][oq][pq][qq][rq][sq][jp][kp][lp][mp][np][op][pp][qp][rp][sp][jo][ko][lo][mo][no][oo][po][qo][ro][so][jn][kn][ln][mn][nn][on][pn][qn][rn][sn][jm][km][lm][mm][nm][om][pm][qm][rm][sm][jl][kl][ll][ml][nl][ol][pl][ql][rl][sl][jk][kk][lk][mk][nk][ok][pk][qk][rk][sk][kj][lj][mj][nj][oj][pj][qj][rj][sj][qi][ri][si][qh][rh][sh][qg][rg][sg][qf][rf][sf][qe][re][se][qd][rd][sd][qc][rc][sc][qb][rb][sb][qa][ra][sa])","winning_color":"b","turn_color":"b","black_crucial_stone":"or","white_crucial_stone":"","black_search_goal":"TOLIVE","white_search_goal":"TOKILL","black_ko_rule":"disallow_ko","white_ko_rule":"allow_ko","region":")json") +
      kCommonRegion + "\"}";

  SolverConfig real_cfg = DefaultConfig(3500U);
  real_cfg.max_depth = 48U;
  real_cfg.memory_budget_bytes = 512ULL * 1024ULL * 1024ULL;

  // 1. chao_vol1_p042: must prove PROVEN_WIN under <= 1000 nodes with RZ pruning
  const ParsedProblem<19> p042 = parser.ParseTsumegoJsonObject(
      "chao_vol1_p042", p042_json, TurnConflictPolicy::kRejectStrict);
  Check(p042.valid && p042.region_search_mask.has_value(),
        "Real-problem p042 parses cleanly with full region");
  if (p042.valid) {
    DfpnSolver<19> solver(real_cfg);
    const SolveReport<19> rep = solver.Solve(
        p042.initial_position, p042.proof_context, p042.region_search_mask,
        p042.problem_id);
    Check(rep.root_status == ProofOutcome::kProvenWin &&
              rep.num_nodes <= 1000U && rep.pruned_outside_rz_count > 0U,
          "Native C++20 solves p042 as PROVEN_WIN within <= 1000 nodes with RZ pruning",
          "nodes=" + std::to_string(rep.num_nodes) + ", pruned=" +
              std::to_string(rep.pruned_outside_rz_count));
    const VerificationReport mem = checker.VerifyProofDag(
        p042.initial_position, p042.proof_context, rep,
        VerificationScope::kOriginalRoot);
    const std::string lproof = checker.SerializeLProofJson(
        p042.initial_position, p042.proof_context, rep);
    const VerificationReport file = checker.VerifyLProofJsonString(
        lproof, &p042, VerificationScope::kOriginalRoot);
    Check(mem.passed && file.passed &&
              mem.canonical_dag_checksum == file.canonical_dag_checksum,
          "Native C++20 p042 passes memory & external-bound original_root verification",
          "mem=" + mem.error_code + ", file=" + file.error_code);
  }

  // 2. chao_vol1_p031: must prove PROVEN_WIN with B[sr] under 3500-node budget
  const ParsedProblem<19> p031 = BuildP031();
  Check(p031.valid && p031.region_search_mask.has_value(),
        "Real-problem p031 parses cleanly with full region");
  if (p031.valid) {
    DfpnSolver<19> solver(real_cfg);
    const SolveReport<19> rep = solver.Solve(
        p031.initial_position, p031.proof_context, p031.region_search_mask,
        p031.problem_id);
    const int16_t kMoveSr =
        static_cast<int16_t>(Position<19>::CoordFromRowCol(17, 18));
    Check(rep.root_status == ProofOutcome::kProvenWin &&
              rep.best_move == kMoveSr && rep.num_nodes <= 3500U &&
              rep.pruned_outside_rz_count > 0U,
          "Native C++20 solves p031 as PROVEN_WIN best_move=sr within 3500 nodes with RZ pruning",
          "best=" + std::to_string(rep.best_move) + ", nodes=" +
              std::to_string(rep.num_nodes) + ", pruned=" +
              std::to_string(rep.pruned_outside_rz_count));
    const VerificationReport mem = checker.VerifyProofDag(
        p031.initial_position, p031.proof_context, rep,
        VerificationScope::kOriginalRoot);
    const std::string lproof = checker.SerializeLProofJson(
        p031.initial_position, p031.proof_context, rep);
    const VerificationReport file = checker.VerifyLProofJsonString(
        lproof, &p031, VerificationScope::kOriginalRoot);
    Check(mem.passed && file.passed &&
              mem.canonical_dag_checksum == file.canonical_dag_checksum,
          "Native C++20 p031 passes memory & external-bound original_root verification",
          "mem=" + mem.error_code + ", file=" + file.error_code);

    std::string lproof_off_cs;
    std::string lproof_on_cs;
    (void)checker.SerializeLProofJson(
        p031.initial_position, p031.proof_context, rep, &lproof_off_cs);

    SolverConfig prof_cfg = real_cfg;
    prof_cfg.enable_stage_profiling = true;
    DfpnSolver<19> prof_solver(prof_cfg);
    const SolveReport<19> prof_rep = prof_solver.Solve(
        p031.initial_position, p031.proof_context, p031.region_search_mask,
        p031.problem_id);
    (void)checker.SerializeLProofJson(
        p031.initial_position, p031.proof_context, prof_rep, &lproof_on_cs);

    const auto& st = prof_solver.StageProfile();
    const uint64_t reval_ns =
        st.reval_by_caller[0].inclusive_ns +
        st.reval_by_caller[1].inclusive_ns +
        st.reval_by_caller[2].inclusive_ns;
    const uint64_t accounted_ns =
        st.benson_main_ns + st.tt.board_lookup_exclusive_ns +
        st.tt.pattern_scan_exclusive_ns + reval_ns +
        st.outside_rz_play_move_ns + st.frontier_tctx_ns +
        st.frontier_gen_legal_ns + st.cand_eval_exclusive_ns + st.benson_cand_ns +
        st.frontier_sort_init_ns + st.main_play_undo_ns + st.rz_compute_ns +
        st.tt.board_store_ns + st.tt.pattern_store_ns;
    const uint64_t reval_leaf_ns =
        st.reval_cache_lookup_ns + st.benson_replay_ns +
        st.reval_witness_play_move_ns + st.reval_universal_gen_legal_ns +
        st.reval_universal_edge_scan_ns + st.reval_universal_play_move_ns;
    Check(prof_rep.num_nodes == rep.num_nodes &&
              prof_rep.root_status == rep.root_status &&
              prof_rep.best_move == rep.best_move &&
              prof_rep.pruned_outside_rz_count == rep.pruned_outside_rz_count &&
              !lproof_off_cs.empty() && lproof_off_cs == lproof_on_cs,
          "R22 stage profiling ON/OFF preserves exact p031 node count, status & proof checksum",
          "nodes=" + std::to_string(prof_rep.num_nodes) + "/" +
              std::to_string(rep.num_nodes) + ", csMatch=" +
              std::string(lproof_off_cs == lproof_on_cs ? "1" : "0"));
    Check(st.enabled && st.benson_main_calls == prof_rep.num_nodes &&
              st.new_frontiers > 0U &&
              st.candidates_generated >= st.candidates_scored &&
              st.solve_total_ns > 0U && accounted_ns <= st.solve_total_ns &&
              reval_leaf_ns <= reval_ns,
          "R22 stage profiling records exact exclusive stage sums <= solve_total_ns & reval_leaf_ns <= reval_ns",
          "bensonMain=" + std::to_string(st.benson_main_calls) +
              ", nodes=" + std::to_string(prof_rep.num_nodes) +
              ", accounted=" + std::to_string(accounted_ns) +
              ", total=" + std::to_string(st.solve_total_ns));

    // Real p031 defensive line: B[sr] -> W[pass] -> B[qs] forms two tiger's mouths (rs, ss)
    Position<19> p31_pos = p031.initial_position;
    const int16_t kMoveQs =
        static_cast<int16_t>(Position<19>::CoordFromRowCol(18, 16));
    const bool ok_sr = p31_pos.PlayMove(kMoveSr);
    const bool ok_pass = p31_pos.PlayMove(ldprover::kPassMove);
    const bool ok_qs = p31_pos.PlayMove(kMoveQs);
    const int p31_eye =
        DfpnSolver<19>::EstimateParentEyeLikeCount(p31_pos, p031.proof_context);
    const int32_t p31_pass =
        solver.EvaluatePassMoveScore(p31_pos, p031.proof_context, false);
    SolverConfig no_order_cfg = real_cfg;
    no_order_cfg.enable_fast_capture_ordering = false;
    DfpnSolver<19> solver_no_order(no_order_cfg);
    const int32_t p31_pass_no_order =
        solver_no_order.EvaluatePassMoveScore(p31_pos, p031.proof_context, false);
    Check(ok_sr && ok_pass && ok_qs && p31_eye == 2 && p31_pass == 3850 &&
              p31_pass_no_order == 0,
          "R9/R10 §1 p031 after B[sr]->W[pass]->B[qs] yields eyeLike=2, PASS score=3850 (ordering on) and 0 (ordering off)",
          "eyeLike=" + std::to_string(p31_eye) +
              ", passScore=" + std::to_string(p31_pass) +
              ", passNoOrder=" + std::to_string(p31_pass_no_order));
  }
}

void TestSection7R9EyeLikePassParity() {
  std::cout << "\n=== 7. R9 §1 Eye-Like Heuristic & AND-Node PASS Score Parity ===\n";
  ProblemContractParser<19> parser;

  SolverConfig cfg_rz = DefaultConfig(3500U);
  cfg_rz.max_depth = 48U;
  cfg_rz.enable_rz_pruning = true;

  SolverConfig cfg_no_rz = cfg_rz;
  cfg_no_rz.enable_rz_pruning = false;

  DfpnSolver<19> solver_rz(cfg_rz);
  DfpnSolver<19> solver_no_rz(cfg_no_rz);

  struct EyeShapeCase {
    std::string name;
    std::string sgf;
    std::string crucial;
    int expected_eye_like;
    int32_t expected_pass_rz;
    int32_t expected_pass_no_rz;
  };

  const std::vector<EyeShapeCase> cases = {
      {"full_eye_corner",
       "(;GM[1]FF[4]SZ[19]PL[W]AB[ba][ab][bb]AW[dd])",
       "bb",
       2,
       3850,
       3850},
      {"single_tiger_mouth",
       "(;GM[1]FF[4]SZ[19]PL[W]AB[ba][bb][cb]AW[dd])",
       "bb",
       1,
       3450,
       360},
      {"double_tiger_mouth",
       "(;GM[1]FF[4]SZ[19]PL[W]AB[ca][cb][cc][dc][ec][eb][ea]AW[gg])",
       "dc",
       2,
       3850,
       3850},
      {"diag_enemy_full_eye",
       "(;GM[1]FF[4]SZ[19]PL[W]AB[ba][ab][ca][cb][cc][bc][ac]AW[bb])",
       "ba",
       2,
       3850,
       3850},
  };

  for (const auto& tc : cases) {
    const std::string raw_json =
        std::string("{\"masked_sgf_str\":\"") + tc.sgf +
        "\",\"winning_color\":\"b\",\"turn_color\":\"w\","
        "\"black_crucial_stone\":\"" +
        tc.crucial +
        "\",\"white_crucial_stone\":\"\",\"black_search_goal\":\"TOLIVE\","
        "\"white_search_goal\":\"TOKILL\",\"black_ko_rule\":\"disallow_ko\","
        "\"white_ko_rule\":\"allow_ko\","
        "\"region\":\"aa,ba,ca,da,ab,bb,cb,db,ac,bc,cc,dc\"}";
    const ParsedProblem<19> parsed = parser.ParseTsumegoJsonObject(
        "r9_eye_" + tc.name, raw_json, TurnConflictPolicy::kRejectStrict);
    Check(parsed.valid, "R9 §1 eye-shape fixture parses cleanly: " + tc.name,
          parsed.error_message);
    if (!parsed.valid) continue;

    const int eye_like = DfpnSolver<19>::EstimateParentEyeLikeCount(
        parsed.initial_position, parsed.proof_context);
    const int32_t pass_rz = solver_rz.EvaluatePassMoveScore(
        parsed.initial_position, parsed.proof_context, false);
    const int32_t pass_no_rz = solver_no_rz.EvaluatePassMoveScore(
        parsed.initial_position, parsed.proof_context, false);
    Check(eye_like == tc.expected_eye_like &&
              pass_rz == tc.expected_pass_rz &&
              pass_no_rz == tc.expected_pass_no_rz,
          "R9 §1 eye-shape " + tc.name + " matches TS eyeLike & PASS scores",
          "got eyeLike=" + std::to_string(eye_like) +
              ", passRz=" + std::to_string(pass_rz) +
              ", passNoRz=" + std::to_string(pass_no_rz));
  }
}

template <int N>
void AssertGenerateLegalMovesMatchesReference(
    const Position<N>& pos,
    const std::type_identity_t<std::optional<BitBoard<N>>>& region_hint,
    const std::string& label) {
  const BitBoard<N> b_before = pos.Stones(ldprover::Color::kBlack);
  const BitBoard<N> w_before = pos.Stones(ldprover::Color::kWhite);
  const BitBoard<N> wall_before = pos.ImmortalWall();
  const ldprover::Color to_play_before = pos.ToPlay();
  const int16_t ko_before = pos.KoPoint();
  const uint8_t passes_before = pos.ConsecutivePasses();
  const uint64_t tok_before = pos.SurvivingTargetTokensMask();
  const uint64_t hash_before = pos.ZobristHash();
  const auto hist_before = pos.HistorySnapshots();
  const auto trace_before = pos.PlayedMoveTrace();

  const std::vector<int16_t> actual = pos.GenerateLegalMoves(region_hint);

  std::vector<int16_t> expected;
  if (!pos.IsAtDoublePass()) {
    for (int coord = 0; coord < N * N; ++coord) {
      if (region_hint.has_value() && !region_hint->Get(coord)) continue;
      if (pos.IsLegalMove(static_cast<int16_t>(coord))) {
        expected.push_back(static_cast<int16_t>(coord));
      }
    }
    expected.push_back(ldprover::kPassMove);
  }

  bool hist_unchanged = (hist_before.size() == pos.HistorySnapshots().size());
  if (hist_unchanged) {
    for (size_t i = 0; i < hist_before.size(); ++i) {
      const auto& a = hist_before[i];
      const auto& b = pos.HistorySnapshots()[i];
      if (a.black_stones != b.black_stones || a.white_stones != b.white_stones ||
          a.to_play != b.to_play || a.zobrist_hash != b.zobrist_hash) {
        hist_unchanged = false;
        break;
      }
    }
  }
  const bool pos_unchanged =
      (pos.Stones(ldprover::Color::kBlack) == b_before) &&
      (pos.Stones(ldprover::Color::kWhite) == w_before) &&
      (pos.ImmortalWall() == wall_before) &&
      (pos.ToPlay() == to_play_before) && (pos.KoPoint() == ko_before) &&
      (pos.ConsecutivePasses() == passes_before) &&
      (pos.SurvivingTargetTokensMask() == tok_before) &&
      (pos.ZobristHash() == hash_before) && hist_unchanged &&
      (pos.PlayedMoveTrace() == trace_before);

  Check(actual == expected && pos_unchanged,
        "GenerateLegalMoves matches reference IsLegalMove order & mutates zero state: " +
            label,
        "actualSize=" + std::to_string(actual.size()) +
            ", expectedSize=" + std::to_string(expected.size()) +
            ", posUnchanged=" + std::string(pos_unchanged ? "1" : "0"));
}

template <int N>
void RunSuperko18CellForSize() {
  const int c_aa = Position<N>::CoordFromRowCol(0, 0);
  const int c_ab = Position<N>::CoordFromRowCol(1, 0);
  const int c_ba = Position<N>::CoordFromRowCol(0, 1);
  const int c_bb = Position<N>::CoordFromRowCol(1, 1);
  const int c_ca = Position<N>::CoordFromRowCol(0, 2);
  const int c_cb = Position<N>::CoordFromRowCol(1, 2);
  const int c_da = Position<N>::CoordFromRowCol(0, 3);

  for (const ldprover::KoRule rule :
       {ldprover::KoRule::kSituationalSuperko,
        ldprover::KoRule::kPositionalSuperko,
        ldprover::KoRule::kSimpleKoOnly}) {
    ldprover::ProofContext ctx;
    ctx.context_id = 0x515253ULL + static_cast<uint64_t>(N);
    ctx.root_attacker = ldprover::Color::kBlack;
    ctx.attacker_goal = ldprover::SearchGoal::kToLive;
    ctx.ko_rule = rule;
    ctx.attacker_allow_ko = true;
    ctx.defender_allow_ko = true;

    // Path 1: AB[bb][cb][da] AW[ab][ba][ca], PL[B] -> B[aa], W[ba], B[pass]
    Position<N> pos1(ctx);
    pos1.SetupInitialStone(c_bb, ldprover::Color::kBlack);
    pos1.SetupInitialStone(c_cb, ldprover::Color::kBlack);
    pos1.SetupInitialStone(c_da, ldprover::Color::kBlack);
    pos1.SetupInitialStone(c_ab, ldprover::Color::kWhite);
    pos1.SetupInitialStone(c_ba, ldprover::Color::kWhite);
    pos1.SetupInitialStone(c_ca, ldprover::Color::kWhite);
    pos1.FinalizeInitialPosition(ldprover::Color::kBlack);
    const bool p1_m1 = pos1.PlayMove(static_cast<int16_t>(c_aa));
    const bool p1_m2 = pos1.PlayMove(static_cast<int16_t>(c_ba));
    const bool p1_m3 = pos1.PlayMove(ldprover::kPassMove);

    // Path 2: AB[bb][cb][da] AW[ab][ba], PL[B] -> B[pass]
    Position<N> pos2(ctx);
    pos2.SetupInitialStone(c_bb, ldprover::Color::kBlack);
    pos2.SetupInitialStone(c_cb, ldprover::Color::kBlack);
    pos2.SetupInitialStone(c_da, ldprover::Color::kBlack);
    pos2.SetupInitialStone(c_ab, ldprover::Color::kWhite);
    pos2.SetupInitialStone(c_ba, ldprover::Color::kWhite);
    pos2.FinalizeInitialPosition(ldprover::Color::kBlack);
    const bool p2_m1 = pos2.PlayMove(ldprover::kPassMove);

    const bool expected_ca_legal_p1 = (rule == ldprover::KoRule::kSimpleKoOnly);
    const bool expected_ca_legal_p2 = true;

    const bool same_board_hash =
        (pos1.Stones(ldprover::Color::kBlack) ==
         pos2.Stones(ldprover::Color::kBlack)) &&
        (pos1.Stones(ldprover::Color::kWhite) ==
         pos2.Stones(ldprover::Color::kWhite)) &&
        (pos1.ToPlay() == pos2.ToPlay()) &&
        (pos1.KoPoint() == pos2.KoPoint()) &&
        (pos1.ConsecutivePasses() == pos2.ConsecutivePasses()) &&
        (pos1.ZobristHash() == pos2.ZobristHash()) &&
        (N != 19 || pos1.ZobristHash() == 6044147128762452085ULL);

    const std::string tag =
        "N=" + std::to_string(N) + ",rule=" + std::to_string(static_cast<int>(rule));
    AssertGenerateLegalMovesMatchesReference(pos1, std::nullopt, "p1_" + tag);
    AssertGenerateLegalMovesMatchesReference(pos2, std::nullopt, "p2_" + tag);

    const auto moves1 = pos1.GenerateLegalMoves(std::nullopt);
    const auto moves2 = pos2.GenerateLegalMoves(std::nullopt);
    const bool gen_ca_p1 =
        std::find(moves1.begin(), moves1.end(), static_cast<int16_t>(c_ca)) !=
        moves1.end();
    const bool gen_ca_p2 =
        std::find(moves2.begin(), moves2.end(), static_cast<int16_t>(c_ca)) !=
        moves2.end();
    Position<N> try1 = pos1;
    Position<N> try2 = pos2;
    const bool play_ca_p1 = try1.PlayMove(static_cast<int16_t>(c_ca));
    const bool play_ca_p2 = try2.PlayMove(static_cast<int16_t>(c_ca));

    Check(p1_m1 && p1_m2 && p1_m3 && p2_m1 && same_board_hash &&
              gen_ca_p1 == expected_ca_legal_p1 &&
              pos1.IsLegalMove(static_cast<int16_t>(c_ca)) == expected_ca_legal_p1 &&
              play_ca_p1 == expected_ca_legal_p1 &&
              gen_ca_p2 == expected_ca_legal_p2 &&
              pos2.IsLegalMove(static_cast<int16_t>(c_ca)) == expected_ca_legal_p2 &&
              play_ca_p2 == expected_ca_legal_p2,
          "R22 §4 18-cell superko equivalence check (" + tag + ")",
          "hash=" + std::to_string(pos1.ZobristHash()) +
              ", gen1=" + std::to_string(gen_ca_p1) +
              ", gen2=" + std::to_string(gen_ca_p2));
  }
}

void TestSection8GenerateLegalMovesSemantics() {
  std::cout << "\n=== 8. R22 §4/§5 GenerateLegalMoves Semantic Guard (18-Cell Superko & Edge Cases) ===\n";
  RunSuperko18CellForSize<5>();
  RunSuperko18CellForSize<7>();
  RunSuperko18CellForSize<19>();

  // Edge Case A: Suicide, Crucial-Token Capture, and Immortal Wall on 5x5
  {
    ldprover::ProofContext ctx;
    ctx.context_id = 0xAA01ULL;
    ctx.root_attacker = ldprover::Color::kBlack;
    ctx.attacker_goal = ldprover::SearchGoal::kToKill;
    ctx.ko_rule = ldprover::KoRule::kSituationalSuperko;
    ctx.attacker_allow_ko = true;
    ctx.defender_allow_ko = true;
    ctx.initial_tokens.push_back(
        {0U, static_cast<int16_t>(Position<5>::CoordFromRowCol(0, 1)), 0U,
         ldprover::Color::kWhite});

    // W[ba] in atari on aa; W[ea,db] is immortal wall with single empty point da.
    Position<5> edge_pos(ctx);
    edge_pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 0),
                               ldprover::Color::kBlack);
    edge_pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 1),
                               ldprover::Color::kBlack);
    edge_pos.SetupInitialStone(Position<5>::CoordFromRowCol(0, 2),
                               ldprover::Color::kBlack);
    edge_pos.SetupInitialStone(Position<5>::CoordFromRowCol(0, 1),
                               ldprover::Color::kWhite);
    edge_pos.SetupInitialStone(Position<5>::CoordFromRowCol(0, 4),
                               ldprover::Color::kWhite);
    edge_pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 3),
                               ldprover::Color::kBlack);
    edge_pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 4),
                               ldprover::Color::kBlack);
    BitBoard<5> wall;
    wall.Set(Position<5>::CoordFromRowCol(0, 4), true);
    edge_pos.SetImmortalWall(wall);
    edge_pos.FinalizeInitialPosition(ldprover::Color::kBlack);

    AssertGenerateLegalMovesMatchesReference(edge_pos, std::nullopt,
                                             "5x5_capture_suicide_wall");
    const auto all_m = edge_pos.GenerateLegalMoves(std::nullopt);
    const int c_aa = Position<5>::CoordFromRowCol(0, 0);
    const int c_da = Position<5>::CoordFromRowCol(0, 3);
    Check(std::find(all_m.begin(), all_m.end(), static_cast<int16_t>(c_aa)) !=
              all_m.end(),
          "5x5 capturing crucial token at aa is legal even with 1 eye point",
          "");
    // Now test White suicide on aa when B[ab,bb,ca] and W[da] wall:
    // After B[pass], White at aa is suicide (cannot capture B[ab,bb,ca]),
    // whereas B[da] cannot capture immortal wall W[ea] -> Wait, B[da] connects to B[db], legal.
    Position<5> sui_pos = edge_pos;
    sui_pos.SetupInitialStone(Position<5>::CoordFromRowCol(0, 1),
                              ldprover::Color::kEmpty);
    sui_pos.SetupInitialStone(Position<5>::CoordFromRowCol(0, 1),
                              ldprover::Color::kBlack);
    // Surround (0,0) with B[(0,1), (1,0)]: W playing at (0,0) is pure suicide.
    Position<5> pure_sui(ctx);
    pure_sui.SetupInitialStone(Position<5>::CoordFromRowCol(0, 1),
                               ldprover::Color::kBlack);
    pure_sui.SetupInitialStone(Position<5>::CoordFromRowCol(1, 0),
                               ldprover::Color::kBlack);
    pure_sui.FinalizeInitialPosition(ldprover::Color::kWhite);
    AssertGenerateLegalMovesMatchesReference(pure_sui, std::nullopt,
                                             "5x5_white_suicide_at_aa");
    const auto sui_m = pure_sui.GenerateLegalMoves(std::nullopt);
    Check(std::find(sui_m.begin(), sui_m.end(), static_cast<int16_t>(c_aa)) ==
              sui_m.end(),
          "5x5 suicide move W[aa] is excluded by GenerateLegalMoves", "");
    (void)c_da;

    // Crucial token mask & immortal wall check: Play W[ca] inside W[ba]? Wait:
    // White[ea] surrounded by B[(0,3),(1,4)] is immortal wall -> Black cannot
    // capture W[ea], and White cannot capture non-empty. Put B[(0,3)] wall
    // protection: surround W[ea] at (0,4) except (0,3)=da occupied -> even with
    // (0,3) empty: B at (0,3) has neighbors (0,2)=B, (1,3)=B, (0,4)=W(wall)
    // Test opposite: surround B[(0,4)] (immortal) by W[(0,3)=empty, (1,4)=W]
    // -> W[(0,3)] surrounded by W[(1,3),(0,2)]? Place W[(0,3)] surrounded by
    // B[(0,2),(1,3)] -> W[(0,3)] cannot capture B, and B[(0,4)] wouldn't be
    // captured if W had wall. Put B at (0,4) WITH wall, W surrounds at (1,4),
    // and only empty point is (0,3) surrounded by B[(0,2),(1,3)] -> wait: put
    // B[(1,4)] immortal wall, surrounded by W[(2,4),(1,3),(0,4)=empty] ->
    // W[(0,4)] fails suicide because immortal B[(1,4)] cannot be captured!
    // B[(1,4)] is immortal wall surrounded by W[(2,4),(1,3)] and empty (0,4);
    // B[(0,3)] has liberty (0,2), so W[(0,4)] cannot capture B[(1,4)] (wall)
    // nor B[(0,3)] -> W[ea] is suicide and excluded.
    Position<5> wall_pos(ctx);
    wall_pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 4),
                               ldprover::Color::kBlack);
    wall_pos.SetupInitialStone(Position<5>::CoordFromRowCol(0, 3),
                               ldprover::Color::kBlack);
    wall_pos.SetupInitialStone(Position<5>::CoordFromRowCol(2, 4),
                               ldprover::Color::kWhite);
    wall_pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 3),
                               ldprover::Color::kWhite);
    BitBoard<5> wall_b;
    wall_b.Set(Position<5>::CoordFromRowCol(1, 4), true);
    wall_pos.SetImmortalWall(wall_b);
    wall_pos.FinalizeInitialPosition(ldprover::Color::kWhite);
    AssertGenerateLegalMovesMatchesReference(wall_pos, std::nullopt,
                                             "5x5_immortal_wall_no_capture");
    const auto wm = wall_pos.GenerateLegalMoves(std::nullopt);
    const int c_ea = Position<5>::CoordFromRowCol(0, 4);
    Check(std::find(wm.begin(), wm.end(), static_cast<int16_t>(c_ea)) ==
              wm.end(),
          "5x5 W[ea] cannot capture immortal wall B[eb] -> suicide excluded", "");
  }

  // Edge Case B: Explicit Empty Region & Double PASS on 19x19 (p042 context)
  {
    const ParsedProblem<19> p001 = BuildP001();
    const std::optional<BitBoard<19>> empty_reg = BitBoard<19>{};
    AssertGenerateLegalMovesMatchesReference(p001.initial_position, empty_reg,
                                             "19x19_explicit_empty_region");
    const auto em = p001.initial_position.GenerateLegalMoves(empty_reg);
    Check(em.size() == 1U && em[0] == ldprover::kPassMove,
          "19x19 explicit empty region returns [kPassMove] only",
          "size=" + std::to_string(em.size()));

    Position<19> dp = p001.initial_position;
    const bool p1 = dp.PlayMove(ldprover::kPassMove);
    const bool p2 = dp.PlayMove(ldprover::kPassMove);
    AssertGenerateLegalMovesMatchesReference(dp, std::nullopt,
                                             "19x19_double_pass_unbounded");
    AssertGenerateLegalMovesMatchesReference(dp, p001.region_search_mask,
                                             "19x19_double_pass_region");
    Check(p1 && p2 && dp.GenerateLegalMoves(std::nullopt).empty() &&
              dp.GenerateLegalMoves(p001.region_search_mask).empty(),
          "19x19 double PASS yields empty legal move vector", "");
  }

  // Edge Case C: p003/p005 Ko & Capture States
  {
    const ParsedProblem<19> p003 = BuildP003();
    AssertGenerateLegalMovesMatchesReference(p003.initial_position,
                                             p003.region_search_mask,
                                             "19x19_p003_root");
    const ParsedProblem<19> p005 = BuildP005(true);
    Position<19> ko_state = p005.initial_position;
    // Play B[ca] (ko capture of W[ba])? Wait: in p005 B plays ca to test ko state
    const int16_t kCa =
        static_cast<int16_t>(Position<19>::CoordFromRowCol(0, 2));
    if (ko_state.PlayMove(kCa)) {
      AssertGenerateLegalMovesMatchesReference(ko_state,
                                               p005.region_search_mask,
                                               "19x19_p005_after_ko_capture");
    }
  }
}

template <int N>
void AssertZobristSynced(const Position<N>& pos, const std::string& label) {
  const uint64_t expected = pos.RecomputeZobristForTest();
  const bool snap_ok = !pos.HistorySnapshots().empty() &&
                       pos.HistorySnapshots().back().zobrist_hash == expected;
  Check(pos.ZobristHash() == expected && snap_ok, label,
        "hash=" + std::to_string(pos.ZobristHash()) +
            " recomputed=" + std::to_string(expected) +
            " snaps=" + std::to_string(pos.HistorySnapshots().size()));
}

void TestSection9IncrementalZobristParity() {
  std::cout << "\n=== 9. R24 Incremental Zobrist Step-by-Step Parity ===\n";

  // 9.1 Multi-chain simultaneous capture (including U-chain touched twice),
  // suicide rollback, immortal-wall suicide rollback, PASS, and full Undo on 5x5
  {
    ldprover::ProofContext ctx{};
    ctx.ko_rule = ldprover::KoRule::kSituationalSuperko;
    Position<5> pos(ctx);
    Check(pos.ZobristHash() == pos.RecomputeZobristForTest(),
          "5x5 empty Clear() hash matches ComputeZobrist", "");

    // Setup U-shaped W[(0,0),(0,1),(1,0)] + isolated W[(1,2)] whose sole
    // common liberty is (1,1); surrounders B[(0,2),(1,3),(2,0),(2,2)] and (2,1)?
    // Check liberties of (0,0),(0,1),(1,0):
    //   (0,0)->(0,1)=W,(1,0)=W
    //   (0,1)->(0,0)=W,(0,2)=B,(1,1)=empty
    //   (1,0)->(0,0)=W,(2,0)=B,(1,1)=empty
    // Check liberties of W[(1,2)]: (0,2)=B,(1,3)=B,(2,2)=B,(1,1)=empty!
    pos.SetupInitialStone(Position<5>::CoordFromRowCol(0, 0),
                          ldprover::Color::kWhite);
    pos.SetupInitialStone(Position<5>::CoordFromRowCol(0, 1),
                          ldprover::Color::kWhite);
    pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 0),
                          ldprover::Color::kWhite);
    pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 2),
                          ldprover::Color::kWhite);
    pos.SetupInitialStone(Position<5>::CoordFromRowCol(0, 2),
                          ldprover::Color::kBlack);
    pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 3),
                          ldprover::Color::kBlack);
    pos.SetupInitialStone(Position<5>::CoordFromRowCol(2, 0),
                          ldprover::Color::kBlack);
    pos.SetupInitialStone(Position<5>::CoordFromRowCol(2, 2),
                          ldprover::Color::kBlack);
    // Also isolate (4,4) with W[(4,3),(3,4)] so Black playing (4,4) is suicide
    pos.SetupInitialStone(Position<5>::CoordFromRowCol(4, 3),
                          ldprover::Color::kWhite);
    pos.SetupInitialStone(Position<5>::CoordFromRowCol(3, 4),
                          ldprover::Color::kWhite);
    pos.FinalizeInitialPosition(ldprover::Color::kBlack);
    AssertZobristSynced(pos, "5x5 initial setup");
    const uint64_t h_init = pos.ZobristHash();

    // Suicide attempt at (4,4) must fail and preserve hash/history identically
    const bool sui_ok =
        pos.PlayMove(static_cast<int16_t>(Position<5>::CoordFromRowCol(4, 4)));
    Check(!sui_ok, "5x5 suicide rejected", "");
    AssertZobristSynced(pos, "5x5 post-suicide-rollback");
    Check(pos.ZobristHash() == h_init, "5x5 hash unchanged after suicide", "");

    // Multi-chain multi-stone capture at (1,1) captures 4 W stones (3+1)
    const bool cap_ok =
        pos.PlayMove(static_cast<int16_t>(Position<5>::CoordFromRowCol(1, 1)));
    Check(cap_ok && pos.StoneAt(Position<5>::CoordFromRowCol(0, 0)) ==
                        ldprover::Color::kEmpty &&
              pos.StoneAt(Position<5>::CoordFromRowCol(1, 2)) ==
                  ldprover::Color::kEmpty,
          "5x5 simultaneous U-chain + singleton capture succeeds", "");
    AssertZobristSynced(pos, "5x5 after multi-chain capture");

    // Normal alternating moves & PASS & double-PASS + Undo unwind
    Check(pos.PlayMove(static_cast<int16_t>(Position<5>::CoordFromRowCol(0, 0))),
          "5x5 normal W move", "");
    AssertZobristSynced(pos, "5x5 after normal W move");
    Check(pos.PlayMove(ldprover::kPassMove), "5x5 B pass", "");
    AssertZobristSynced(pos, "5x5 after B pass");
    Check(pos.PlayMove(ldprover::kPassMove), "5x5 W double-pass", "");
    AssertZobristSynced(pos, "5x5 after W double-pass");
    Check(!pos.PlayMove(ldprover::kPassMove), "5x5 triple-pass rejected", "");
    AssertZobristSynced(pos, "5x5 after rejected move post-double-pass");

    while (!pos.PlayedMoveTrace().empty()) {
      pos.UndoMove();
      AssertZobristSynced(pos, "5x5 during UndoMove unwind");
    }
    Check(pos.ZobristHash() == h_init, "5x5 UndoMove restores exact init hash",
          "");

    // Immortal-wall suicide rollback
    Position<5> wall_pos(ctx);
    wall_pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 4),
                               ldprover::Color::kBlack);
    wall_pos.SetupInitialStone(Position<5>::CoordFromRowCol(0, 3),
                               ldprover::Color::kBlack);
    wall_pos.SetupInitialStone(Position<5>::CoordFromRowCol(2, 4),
                               ldprover::Color::kWhite);
    wall_pos.SetupInitialStone(Position<5>::CoordFromRowCol(1, 3),
                               ldprover::Color::kWhite);
    BitBoard<5> wall_b;
    wall_b.Set(Position<5>::CoordFromRowCol(1, 4), true);
    wall_pos.SetImmortalWall(wall_b);
    wall_pos.FinalizeInitialPosition(ldprover::Color::kWhite);
    AssertZobristSynced(wall_pos, "5x5 immortal wall init");
    const bool wall_sui = wall_pos.PlayMove(
        static_cast<int16_t>(Position<5>::CoordFromRowCol(0, 4)));
    Check(!wall_sui, "5x5 immortal-wall capture suicide rejected", "");
    AssertZobristSynced(wall_pos, "5x5 post-immortal-wall-suicide rollback");
  }

  // 9.2 Simple ko creation, simple ko rejection, ko clearing via non-ko move
  // and PASS, SSK + PSK superko rollbacks, and GenerateLegalMoves on 7x7 & 19x19
  auto run_ko_and_superko_suite = []<int N>(const std::string& tag) {
    ldprover::ProofContext ssk_ctx{};
    ssk_ctx.ko_rule = ldprover::KoRule::kSituationalSuperko;
    Position<N> pos(ssk_ctx);
    // Standard corner/edge simple ko around (0,1) captured vs (0,2):
    // B: (0,0), (1,1), (0,3)? Wait: simpler centered ko on >=5x5:
    //   B at (1,2), (2,1), (2,3), (3,2) captures W[(2,2)] when W surrounds (1,2)?
    //   Classic 4-stone ko at row 2:
    //   B[(1,1),(2,0),(3,1)], W[(1,2),(2,3),(3,2),(2,1)], empty=(2,2)
    pos.SetupInitialStone(Position<N>::CoordFromRowCol(1, 1),
                          ldprover::Color::kBlack);
    pos.SetupInitialStone(Position<N>::CoordFromRowCol(2, 0),
                          ldprover::Color::kBlack);
    pos.SetupInitialStone(Position<N>::CoordFromRowCol(3, 1),
                          ldprover::Color::kBlack);
    pos.SetupInitialStone(Position<N>::CoordFromRowCol(1, 2),
                          ldprover::Color::kWhite);
    pos.SetupInitialStone(Position<N>::CoordFromRowCol(2, 3),
                          ldprover::Color::kWhite);
    pos.SetupInitialStone(Position<N>::CoordFromRowCol(3, 2),
                          ldprover::Color::kWhite);
    pos.SetupInitialStone(Position<N>::CoordFromRowCol(2, 1),
                          ldprover::Color::kWhite);
    // Keep extra stones so non-ko moves remain valid without altering ko
    pos.FinalizeInitialPosition(ldprover::Color::kBlack);
    AssertZobristSynced(pos, tag + " ko init");

    const int16_t kKoCaptureB =
        static_cast<int16_t>(Position<N>::CoordFromRowCol(2, 2));
    const int16_t kKoRecapW =
        static_cast<int16_t>(Position<N>::CoordFromRowCol(2, 1));
    bool is_ko = false;
    Check(pos.PlayMove(kKoCaptureB, &is_ko) && is_ko &&
              pos.KoPoint() == kKoRecapW,
          tag + " simple ko created at (2,1)", "");
    AssertZobristSynced(pos, tag + " after simple ko capture");

    // Immediate ko recapture rejected
    Check(!pos.PlayMove(kKoRecapW), tag + " immediate ko recapture rejected",
          "");
    AssertZobristSynced(pos, tag + " after rejected ko recapture");

    // GenerateLegalMoves keeps parent hash/history untouched
    const uint64_t pre_gen_hash = pos.ZobristHash();
    const size_t pre_gen_snaps = pos.HistorySnapshots().size();
    const auto gl = pos.GenerateLegalMoves(std::nullopt);
    Check(!gl.empty() && pos.ZobristHash() == pre_gen_hash &&
              pos.HistorySnapshots().size() == pre_gen_snaps,
          tag + " GenerateLegalMoves leaves hash & history invariant", "");
    AssertZobristSynced(pos, tag + " after GenerateLegalMoves");

    // Ko cleared by PASS
    {
      Position<N> pass_clear = pos;
      Check(pass_clear.PlayMove(ldprover::kPassMove) &&
                pass_clear.KoPoint() == ldprover::kNullMove,
            tag + " PASS clears ko_point_", "");
      AssertZobristSynced(pass_clear, tag + " after PASS clears ko");
      pass_clear.UndoMove();
      AssertZobristSynced(pass_clear, tag + " after Undo PASS restores ko");
    }

    // Ko cleared by non-ko move, then SSK superko test via recapture
    const int16_t w_else =
        static_cast<int16_t>(Position<N>::CoordFromRowCol(N - 1, N - 1));
    const int16_t b_else =
        static_cast<int16_t>(Position<N>::CoordFromRowCol(N - 1, N - 2));
    Check(pos.PlayMove(w_else) && pos.KoPoint() == ldprover::kNullMove,
          tag + " non-ko move clears ko_point_", "");
    AssertZobristSynced(pos, tag + " after non-ko W move clears ko");
    Check(pos.PlayMove(b_else), tag + " non-ko B move", "");
    AssertZobristSynced(pos, tag + " after non-ko B move");
    Check(pos.PlayMove(kKoRecapW, &is_ko) && is_ko &&
              pos.KoPoint() == kKoCaptureB,
          tag + " W recaptures ko after ko threat", "");
    AssertZobristSynced(pos, tag + " after W ko recapture");

    // Exact SSK & PSK superko violation rollback (using R22 18-cell superko
    // gadget: AB[bb][cb][da] AW[ab][ba][ca], B[aa], W[ba], B[pass] -> W[ca])
    for (auto rule : {ldprover::KoRule::kSituationalSuperko,
                      ldprover::KoRule::kPositionalSuperko}) {
      ldprover::ProofContext rctx{};
      rctx.ko_rule = rule;
      Position<N> rpos(rctx);
      const int16_t c_aa =
          static_cast<int16_t>(Position<N>::CoordFromRowCol(0, 0));
      const int16_t c_ba =
          static_cast<int16_t>(Position<N>::CoordFromRowCol(0, 1));
      const int16_t c_ca =
          static_cast<int16_t>(Position<N>::CoordFromRowCol(0, 2));
      const int16_t c_ab =
          static_cast<int16_t>(Position<N>::CoordFromRowCol(1, 0));
      const int16_t c_bb =
          static_cast<int16_t>(Position<N>::CoordFromRowCol(1, 1));
      const int16_t c_cb =
          static_cast<int16_t>(Position<N>::CoordFromRowCol(1, 2));
      const int16_t c_da =
          static_cast<int16_t>(Position<N>::CoordFromRowCol(0, 3));
      rpos.SetupInitialStone(c_bb, ldprover::Color::kBlack);
      rpos.SetupInitialStone(c_cb, ldprover::Color::kBlack);
      rpos.SetupInitialStone(c_da, ldprover::Color::kBlack);
      rpos.SetupInitialStone(c_ab, ldprover::Color::kWhite);
      rpos.SetupInitialStone(c_ba, ldprover::Color::kWhite);
      rpos.SetupInitialStone(c_ca, ldprover::Color::kWhite);
      rpos.FinalizeInitialPosition(ldprover::Color::kBlack);
      AssertZobristSynced(rpos, tag + " superko init");

      Check(rpos.PlayMove(c_aa), tag + " superko setup B[aa]", "");
      AssertZobristSynced(rpos, tag + " after superko setup B[aa]");
      Check(rpos.PlayMove(c_ba), tag + " superko setup W[ba]", "");
      AssertZobristSynced(rpos, tag + " after superko setup W[ba]");
      Check(rpos.PlayMove(ldprover::kPassMove), tag + " superko setup B[pass]",
            "");
      AssertZobristSynced(rpos, tag + " after superko setup B[pass]");

      const uint64_t pre_superko_hash = rpos.ZobristHash();
      const size_t pre_superko_snaps = rpos.HistorySnapshots().size();
      const bool rejected_ca = !rpos.PlayMove(c_ca);
      Check(rejected_ca && rpos.ZobristHash() == pre_superko_hash &&
                rpos.HistorySnapshots().size() == pre_superko_snaps,
            tag + " superko rollback preserves exact Zobrist & history",
            "rule=" + std::to_string(static_cast<int>(rule)));
      AssertZobristSynced(rpos, tag + " post-superko-rollback");
    }
  };
  run_ko_and_superko_suite.template operator()<5>("5x5");
  run_ko_and_superko_suite.template operator()<7>("7x7");
  run_ko_and_superko_suite.template operator()<19>("19x19");
}

template <int N>
void VerifyOrthoTableForSize(const std::string& tag) {
  Position<N> pos;
  int corners = 0;
  int edges = 0;
  int interiors = 0;
  bool all_exact = true;
  for (int coord = 0; coord < N * N; ++coord) {
    const auto ref = pos.OrthogonalNeighbors(coord);
    const auto tbl = Position<N>::PrecomputedOrthogonalNeighborsForTest(coord);
    if (static_cast<size_t>(tbl.count) != ref.size()) {
      all_exact = false;
      break;
    }
    for (size_t i = 0; i < ref.size(); ++i) {
      if (tbl.coords[i] != ref[i]) {
        all_exact = false;
        break;
      }
    }
    if (!all_exact) break;
    if (tbl.count == 2) ++corners;
    else if (tbl.count == 3) ++edges;
    else if (tbl.count == 4) ++interiors;
    else all_exact = false;
  }
  const auto neg = Position<N>::PrecomputedOrthogonalNeighborsForTest(-1);
  const auto oob =
      Position<N>::PrecomputedOrthogonalNeighborsForTest(N * N);
  Check(all_exact && corners == 4 && edges == 4 * (N - 2) &&
            interiors == (N - 2) * (N - 2) && neg.count == 0 && oob.count == 0,
        "R25 " + tag + " precomputed ortho table matches OrthogonalNeighbors in exact sequence & counts",
        "exact=" + std::to_string(all_exact) + " c/e/i=" +
            std::to_string(corners) + "/" + std::to_string(edges) + "/" +
            std::to_string(interiors));
}

void TestSection10OrthoNeighborTableParity() {
  std::cout << "\n=== 10. R25 Precomputed Orthogonal Neighbor Table Exhaustive Parity ===\n";
  VerifyOrthoTableForSize<5>("5x5");
  VerifyOrthoTableForSize<7>("7x7");
  VerifyOrthoTableForSize<19>("19x19");
}

void TestSection11ConvergenceObserverParity() {
  std::cout << "\n=== 11. R26 Opt-In Read-Only Convergence Observer Parity ===\n";
  const ParsedProblem<19> p003 = BuildP003();
  SolverConfig cfg_off = DefaultConfig(3500U);
  SolverConfig cfg_on = DefaultConfig(3500U);
  cfg_on.enable_convergence_trace = true;
  cfg_on.observed_paths = {"", "pass", "nonexistent"};

  DfpnSolver<19> s_off(cfg_off);
  DfpnSolver<19> s_on(cfg_on);
  const auto r_off = s_off.Solve(p003.initial_position, p003.proof_context,
                                 p003.region_search_mask, "p003");
  const auto r_on = s_on.Solve(p003.initial_position, p003.proof_context,
                               p003.region_search_mask, "p003");

  ProofArtifactManager<19> mgr;
  std::string cs_off, cs_on;
  const std::string j_off = mgr.SerializeLProofJson(
      p003.initial_position, p003.proof_context, r_off, &cs_off);
  const std::string j_on = mgr.SerializeLProofJson(
      p003.initial_position, p003.proof_context, r_on, &cs_on);
  const auto& tr = s_on.ConvergenceTrace();
  bool root_partition_ok = false;
  if (tr.watched_paths.size() == 3U && tr.watched_paths[0].frontier_exists) {
    const auto& w0 = tr.watched_paths[0];
    const uint32_t sum =
        w0.closed_proven_win_direct + w0.closed_proven_win_outside_rz +
        w0.closed_proven_loss_direct + w0.closed_proven_loss_outside_rz +
        w0.ko_barrier_count + w0.deferred_outside_rz_count +
        w0.expanded_unknown_count + w0.unexpanded_unknown_count;
    root_partition_ok = (sum == w0.total_legal_moves && w0.total_legal_moves > 0);
  }
  Check(j_off == j_on && cs_off == cs_on && !s_off.ConvergenceTrace().enabled &&
            tr.enabled && tr.first_terminal_leaf_node > 0 &&
            tr.first_non_terminal_subproof_node >= tr.first_terminal_leaf_node &&
            tr.first_non_terminal_subproof_dag_id != ldprover::kInvalidDagNodeId &&
            tr.first_non_terminal_subproof_dag_id > 0U &&
            tr.first_non_terminal_subproof_path != tr.first_terminal_leaf_path &&
            tr.path_basis == "solve_root_relative" &&
            tr.initial_trace_path.empty() && root_partition_ok &&
            tr.watched_paths.size() == 3U &&
            tr.watched_paths[2].first_enter_node == 0,
        "R26 convergence observer leaves p003 LProof bytes invariant and partitions legal moves cleanly",
        "leaf=" + std::to_string(tr.first_terminal_leaf_node) +
            " nonTerm=" + std::to_string(tr.first_non_terminal_subproof_node) +
            " nonTermDag=" + std::to_string(tr.first_non_terminal_subproof_dag_id) +
            " partition=" + std::to_string(root_partition_ok));
}

void TestSection12R27ObserverAndNearPnContinuation() {
  std::cout << "\n=== 12. R27 Observer Path-Basis, Subproof Binding & Near-PN Continuation ===\n";
  ProblemContractParser<19> parser;
  const std::string& region_p060 = CommonChaoRegion19();
  const std::string p060_json =
      std::string(
          R"json({"masked_sgf_str":"(;FF[4]CA[UTF-8]SZ[19]KM[30]AB[pr][qr][rq][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[or][oq][pq][qq][ap][bp][cp][dp][ep][fp][gp][hp][ip][qp][io][in][qn][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[pr][rq]MA[as][bs][cs][ds][es][fs][gs][hs][is][js][ks][ls][ms][ns][os][ps][qs][rs][ss][ar][br][cr][dr][er][fr][gr][hr][ir][jr][kr][lr][mr][nr][or][pr][qr][rr][sr][aq][bq][cq][dq][eq][fq][gq][hq][iq][jq][kq][lq][mq][nq][oq][pq][qq][rq][sq][jp][kp][lp][mp][np][op][pp][qp][rp][sp][jo][ko][lo][mo][no][oo][po][qo][ro][so][jn][kn][ln][mn][nn][on][pn][qn][rn][sn][jm][km][lm][mm][nm][om][pm][qm][rm][sm][jl][kl][ll][ml][nl][ol][pl][ql][rl][sl][jk][kk][lk][mk][nk][ok][pk][qk][rk][sk][kj][lj][mj][nj][oj][pj][qj][rj][sj][qi][ri][si][qh][rh][sh][qg][rg][sg][qf][rf][sf][qe][re][se][qd][rd][sd][qc][rc][sc][qb][rb][sb][qa][ra][sa])","winning_color":"b","turn_color":"b","black_crucial_stone":"pr,rq","white_crucial_stone":"","black_search_goal":"TOLIVE","white_search_goal":"TOKILL","black_ko_rule":"disallow_ko","white_ko_rule":"allow_ko","region":")json") +
      region_p060 + "\"}";
  const ParsedProblem<19> p060 = parser.ParseTsumegoJsonObject(
      "chao_vol1_p060", p060_json, TurnConflictPolicy::kRejectStrict);
  Check(p060.valid, "Inline p060 parses cleanly for R27 checks");

  // 1. Subposition start path alignment (R26 §3 P2 #1).
  {
    Position<19> sub_rs = p060.initial_position;
    const int16_t kMoveRs =
        static_cast<int16_t>(Position<19>::CoordFromRowCol(18, 17));
    Check(sub_rs.PlayMove(kMoveRs), "Playing B[rs] on p060 succeeds");
    SolverConfig cfg = DefaultConfig(256U);
    cfg.enable_convergence_trace = true;
    cfg.observed_paths = {"", "rs", "rs/pass", "pass"};
    DfpnSolver<19> solver(cfg);
    (void)solver.Solve(sub_rs, p060.proof_context, p060.region_search_mask,
                       "chao_vol1_p060_rs");
    const auto& tr = solver.ConvergenceTrace();
    const bool paths_ok =
        tr.path_basis == "solve_root_relative" &&
        tr.initial_trace_path == "rs" &&
        tr.watched_paths.size() == 4U &&
        tr.watched_paths[0].first_enter_node == 1U &&
        tr.watched_paths[0].visit_count >= 1U &&
        tr.watched_paths[0].frontier_exists &&
        tr.watched_paths[0].total_legal_moves == 144U &&
        tr.watched_paths[1].first_enter_node == 0U &&
        tr.watched_paths[1].visit_count == 0U &&
        !tr.watched_paths[1].frontier_exists &&
        tr.watched_paths[2].first_enter_node == 0U &&
        tr.watched_paths[2].visit_count == 0U &&
        !tr.watched_paths[2].frontier_exists &&
        tr.watched_paths[3].first_enter_node > 1U &&
        tr.watched_paths[3].visit_count >= 1U &&
        tr.watched_paths[3].frontier_exists &&
        tr.watched_paths[3].total_legal_moves == 144U;
    Check(paths_ok,
          "Subposition Solve uses solve_root_relative paths for both counters and frontier snapshots");
  }

  // 2. Non-terminal subproof separation + read-only edge-binding & precheck verifiers.
  ProofArtifactManager<19> mgr;
  {
    SolverConfig cfg_off = DefaultConfig(500U);
    SolverConfig cfg_on = DefaultConfig(500U);
    cfg_on.enable_convergence_trace = true;
    cfg_on.observed_paths = {""};
    DfpnSolver<19> s_off(cfg_off);
    DfpnSolver<19> s_on(cfg_on);
    const auto r_off = s_off.Solve(p060.initial_position, p060.proof_context,
                                   p060.region_search_mask, "p060_500");
    const auto r_on = s_on.Solve(p060.initial_position, p060.proof_context,
                                 p060.region_search_mask, "p060_500");
    const std::string j_off = mgr.SerializeLProofJson(
        p060.initial_position, p060.proof_context, r_off);
    const std::string j_on = mgr.SerializeLProofJson(
        p060.initial_position, p060.proof_context, r_on);
    const auto& tr = s_on.ConvergenceTrace();
    Check(j_off == j_on && tr.first_terminal_leaf_node == 337U &&
              tr.first_non_terminal_subproof_node >= 337U &&
              tr.first_non_terminal_subproof_dag_id != ldprover::kInvalidDagNodeId &&
              tr.first_non_terminal_subproof_dag_id > 0U &&
              tr.first_non_terminal_subproof_path != tr.first_terminal_leaf_path,
          "p060@500 separates first terminal leaf (dag=0) from non-terminal subproofs (dag>0, distinct path)",
          "leaf=" + std::to_string(tr.first_terminal_leaf_node) +
              " nonTerm=" + std::to_string(tr.first_non_terminal_subproof_node) +
              " nonTermDag=" + std::to_string(tr.first_non_terminal_subproof_dag_id) +
              " nonTermPath=" + tr.first_non_terminal_subproof_path);

    // UNKNOWN root p060@500 non-terminal subproof ("qs/pass/sq/pass/rr/os"):
    // default mode allows unbound semantic replay, while kRequireBoundRootEdge rejects LP-U01.
    const std::vector<int16_t> p60_rel = {
        static_cast<int16_t>(Position<19>::CoordFromRowCol(18, 16)),
        ldprover::kPassMove,
        static_cast<int16_t>(Position<19>::CoordFromRowCol(16, 18)),
        ldprover::kPassMove,
        static_cast<int16_t>(Position<19>::CoordFromRowCol(17, 17)),
        static_cast<int16_t>(Position<19>::CoordFromRowCol(18, 14)),
    };
    const auto v60_default = mgr.VerifySubproofAtPath(
        p060.initial_position, p060.proof_context, r_on, p60_rel,
        tr.first_non_terminal_subproof_dag_id);
    const auto v60_strict = mgr.VerifySubproofAtPath(
        p060.initial_position, p060.proof_context, r_on, p60_rel,
        tr.first_non_terminal_subproof_dag_id,
        ldprover::SubproofBindingPolicy::kRequireBoundRootEdge);
    Check(v60_default.passed && v60_default.error_code == "PASS" &&
              !v60_default.edge_bound_to_root_dag &&
              v60_default.edge_binding_status == "unbound_unknown_root" &&
              v60_default.recorded_edge_dag_node_id == -1 &&
              v60_default.semantic_replay_passed && !v60_strict.passed &&
              v60_strict.error_code == "LP-U01" &&
              v60_strict.edge_binding_status == "unbound_unknown_root" &&
              !v60_strict.semantic_replay_passed,
          "UNKNOWN-root subproof distinguishes unbound_unknown_root PASS from kRequireBoundRootEdge LP-U01");

    // Proven root p004: edge ownership vs semantic replay & structural prechecks (R27 P1 #1/#2).
    const ParsedProblem<19> p004 = BuildP004();
    const auto rp4 =
        DfpnSolver<19>(DefaultConfig(3500U))
            .Solve(p004.initial_position, p004.proof_context,
                   p004.region_search_mask, "p004");
    const std::string pre_p4 =
        mgr.SerializeLProofJson(p004.initial_position, p004.proof_context, rp4);
    uint32_t pass_child_id = ldprover::kInvalidDagNodeId;
    uint32_t move_21_id = ldprover::kInvalidDagNodeId;
    const auto& root_dn = rp4.proof_dag_nodes[rp4.root_dag_node_id];
    for (size_t k = 0; k < root_dn.child_moves.size(); ++k) {
      if (root_dn.child_moves[k] == ldprover::kPassMove) {
        pass_child_id = root_dn.child_node_ids[k];
      } else if (root_dn.child_moves[k] == 21) {
        move_21_id = root_dn.child_node_ids[k];
      }
    }
    Check(pass_child_id != ldprover::kInvalidDagNodeId &&
              move_21_id != ldprover::kInvalidDagNodeId &&
              pass_child_id != move_21_id,
          "p004 proven root exposes distinct PASS and move-21 child DAG edges",
          "pass_id=" + std::to_string(pass_child_id) +
              " move21_id=" + std::to_string(move_21_id));

    const auto v_root = mgr.VerifySubproofAtPath(
        p004.initial_position, p004.proof_context, rp4, {},
        rp4.root_dag_node_id);
    const auto v_pass_edge = mgr.VerifySubproofAtPath(
        p004.initial_position, p004.proof_context, rp4, {ldprover::kPassMove},
        pass_child_id);
    const auto v_21_edge = mgr.VerifySubproofAtPath(
        p004.initial_position, p004.proof_context, rp4, {21}, move_21_id);
    Check(v_root.passed && v_root.edge_bound_to_root_dag &&
              v_root.edge_binding_status == "bound_to_root_dag" &&
              v_root.recorded_edge_dag_node_id ==
                  static_cast<int32_t>(rp4.root_dag_node_id) &&
              v_root.semantic_replay_passed &&
              v_pass_edge.passed && v_pass_edge.edge_bound_to_root_dag &&
              v_pass_edge.edge_binding_status == "bound_to_root_dag" &&
              v_pass_edge.recorded_edge_dag_node_id ==
                  static_cast<int32_t>(pass_child_id) &&
              v_21_edge.passed && v_21_edge.edge_bound_to_root_dag &&
              v_21_edge.edge_binding_status == "bound_to_root_dag" &&
              v_21_edge.recorded_edge_dag_node_id ==
                  static_cast<int32_t>(move_21_id),
          "p004 original root edges verify PASS with bound_to_root_dag receipts");

    // Asking VerifySubproofAtPath on path {21} with PASS's DAG (`pass_child_id`):
    // default strict ownership rejects LP-R02 (`edge_mismatch`, recorded=move_21_id),
    // while explicit `kSemanticReplayOnly` and `VerifySiblingQueryReplay` verify semantic PASS.
    const auto v_mismatch = mgr.VerifySubproofAtPath(
        p004.initial_position, p004.proof_context, rp4, {21}, pass_child_id);
    const auto v_sem_21 = mgr.VerifySubproofAtPath(
        p004.initial_position, p004.proof_context, rp4, {21}, pass_child_id,
        ldprover::SubproofBindingPolicy::kSemanticReplayOnly);
    const auto v_sib_21 = mgr.VerifySiblingQueryReplay(
        p004.initial_position, p004.proof_context, rp4, {}, ldprover::kPassMove,
        pass_child_id, 21);
    Check(!v_mismatch.passed && v_mismatch.error_code == "LP-R02" &&
              !v_mismatch.edge_bound_to_root_dag &&
              v_mismatch.edge_binding_status == "edge_mismatch" &&
              v_mismatch.recorded_edge_dag_node_id ==
                  static_cast<int32_t>(move_21_id) &&
              !v_mismatch.semantic_replay_passed &&
              v_sem_21.passed && v_sem_21.error_code == "PASS" &&
              !v_sem_21.edge_bound_to_root_dag &&
              v_sem_21.edge_binding_status == "unbound_replay_only" &&
              v_sem_21.recorded_edge_dag_node_id ==
                  static_cast<int32_t>(move_21_id) &&
              v_sem_21.semantic_replay_passed &&
              v_sib_21.passed && v_sib_21.error_code == "PASS" &&
              v_sib_21.source_edge_bound_to_root_dag &&
              v_sib_21.source_edge_binding_status == "bound_to_root_dag" &&
              v_sib_21.source_recorded_edge_dag_node_id ==
                  static_cast<int32_t>(pass_child_id) &&
              !v_sib_21.edge_bound_to_root_dag &&
              v_sib_21.edge_binding_status == "unbound_replay_only" &&
              v_sib_21.recorded_edge_dag_node_id ==
                  static_cast<int32_t>(move_21_id) &&
              v_sib_21.semantic_replay_passed,
          "p004 move 21 + PASS DAG separates LP-R02 edge_mismatch from PASS unbound_replay_only and preserves source binding");

    // Negative controls on p004: move 2 (ca) fails both semantic replay and edge ownership;
    // spoofed sibling source `{21} -> pass_child_id` fails source edge binding;
    // non-recorded sub-path `{21, 0}` reports `edge_not_found`.
    const auto v_neg2_strict = mgr.VerifySubproofAtPath(
        p004.initial_position, p004.proof_context, rp4, {2}, pass_child_id);
    const auto v_neg2_sem = mgr.VerifySubproofAtPath(
        p004.initial_position, p004.proof_context, rp4, {2}, pass_child_id,
        ldprover::SubproofBindingPolicy::kSemanticReplayOnly);
    const auto v_neg2_sib = mgr.VerifySiblingQueryReplay(
        p004.initial_position, p004.proof_context, rp4, {}, ldprover::kPassMove,
        pass_child_id, 2);
    const auto v_spoof_src = mgr.VerifySiblingQueryReplay(
        p004.initial_position, p004.proof_context, rp4, {}, 21,
        pass_child_id, ldprover::kPassMove);
    // Legal unrecorded path `{21, 0}` (`W[cb]`, then non-witness `B[aa]`) -> edge_not_found.
    const auto v_unrecorded = mgr.VerifySubproofAtPath(
        p004.initial_position, p004.proof_context, rp4, {21, 0},
        pass_child_id);
    const std::string post_p4 =
        mgr.SerializeLProofJson(p004.initial_position, p004.proof_context, rp4);
    Check(!v_neg2_strict.passed && v_neg2_strict.error_code == "LP-R02" &&
              !v_neg2_sem.passed && v_neg2_sem.error_code == "LP-R02" &&
              !v_neg2_sem.semantic_replay_passed &&
              v_neg2_sem.edge_binding_status == "unbound_replay_only" &&
              !v_neg2_sib.passed && v_neg2_sib.error_code == "LP-R02" &&
              !v_neg2_sib.semantic_replay_passed &&
              !v_spoof_src.passed && v_spoof_src.error_code == "LP-R02" &&
              !v_spoof_src.source_edge_bound_to_root_dag &&
              v_spoof_src.source_edge_binding_status == "edge_mismatch" &&
              v_spoof_src.source_recorded_edge_dag_node_id ==
                  static_cast<int32_t>(move_21_id) &&
              v_spoof_src.edge_binding_status == "edge_mismatch" &&
              !v_unrecorded.passed && v_unrecorded.error_code == "LP-R02" &&
              v_unrecorded.edge_binding_status == "edge_not_found" &&
              v_unrecorded.recorded_edge_dag_node_id == -1 && pre_p4 == post_p4,
          "p004 negative controls & spoofed sibling source reject LP-R02 and keep LProof bytes invariant");

    // R28 P1: UNKNOWN-root sibling replay on p004@6 (`cb` closed at DAG 1, `ed` unvisited).
    {
      SolverConfig cfg_p04_6 = DefaultConfig(6U);
      cfg_p04_6.enable_convergence_trace = true;
      cfg_p04_6.observed_paths = {"", "ed", "pass", "cb", "ca"};
      DfpnSolver<19> s_p04_6(cfg_p04_6);
      const auto rp4_6 = s_p04_6.Solve(
          p004.initial_position, p004.proof_context, p004.region_search_mask,
          "p004_6");
      const auto& tr6 = s_p04_6.ConvergenceTrace();
      bool cb_closed_dag1 = false;
      bool ed_closed = false;
      for (const auto& cc : tr6.watched_paths[0].closed_children) {
        if (cc.move == 21 && cc.dag_node_id == 1U) cb_closed_dag1 = true;
        if (cc.move == 61) ed_closed = true;
      }
      const std::string pre_p4_6 = mgr.SerializeLProofJson(
          p004.initial_position, p004.proof_context, rp4_6);

      // Claiming `ed` (61) owns DAG 1 when replaying onto `cb` (21):
      // default strict mode rejects LP-U01; explicit semantic modes pass while
      // leaving source provenance unbound.
      const auto sib6_strict = mgr.VerifySiblingQueryReplay(
          p004.initial_position, p004.proof_context, rp4_6, {}, 61, 1U, 21);
      const auto sib6_sem = mgr.VerifySiblingQueryReplay(
          p004.initial_position, p004.proof_context, rp4_6, {}, 61, 1U, 21,
          ldprover::SubproofBindingPolicy::kSemanticReplayOnly);
      const auto sib6_root_when_proven = mgr.VerifySiblingQueryReplay(
          p004.initial_position, p004.proof_context, rp4_6, {}, 61, 1U, 21,
          ldprover::SubproofBindingPolicy::kStrictWhenRootProven);
      const auto sib6_neg_ca = mgr.VerifySiblingQueryReplay(
          p004.initial_position, p004.proof_context, rp4_6, {}, 2, 1U, 21,
          ldprover::SubproofBindingPolicy::kSemanticReplayOnly);
      const std::string post_p4_6 = mgr.SerializeLProofJson(
          p004.initial_position, p004.proof_context, rp4_6);

      Check(rp4_6.root_status == ProofOutcome::kUnknown &&
                rp4_6.num_nodes == 6U && rp4_6.proof_dag_nodes.size() == 4U &&
                cb_closed_dag1 && !ed_closed &&
                tr6.watched_paths[1].visit_count == 0ULL &&
                !sib6_strict.passed && sib6_strict.error_code == "LP-U01" &&
                !sib6_strict.source_edge_bound_to_root_dag &&
                sib6_strict.source_edge_binding_status ==
                    "unbound_unknown_root" &&
                sib6_strict.source_recorded_edge_dag_node_id == -1 &&
                !sib6_strict.semantic_replay_passed &&
                sib6_sem.passed && sib6_sem.error_code == "PASS" &&
                !sib6_sem.source_edge_bound_to_root_dag &&
                sib6_sem.source_edge_binding_status == "unbound_replay_only" &&
                sib6_sem.source_recorded_edge_dag_node_id == -1 &&
                !sib6_sem.edge_bound_to_root_dag &&
                sib6_sem.edge_binding_status == "unbound_replay_only" &&
                sib6_sem.recorded_edge_dag_node_id == -1 &&
                sib6_sem.semantic_replay_passed &&
                sib6_root_when_proven.passed &&
                !sib6_root_when_proven.source_edge_bound_to_root_dag &&
                sib6_root_when_proven.source_edge_binding_status ==
                    "unbound_unknown_root" &&
                sib6_root_when_proven.edge_binding_status ==
                    "unbound_replay_only" &&
                sib6_root_when_proven.semantic_replay_passed &&
                !sib6_neg_ca.passed && sib6_neg_ca.error_code == "LP-R02" &&
                !sib6_neg_ca.source_edge_bound_to_root_dag &&
                !sib6_neg_ca.semantic_replay_passed && pre_p4_6 == post_p4_6,
            "R28 p004@6 separates strict LP-U01 from explicit semantic PASS (unbound source provenance)");
    }

    // R27 P1 #2: Structural pre-checks run BEFORE any vector indexing across both entries.
    {
      auto corrupt_target = rp4;
      corrupt_target.proof_dag_nodes[pass_child_id].child_moves.push_back(0);
      const auto ct_def = mgr.VerifySubproofAtPath(
          p004.initial_position, p004.proof_context, corrupt_target,
          {ldprover::kPassMove}, pass_child_id);
      const auto ct_sem = mgr.VerifySubproofAtPath(
          p004.initial_position, p004.proof_context, corrupt_target, {21},
          pass_child_id, ldprover::SubproofBindingPolicy::kSemanticReplayOnly);
      const auto ct_sib = mgr.VerifySiblingQueryReplay(
          p004.initial_position, p004.proof_context, corrupt_target, {},
          ldprover::kPassMove, pass_child_id, 21);

      auto corrupt_root = rp4;
      corrupt_root.proof_dag_nodes[rp4.root_dag_node_id].child_moves.push_back(
          ldprover::kPassMove);
      const auto cr_sub = mgr.VerifySubproofAtPath(
          p004.initial_position, p004.proof_context, corrupt_root,
          {ldprover::kPassMove}, pass_child_id);
      const auto cr_sib = mgr.VerifySiblingQueryReplay(
          p004.initial_position, p004.proof_context, corrupt_root, {},
          ldprover::kPassMove, pass_child_id, 21);

      auto corrupt_cycle = rp4;
      if (!corrupt_cycle.proof_dag_nodes[pass_child_id].child_node_ids.empty()) {
        corrupt_cycle.proof_dag_nodes[pass_child_id].child_node_ids[0] =
            pass_child_id;
      }
      const auto cc_sub = mgr.VerifySubproofAtPath(
          p004.initial_position, p004.proof_context, corrupt_cycle,
          {ldprover::kPassMove}, pass_child_id);
      const auto cc_sib = mgr.VerifySiblingQueryReplay(
          p004.initial_position, p004.proof_context, corrupt_cycle, {},
          ldprover::kPassMove, pass_child_id, 21);

      auto corrupt_redir = rp4;
      corrupt_redir.proof_dag_nodes[pass_child_id].is_pruned_outside_rz = true;
      corrupt_redir.proof_dag_nodes[pass_child_id].source_proof_node_id =
          pass_child_id;
      const auto cp_sub = mgr.VerifySubproofAtPath(
          p004.initial_position, p004.proof_context, corrupt_redir,
          {ldprover::kPassMove}, pass_child_id);
      const auto cp_sib = mgr.VerifySiblingQueryReplay(
          p004.initial_position, p004.proof_context, corrupt_redir, {},
          ldprover::kPassMove, pass_child_id, 21);

      auto corrupt_redir_src = rp4;
      corrupt_redir_src.proof_dag_nodes[pass_child_id].is_pruned_outside_rz =
          true;
      corrupt_redir_src.proof_dag_nodes[pass_child_id].source_proof_node_id =
          move_21_id;
      corrupt_redir_src.proof_dag_nodes[move_21_id].child_moves.push_back(0);
      const auto cs_sub = mgr.VerifySubproofAtPath(
          p004.initial_position, p004.proof_context, corrupt_redir_src,
          {ldprover::kPassMove}, pass_child_id);
      const auto cs_sib = mgr.VerifySiblingQueryReplay(
          p004.initial_position, p004.proof_context, corrupt_redir_src, {},
          ldprover::kPassMove, pass_child_id, 21);

      Check(!ct_def.passed && ct_def.error_code == "LP-T02" &&
                ct_def.failed_node_id == static_cast<int32_t>(pass_child_id) &&
                !ct_sem.passed && ct_sem.error_code == "LP-T02" &&
                !ct_sib.passed && ct_sib.error_code == "LP-T02" &&
                !cr_sub.passed && cr_sub.error_code == "LP-T02" &&
                !cr_sib.passed && cr_sib.error_code == "LP-T02" &&
                !cc_sub.passed && cc_sub.error_code == "LP-T02" &&
                !cc_sib.passed && cc_sib.error_code == "LP-T02" &&
                !cp_sub.passed && cp_sub.error_code == "LP-R02" &&
                !cp_sib.passed && cp_sib.error_code == "LP-R02" &&
                !cs_sub.passed && cs_sub.error_code == "LP-T02" &&
                cs_sub.failed_node_id == static_cast<int32_t>(move_21_id) &&
                !cs_sib.passed && cs_sib.error_code == "LP-T02",
            "Structural prechecks catch mismatched parallel arrays, self-loops, and bad redirects before indexing");
    }
  }

  // 3. Near-pn continuation zero/one/default budgets (p031@120) & p060@3500 determinism.
  {
    const ParsedProblem<19> p031 = BuildP031();
    Check(p031.valid, "Inline p031 parses cleanly for R27 zero/1/64 checks");
    auto run_p031 = [&](bool enabled, uint32_t max_calls,
                        SolveReport<19>* out_rep,
                        ldprover::ConvergenceTraceReport* out_tr) {
      SolverConfig cfg = DefaultConfig(120U);
      cfg.max_depth = 48U;
      cfg.memory_budget_bytes = 512ULL * 1024ULL * 1024ULL;
      cfg.enable_near_pn_continuation = enabled;
      cfg.near_pn_continuation_max_calls = max_calls;
      cfg.enable_convergence_trace = true;
      cfg.observed_paths = {"", "ps"};
      DfpnSolver<19> s(cfg);
      *out_rep = s.Solve(p031.initial_position, p031.proof_context,
                         p031.region_search_mask, "p031_120");
      *out_tr = s.ConvergenceTrace();
    };
    SolveReport<19> r_d, r_0, r_1, r_64;
    ldprover::ConvergenceTraceReport t_d, t_0, t_1, t_64;
    run_p031(false, 64U, &r_d, &t_d);
    run_p031(true, 0U, &r_0, &t_0);
    run_p031(true, 1U, &r_1, &t_1);
    run_p031(true, 64U, &r_64, &t_64);
    const std::string j_d = mgr.SerializeLProofJson(
        p031.initial_position, p031.proof_context, r_d);
    const std::string j_0 = mgr.SerializeLProofJson(
        p031.initial_position, p031.proof_context, r_0);

    Check(j_d == j_0 && r_0.num_nodes == 120U && !t_0.near_pn_continuation.enabled &&
              !t_0.near_pn_continuation.claimed &&
              t_0.near_pn_continuation.trigger_node == 0ULL &&
              t_0.near_pn_continuation.exit_node == 0ULL &&
              t_0.near_pn_continuation.extra_calls_spent == 0ULL,
          "p031@120 with near_pn_continuation_max_calls=0 disables claims (0 extra calls) and matches Arm D",
          "claimed=" + std::to_string(t_0.near_pn_continuation.claimed) +
              " extra=" +
              std::to_string(t_0.near_pn_continuation.extra_calls_spent));
    Check(r_1.num_nodes == 120U && t_1.near_pn_continuation.enabled &&
              t_1.near_pn_continuation.claimed &&
              t_1.near_pn_continuation.claimed_path == "ps" &&
              t_1.near_pn_continuation.trigger_node == 74ULL &&
              t_1.near_pn_continuation.exit_node == 75ULL &&
              t_1.near_pn_continuation.extra_calls_spent == 1ULL,
          "p031@120 with max_calls=1 claims at node 74 and stops at node 75 (+1 call)",
          "trig=" + std::to_string(t_1.near_pn_continuation.trigger_node) +
              " exit=" + std::to_string(t_1.near_pn_continuation.exit_node) +
              " extra=" +
              std::to_string(t_1.near_pn_continuation.extra_calls_spent));
    Check(r_64.num_nodes == 120U && t_64.near_pn_continuation.enabled &&
              t_64.near_pn_continuation.claimed &&
              t_64.near_pn_continuation.claimed_path == "ps" &&
              t_64.near_pn_continuation.trigger_node == 74ULL &&
              t_64.near_pn_continuation.exit_node == 83ULL &&
              t_64.near_pn_continuation.extra_calls_spent == 9ULL,
          "p031@120 with max_calls=64 claims at node 74 and exits at node 83 (+9 calls)",
          "trig=" + std::to_string(t_64.near_pn_continuation.trigger_node) +
              " exit=" + std::to_string(t_64.near_pn_continuation.exit_node) +
              " extra=" +
              std::to_string(t_64.near_pn_continuation.extra_calls_spent));

    SolverConfig cfg_d60 = DefaultConfig(3500U);
    const auto rd60 = DfpnSolver<19>(cfg_d60).Solve(
        p060.initial_position, p060.proof_context, p060.region_search_mask,
        "p060_3500");
    SolverConfig cfg_060 = DefaultConfig(3500U);
    cfg_060.enable_near_pn_continuation = true;
    cfg_060.near_pn_continuation_max_calls = 0U;
    const auto r060 = DfpnSolver<19>(cfg_060).Solve(
        p060.initial_position, p060.proof_context, p060.region_search_mask,
        "p060_3500");

    SolverConfig cfg_e_off = DefaultConfig(3500U);
    cfg_e_off.enable_near_pn_continuation = true;
    cfg_e_off.near_pn_continuation_max_calls = 64U;
    SolverConfig cfg_e_on = cfg_e_off;
    cfg_e_on.enable_convergence_trace = true;
    cfg_e_on.observed_paths = {"", "rs"};

    const auto re_off = DfpnSolver<19>(cfg_e_off).Solve(
        p060.initial_position, p060.proof_context, p060.region_search_mask,
        "p060_e");
    DfpnSolver<19> se_on(cfg_e_on);
    const auto re_on =
        se_on.Solve(p060.initial_position, p060.proof_context,
                    p060.region_search_mask, "p060_e");
    const std::string jd60 = mgr.SerializeLProofJson(
        p060.initial_position, p060.proof_context, rd60);
    const std::string j060 = mgr.SerializeLProofJson(
        p060.initial_position, p060.proof_context, r060);
    const std::string je_off = mgr.SerializeLProofJson(
        p060.initial_position, p060.proof_context, re_off);
    const std::string je_on = mgr.SerializeLProofJson(
        p060.initial_position, p060.proof_context, re_on);
    const auto& nt = se_on.ConvergenceTrace().near_pn_continuation;
    Check(jd60 == j060 && re_on.num_nodes == 3500U && je_off == je_on &&
              nt.enabled && nt.claimed && nt.claimed_path == "rs" &&
              nt.trigger_node == 2631ULL && nt.exit_node == 2656ULL &&
              nt.extra_calls_spent == 25ULL,
          "p060@3500 deterministically claims B[rs] (2631->2656, +25 calls), honors parity, and matches Arm D at max_calls=0",
          "claimed=" + std::to_string(nt.claimed) +
              " path=" + nt.claimed_path +
              " extra=" + std::to_string(nt.extra_calls_spent));
  }
}

}  // namespace

int main() {
  TestSection1SearchRegression();
  TestSection2ScopeParity();
  TestSection3FullStateBindingAndContradictoryRoot();
  TestSection4R7ProtocolEdgeCases();
  TestSection5R8ProblemContractAndConsistency();
  TestSection6RealProblemSolverBreakthrough();
  TestSection7R9EyeLikePassParity();
  TestSection8GenerateLegalMovesSemantics();
  TestSection9IncrementalZobristParity();
  TestSection10OrthoNeighborTableParity();
  TestSection11ConvergenceObserverParity();
  TestSection12R27ObserverAndNearPnContinuation();

  const int failed = g_total - g_passed;
  std::cout << "\n========================================\n"
            << "R5 C++20 Regression Summary: " << g_passed << "/" << g_total
            << " passed, " << failed << " failed.\n"
            << "========================================\n";
  return failed == 0 ? 0 : 1;
}
