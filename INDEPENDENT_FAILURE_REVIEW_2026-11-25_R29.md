# R29 独立复审：关闭兄弟重放源边归属 P1

**裁决：通过。** 当前七文件候选满足 R28 的停止条件，可以交由集成人提交。默认入口要求已证根能把源着法绑定到指定 DAG 节点；显式诊断允许在未决根重放，并保留源边未绑定的事实。R27 临界 pn 续搜实验至此结项，Arm D 继续作为默认策略。[R28 验收条件](./INDEPENDENT_FAILURE_REVIEW_2026-11-25_R28.md)

## 验收对象

基线提交为 `0a1abb66eb48abf5ac37ca85185a45d572b3dc85`。本机核对 `git diff HEAD -- cpp` 的 SHA-256 为 `f28ec71e37f1c32c8dfd6da235ba396bab4389ed7e0ebd2d5118b68a365272e2`。以下检查针对这份未提交候选。实现先按所选策略验证来源；若源验证失败，直接返回源阶段错误。只有源验证通过，才建立查询回执，保留源状态并执行查询局面重放。CLI 观察器显式选择策略。[公开接口](./cpp/include/ldprover/proof/proof_checker.h#L124) · [源校验与查询回执](./cpp/src/proof/proof_checker.cc#L3386) · [CLI 调用点](./cpp/src/cli/tprover_main.cc#L1652)

## 同一份 p004 报告的成对结果

本次在独立 Release 构建上直接调用公开接口。用版本化 p004 题面、6 次调用预算，得到 UNKNOWN 原根与 4 个 DAG 节点。根前沿确认 `cb`（21）经试走闭合至 DAG 1，`ed`（61）从未试走。前三行复用同一内存报告、路径和 DAG 1，只切换源绑定策略。[版本化回归](./cpp/tests/r5_regression_test.cc#L1768)

| 输入与策略 | 回执 | 源归属 | 查询重放 |
|---|---|---|---|
| 未决根，ed → cb，默认 | LP-U01 | unbound_unknown_root，源 ID −1 | 源阶段即停止 |
| 同上，显式 kSemanticReplayOnly | PASS | unbound_replay_only，源 ID −1 | 通过 |
| 同上，显式 kStrictWhenRootProven | PASS | unbound_unknown_root，源 ID −1 | 通过 |
| 同一未决根，以 ca 为源，DAG 1 → cb，显式语义模式 | LP-R02 | unbound_replay_only，源 ID −1 | 源语义检查失败 |
| 已证根，真实 PASS 边 → cb，默认 | PASS | bound_to_root_dag，源 ID 5 | 通过，查询边记录 ID 1 |
| 同一已证根与源，仅将查询手改成 ca | LP-R02 | bound_to_root_dag，源 ID 5 | 失败，查询边记录 ID 3 |

已证正例使用 50 次预算，实际 8 次调用、11 个 DAG 节点。最后两行说明调用方可以分别回答“这份证明从哪里来”和“它能否在另一手上成立”。在未决根上，显式诊断的 PASS 只支持局面语义结论。

## 原生回归与默认产物

- 从当前源代码新建 Release 构建，CTest 2/2，26.99 秒。核心 302/302，本机 POSIX CLI 18/18。另行编译强制便携后备 CLI，顺序子集 17/17。Windows 原生分支不在本机覆盖范围。
- 以 Arm D、3500 次调用上限、深度 48、512 MiB、PatternTT 重新生成四份默认文件，逐份对比归档的干净 HEAD 文件 SHA-256，4/4 相符。当前候选校验器绑定原题，以 original_root 读回：p031（1908 次）、p042（329 次）均 PASS，退出码 0；p060、p090（各 3500 次）均为 LP-U01，退出码 2。[基线摘要原始记录](</Users/go4ai/.gemini/antigravity/brain/409858d5-d8bb-46a6-96b1-acd16ced4db3/scratch/r27_experiment_results.json>)
- 复审范围为 C++ 候选、原有停止条件和上述回归。TS 未重测，16 题续搜实验维持停止。项目本轮只新增本报告，候选源码由集成人按授权提交。
