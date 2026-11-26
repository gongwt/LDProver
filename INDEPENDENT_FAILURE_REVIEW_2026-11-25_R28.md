# R28 独立复审：R27 片段归属、结构预检与零额度

**裁决。** 接受原始已证 DAG 的边归属校验、首次索引前的结构预检、零额度修复。整批候选还剩一个 P1，限于 C++ 兄弟重放公开入口对**源边归属**的承诺。正式原根文件、默认搜索和 R27 停止续搜的裁决均可沿用。

## 候选与独立验证

本机核对 HEAD 为 `0a1abb66eb48abf5ac37ca85185a45d572b3dc85`。复审前后 `git diff HEAD -- cpp` 的 SHA-256 均为 `87699f74fa54bc1889c3a4b7aad35cb49626c3297d87a500ded3cfeb1c123ef8`，覆盖交接中的七个 C++ 文件。[R27 验收条件](./INDEPENDENT_FAILURE_REVIEW_2026-11-25_R27.md) · [实施方报告](</Users/go4ai/.gemini/antigravity/brain/409858d5-d8bb-46a6-96b1-acd16ced4db3/r27_observer_fixes_and_p060_continuation_report.md>)

| 检查 | 本次结果 |
|---|---|
| 干净 Release 构建与 CTest | 2/2，26.61 秒。原生核心 301/301，本机 POSIX CLI 18/18。另行编译强制便携后备 CLI，顺序子集 17/17。 |
| 默认 Arm D，3500 节点档 | 逐份生成文件，对比归档中干净 HEAD 的完整 SHA-256，4/4 相符。当前候选校验器绑定原题读回：p031（1908 节点）、p042（329）均 PASS；p060、p090（各 3500）均为 LP-U01，退出码 2。 |
| 实施方补充项 | TS 274/274 为交付记录；本轮未改 TS，未重新运行 TS 套件。项目缺本地依赖，lint 没有本轮通过结果。便携后备的结果限于本机，Windows 原生未测。 |

## 已通过的行为

- **已证根。** p004 的 PASS 和着法 21 指向不同的原始 DAG 边。在路径 21 请求 PASS 的 DAG，默认严格入口返回 LP-R02 并给出实际边 ID；显式语义重放通过。着法 2 的负对照仍被拒绝。p060@500 的直接片段入口也能分别表达“未决根、语义通过”和“要求已绑定原边、LP-U01”。[绑定策略](./cpp/include/ldprover/proof/proof_checker.h#L100) · [成对断言](./cpp/tests/r5_regression_test.cc#L1628)
- **结构预检。** 两个公开入口在索引平行子边数组前都经过预检，兄弟入口通过源片段校验进入该检查。目标与根的数组错长、自环、非法重定向及错长的重定向源均有回归，返回 LP-T02 或 LP-R02。[结构检查](./cpp/src/proof/proof_checker.cc#L2998) · [原生用例](./cpp/tests/r5_regression_test.cc#L1764)
- **额度。** p031@120 的 API 零额度未领取，与 Arm D 逐字节一致。额度 1 在 74 → 75 消耗 1 次，额度 64 在 74 → 83 消耗 9 次。CLI 的显式额度参数要求正整数，0 返回退出码 2。本轮未扩展 R27 正式实验矩阵。[领取条件](./cpp/src/search/dfpn_solver.cc#L2221) · [CLI 边界](./cpp/tests/cli_boundary_test.cc#L955)

## 剩余 P1：兄弟重放只保留了查询侧的归属

头文件说明兄弟入口会先严格验证源边，再语义重放查询手。实现实际使用 `kStrictWhenRootProven` 检查源：在 UNKNOWN 根，只要片段能在所称源局面证明结论，就可通过。源回执中的 `unbound_unknown_root` 在成功路径被丢弃；对外只留下查询侧的 `unbound_replay_only`。据此可以报告语义重放成功，却无法判断所称源手在这次搜索中是否产生了该证明。[公开承诺](./cpp/include/ldprover/proof/proof_checker.h#L120) · [源策略与回执重建](./cpp/src/proof/proof_checker.cc#L3386)

**自然产生的反例。** 用版本化 `BuildP004()`、`DefaultConfig(6)`，观察根及 `ed`、`pass`、`cb`、`ca`。原根按预算返回 UNKNOWN，共 6 次调用、4 个 DAG 节点。观察器记录 `cb`（21）已闭合，DAG ID 为 1；`ed`（61）从未试走，DAG ID 为无效哨兵。保持报告原样，以 `ed` 为源手、DAG 1 为源片段、`cb` 为查询手，兄弟入口返回 PASS / `unbound_replay_only`。仅把源手换为 `ca`（2）则返回 LP-R02。这说明语义检查确实在工作；前一次 PASS 没有建立 `ed → DAG 1` 的历史归属。该问题影响对复用来源的证明力度，本次没有发现原根胜负误判。

**最小修复与停止条件。** 严格验证来源的入口使用 `kRequireBoundRootEdge`；需要保留 UNKNOWN 根上的语义诊断时，可以显式选择该模式，并在结果中分别保留源绑定状态和查询重放结果。验收用同一份 p004@6 报告：严格请求得到 LP-U01；显式语义请求可以 PASS，但源归属须可读为未绑定。再用已证 p004 的真实 PASS 边重放到 21，确认合法来源仍能通过。完成这组成对断言即可关闭本项；无需改动求解策略或重跑 16 题矩阵。
