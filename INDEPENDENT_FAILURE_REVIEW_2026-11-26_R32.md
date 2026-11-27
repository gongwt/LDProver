# R32 独立复审｜资源结算修复与 Linux 验收入口

**裁决：R31 两项 P1 在正常求解入口可以关闭。** OOM 与 OOM kill 的独立增量已接入搜索、校验和结算；正式计数会检查发布读回、清理、终态计量与总截止。R31 指出的 Linux 测试平台冲突也已修复。本轮新增两项 P2，分别影响缺测回执的解释和公开判定函数的直接调用。下一项决定取决于真实 Linux 专用组的小限额正反例。16 题正式基线继续暂缓。[R31 验收条件](./INDEPENDENT_FAILURE_REVIEW_2026-11-25_R31.md)

## 1. 候选身份与验证范围

| 核对项 | 独立结果 |
|---|---|
| HEAD | `cdf8979d880bc7805e2de8517eb2881acbc5cfad` |
| 5 文件 C++ 补丁 SHA-256 | `73ca6875456a0ab899e439d1b4f866bc234ca5fd03cb6dd7a7c33e7921d9c03b` |
| 监督器 / 边界套件 SHA-256 | `3a191eb4697389c31efd05a13a2c586613f6ef3baf82cc0226402a3651a97536` / `ef69c470110864f9bb5cbda9938dfa31735c04d64d1e7f5a773a0fd7c9151c2c` |
| macOS 独立 Release 构建 | CTest 两目标通过，内核 306/306、CLI 19/19 |
| 同一二进制的监督器回归 | 12/12 通过；真实 Linux 专用组明确报 `NOT RUN` |

已核对实现方原始输出。独立套件使用本机进程计量权限。另做的 p042 成对实验在受限环境首次尝试时停于 worker，两个样例均未到达结算；下表采用允许本机计量后、实际到达结算的两条回执。本机为 Darwin，本机 Docker 服务经只读查询无法连接。本轮未改源码、未提交，未使用 16 题正式额度。[实现方原始输出](</Users/go4ai/.gemini/antigravity/brain/409858d5-d8bb-46a6-96b1-acd16ced4db3/.system_generated/steps/2252/output.txt>) · [本轮 CTest 原始日志](/tmp/r32-review.banF0gYa/tests.log)

## 2. 已关闭的问题

- **OOM 的两个计数能独立触发退出。** 版本化反例从 `(oom=5, oom_kill=1)` 变为 `(5,2)`，回执报告增量 `(0,1)`，原因是 `cgroup_oom_kill`；只有 `oom` 增加时另行归因。缺字段和计数倒退时取消计量资格。[增量判定](./scripts/supervised_solve.mjs#L414) · [端到端断言](./scripts/verify_supervised_resource_boundary.mjs#L798)
- **发布事实与预算结论可以同时成立、分别记账。** 计时从路径检查前开始；摘要按 64 KiB 读取。成功提交后，监督器完成读回和清理，取得终态快照，再用同一单调钟校验截止。p042 发布后延迟的原始记录为 2,414.692 ms，对应限额 1,800 ms，文件保留原根胜证，任务返回 `UNKNOWN / settlement_timeout`，正式计数资格为假。独立套件复验了同一行为。[流式摘要](./scripts/supervised_solve.mjs#L128) · [终态结算](./scripts/supervised_solve.mjs#L1750) · [延迟与内存边界测试](./scripts/verify_supervised_resource_boundary.mjs#L916)
- **Linux 的生产预检与夹具测试已分开。** 普通临时目录在 Linux 上的预期为拒绝；专用组正例有独立入口。源码与 macOS 回归支持关闭原来的平台分支冲突，Linux 硬限额实机结果仍待取得。[平台分支](./scripts/verify_supervised_resource_boundary.mjs#L699) · [真实组入口](./scripts/verify_supervised_resource_boundary.mjs#L1052)

## 3. P2：终态缺测时，旧计数仍显示为终值

用同一 Release 二进制、p042 原题、3,500 次调用上限、深度 48 和 10 秒总截止。在 macOS 合成 cgroup 中，两次起点同为 `(5,1)`，仅改变结算读取时 `oom_kill` 字段是否存在。两次均搜索 329 次、文件独立验真通过，发布证明字节 SHA-256 同为 `f176c88f7124e99523b0d96ac5ca5b602eadd68c381588187c4743fb757643ee`。

| 结算输入 | 任务与计量结果 | 回执 final 两计数 / 两增量 | 总墙钟 |
|---|---|---|---:|
| 两字段完整 | 胜，计量完整 | `(5,1) / (0,0)` | 858.975 ms |
| 缺少 `oom_kill` | UNKNOWN，`metering_unavailable`，取消资格 | **仍为 `(5,1) / (0,0)`** | 865.655 ms |

第二条回执已准确记录 `memory.events_oom_kill_missing`。但终态读取失败的分支直接返回，字段保留了先前成功采样的值。下游若统计“有多少题确认没有发生 kill”，这条记录会混入实测零。最小修复是让未获得的终值和相应增量返回 `null`；需要保留的先前值可显式标作最后一次成功观测。给现有缺测用例补这组字段断言即可。[失败分支](./scripts/supervised_solve.mjs#L1244) · [正例回执](/tmp/r32-pair.D7hV4L/control.receipt.json) · [缺测回执](/tmp/r32-pair.D7hV4L/missingFinalKill.receipt.json)

## 4. P2：公开认证判定函数接受缺失胜负和负峰值

直接调用导出的 `evaluateCertificationDecision`。固定 Linux、完整 cgroup 计量、已验已发布、结算成功、两项 OOM 增量为零等输入，分别只改变一个字段。合法胜证且峰值为 12,000,000 B 时正式计数为真；结论改为 `UNKNOWN` 时为假；**省略结论时为真，单独将峰值改为 −1 B 时也为真**。原因是结论只排除一个字符串，峰值只检查非空和上界。这是纯函数契约测试。正常求解入口另有胜负枚举筛选与内核快照解析，本轮未观察到它误计原题。建议在公开判定入口直接要求胜或败的合法枚举，以及非负安全整数峰值、合法的正整数预算。给以上两种直接调用各补一条拒绝断言。[判定函数](./scripts/supervised_solve.mjs#L950) · [生产入口筛选](./scripts/supervised_solve.mjs#L1514) · [现有判定单测](./scripts/verify_supervised_resource_boundary.mjs#L635)

## 5. 下一步只做真实 Linux 小限额验收

当前 `--real-linux-cgroup-dir` 第 13 组只测 p042 成功路径。它在前 12 组之后、同一测试进程里执行，最终删除临时目录中的证明，且该格没有指定持久回执路径。如果把整个套件预先放进同一个 cgroup，第 13 格读取的组峰值可能包含前面的工作。单见绿色汇总，仍无法复核 p042 的专属峰值或真正到限时的退出记录。[入口、断言及清理](./scripts/verify_supervised_resource_boundary.mjs#L1052)

**交接给 Hydrogen 的验收顺序**　基于同一候选，在 Linux 上从组外分别启动两个新建专用组，每格一题一次、总截止最多 10 秒，先登记机器、二进制摘要、`memory.max` 和零 swap。第一格用 p042 正常发布，持久保存原题身份、证明、最终回执及组计量；第二格用有界工作负载验证内核限额确实生效，保存组外观测的退出状态、`memory.events` 前后值、峰值和正式计数结果。若监督器本身被终止，组外记录仍须能解释本次结果。Neon 可在同一候选补两项 P2，复验既有通过项并记录新脚本摘要。Astra 以实机原始产物裁定；实机不可用就保留当前停点。通过后冻结 Arm D，再开始前沿双 RZ 紧凑化的小档对照。
