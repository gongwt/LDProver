# R31 独立复审｜任务卡 ①a 的发布与资源认证

**裁决：接受 macOS 功能验收。退回两项影响正式计数的 P1，修复后进入 Linux 小限额验收。** 本轮候选已能区分“原根证明已验证”“证明文件已发布”“具备正式计数资格”。可保留本轮搜索内核和监督器的功能改动。冻结 Arm D 作为 600 秒、2 GB 性能基线仍需补齐以下证据。[R30 验收卡](./INDEPENDENT_FAILURE_REVIEW_2026-11-25_R30.md)

## 1. 候选与实际复核范围

| 身份 | 本机核对结果 |
|---|---|
| HEAD | `cdf8979d880bc7805e2de8517eb2881acbc5cfad` |
| 5 个 C++ 文件相对 HEAD 的补丁 SHA-256 | `73ca6875456a0ab899e439d1b4f866bc234ca5fd03cb6dd7a7c33e7921d9c03b`，与 R30 相同 |
| 监督器 SHA-256 | `d0454c9218e5bdc330b85a68206a35a5117f760fb1b333cec3af6c079f1057b4` |
| 边界测试 SHA-256 | `42cd839b681324053871c91e7d702766d2cba8e1ec9cf0876ff6286f472fc2fa` |

本机为 macOS。复用 R30 独立构建的同补丁 Release 二进制，运行当前版监督器套件。首次在受限环境运行时第一个正常样例返回 UNKNOWN；在允许本机进程计量的环境重跑后 **10/10 通过**。本轮未重新编译 C++，亦未重跑其 306 项内核与 19 项 CLI 回归。已核对实现方第 2192 步的逐项输出及冒烟回执。[测试入口](./scripts/verify_supervised_resource_boundary.mjs#L89) · [实现方原始输出](</Users/go4ai/.gemini/antigravity/brain/409858d5-d8bb-46a6-96b1-acd16ced4db3/.system_generated/steps/2192/output.txt>)

**已接受的行为**　p031 与 p042 的正常输出通过独立原题文件校验，macOS 回执保持 `budgetCertified=false`。p042 省略证明路径时正确返回 `verified=true, published=false`。发布前延迟跨截止会保全旧文件，已覆盖的九组静态路径冲突均被拒绝。工作进程组在硬截止前能被正对照探针看到，终止后探针观察到该组为空。默认内核软内存比例仍为 0.85。[发布与进程组断言](./scripts/verify_supervised_resource_boundary.mjs#L150) · [路径矩阵](./scripts/verify_supervised_resource_boundary.mjs#L417)

## 2. P1：独立 OOM 计数合并后丢失事件

监督器分别解析 `oom`、`oom_kill`，随即取两者最大值作为起点和终点，再计算差值。两个内核计数语义不同，一个记录内存限额引发的分配困境，一个记录被 OOM killer 杀死的进程数。只要其中一个字段存在，解析还会把另一个缺失字段补零。现有测试让两个字段从零同时变为一，恰好避开了差异。[快照解析](./scripts/supervised_solve.mjs#L349) · [轮询判定](./scripts/supervised_solve.mjs#L644) · [现有测试](./scripts/verify_supervised_resource_boundary.mjs#L659) · [Linux 内核字段定义](https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html)

本轮直接调用公开快照读取函数，以相同内存读数输入三条合成记录。下表为函数的实际结果。这里复核的是计量算术，未触发内核 OOM。

| 输入 | 读取结果 | 对回执的影响 |
|---|---|---|
| 起点 `oom=5, oom_kill=1` | `ok=true, oomEvents=5` | 比较基准为 5 |
| 终点 `oom=5, oom_kill=2` | `ok=true, oomEvents=5` | 新增一次 kill，按现逻辑差值仍为 0 |
| 仅有 `oom=5` | `ok=true, oomKillCount=0` | 把缺测记录成实测零 |

**验收**　完整保留两组基准、终值及各自增量。区分“发生 OOM”和“有进程被杀”；任一必需字段缺失、非法或计数倒退时取消计量资格。保留全零正例，补单独递增各字段、只有一项缺失、计数倒退的对照，并把结果一直断言到最终回执。

## 3. P1：整题预算认证仍使用提交前的内存快照，且没有最终时间条件

当前流程先检查 cgroup 和截止时间，再改名发布文件，随后**把发布后的整个文件读入内存计算 SHA-256**，清理暂存目录，最后计算 `totalWallMs`。签发 `budgetCertified` 时没有读取终态 cgroup，也没有比较完成时间与总截止。这样，即使摘要读回发生缺测、额外内存峰值，或完整流程已耗尽预算，先前记录的峰值和 PASS 仍足以使 Linux 分支给出正式计数资格。另有一小段路径预检在总计时开始之前。此结论来自控制流审阅；macOS 始终关闭正式认证，现有 10 个通过用例无法观测这一误计数分支。[计时起点](./scripts/supervised_solve.mjs#L833) · [提交前取样](./scripts/supervised_solve.mjs#L1395) · [整文件摘要](./scripts/supervised_solve.mjs#L122) · [发布后读回与清理](./scripts/supervised_solve.mjs#L1458) · [最终认证条件](./scripts/supervised_solve.mjs#L963)

**验收**　保留 R30 已约定的提交前截止检查。正式计数另设完成点，覆盖发布文件的摘要读回和约定清理，以同一单调钟判断截止，并取一次完整终态内存快照后再判资格。哈希采用有界缓冲。若文件已实际发布而结算时超限，应同时保留发布事实及超限原因，正式计数为零。正例仍需文件读回、摘要一致、全程预算合格；分别注入仅在发布完成后出现的迟到、缺测或峰值越限。若 OOM 终止监督器本身，由组外启动器收集终态并记录该题结果。

## 4. P2：测试套件尚不能直接用于目标 Linux 环境

第 10 组把临时目录当作“有效 cgroup”，并在判断平台前无条件要求其通过。生产预检在 Linux 明确要求目录位于真实 cgroup 挂载点，且匹配本进程所属组。因此在正常 Linux 上，该用例预期与生产预检互斥。macOS 已通过的模拟正例应保留。建议把快照解析的夹具测试与真实专用组集成测试分开，Linux 缺少委派环境时报告明确的“未运行”。Linux 上普通临时目录被拒绝本身是一个有效负例。[Linux 预检](./scripts/supervised_solve.mjs#L432) · [测试正例](./scripts/verify_supervised_resource_boundary.mjs#L529)

真实实验每题使用新建专用组，或由启动器给出独立峰值窗口的证据。目前预检确认组内包含监督器 PID，但没有据此证明该组专用或其 `memory.peak` 只属于本题。记录实际 `memory.max`、swap、组身份、两个 OOM 增量、终态峰值和核验用的证明文件。验收主机缺席时维持“Linux 待验证”。[成员核验](./scripts/supervised_solve.mjs#L413) · [Linux 峰值语义](https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html)

## 5. 下一步与停止点

把下一轮限定为 **①a 的认证结算修正**。Neon 主责监督器，Hydrogen 主责差分用例与真实 Linux 小限额证据，Astra 按同一候选复审。继续冻结 C++、0.85 默认比例、搜索规则和证书。先验本报告的计数与收尾正反例，再执行 R30 已约定的小限额矩阵，列出每格条件、实际耗时、内存与文件身份。若只有 macOS 环境，可完成机制修复并单独交付；全量正式基线仍待 Linux 资格成立。

**停止条件**　发现超预算仍能计数、缺测被记为零，或无法取得真实 Linux 证据时，停止正式放行。修正通过后冻结可重建 Arm D，再做前沿双 RZ 紧凑化的小档对照。此轮未改源码、未提交、未启动 16 题长跑。
