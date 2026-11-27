# R34 独立复审｜双格验收的截止与排空证据

**裁决：接受 R33 的内核事件归因修复和输出目录隔离；两项 P1 仍阻塞正式 Linux 验收。** 新运行器已经能拒绝纯软停、只有 SIGKILL 的退出和缺失整份末快照。剩下的问题集中在两个组合条件：观测到了 OOM 的同时已经超时，以及末快照可读但没有排空读数。这两种情形仍可能计为 PASS。[R33 验收条件](./INDEPENDENT_FAILURE_REVIEW_2026-11-26_R33.md)

## 验收对象与范围

| 对象 | 本机核对的身份或结果 |
|---|---|
| HEAD | `cdf8979d880bc7805e2de8517eb2881acbc5cfad` |
| C++ 五文件补丁 SHA-256 | `73ca6875456a0ab899e439d1b4f866bc234ca5fd03cb6dd7a7c33e7921d9c03b` |
| 监督器 / 监督器回归套件 SHA-256 | `827dc867c0f6f9870812c07ccdcfd39e2c0c837fd61bc969cfd4bc6ccdbf3821` / `25fa573bfcc91dad0bb0f654aad93e450eba9a37527e0546f0feb7522b2ff918` |
| 双格运行器 / 新逻辑套件 SHA-256 | `e201892b33aa56fea561d826afdd4392f8f70f4c217fd9f62cf2672cbe733fdc` / `7f06d1d74f201d17ed5647f778cb73156859bf8ecf3f2788dc1f4931f071b4fe` |

在 Darwin 上独立运行新逻辑套件，**5/5 通过**，包括非 Linux 入口退出码 3、输出目录独占和既有故障记录断言。哈希与交接原始输出一致。只复核有改动的运行器和逻辑套件，未重跑 C++、监督器回归或题库搜索。以下追加检查使用普通临时目录及合成计量；负格走公开生命周期和默认快照读取、排空函数，以钩子代替工作进程和真实建组、删组。正格另直接调用公开判定函数。所有报告中的毫秒数与 OOM 事件数若来自夹具，均为输入值。[逻辑套件](./scripts/verify_linux_two_cells_logic.mjs#L134) · [实现方原始输出](</Users/go4ai/.gemini/antigravity/brain/409858d5-d8bb-46a6-96b1-acd16ced4db3/.system_generated/steps/2320/output.txt>)

## 决定放行的成对检查

负格对照固定组外上限 10,000 ms、末快照两个 OOM 计数各增 1、无证明、无内层回执。正格对照具有合法胜证回执、摘要与独立 checker PASS。

| 对照及唯一条件变化 | 当前实际结果 | 验收结论 |
|---|---|---|
| 负格，20 ms，排空读数为 0 | PASS，已观察到 OOM kill | 接受 |
| 负格，同一事件增量，组外截止触发并由运行器终止，耗时字段为 10,025 ms | **PASS**，无失败原因 | 应保留 OOM 事实，整格超时失败 |
| 负格，同一事件增量，仅在末快照前移除 `cgroup.events` | **PASS**，`populated=null` 且 `cgroupDrainedEmpty=true` | 排空证据不完整，应失败 |
| 正格，仅把组外耗时从 40 改为 10,025 ms，定时回调标志仍为 false | **PASS_CERTIFIED** | 组外实测用时已超预算，应失败 |

**P1 · 把组外截止作为两格共用的通过条件。** 负格只在没有内核事件时拿超时标志解释原因；一旦 OOM 增量为正，超时和主动终止就不会阻止通过。正格检查布尔标志，但没有比较已经记录的单调耗时与配置上限。建议用未舍入的单调时间判定到期，在公共判定中核验运行窗口、超时及组外主动终止，同时保留 `kernelIntervention`。清理残余进程和额外文件审计继续分开计时。这样“观察到 OOM”和“在预算内完成该格”都能如实回看。[组外计时](./scripts/verify_linux_cgroup_two_cells.mjs#L579) · [正格判定](./scripts/verify_linux_cgroup_two_cells.mjs#L388) · [负格判定](./scripts/verify_linux_cgroup_two_cells.mjs#L494)

**P1 · 排空必须取得有效零值。** 读取快照时允许缺少 `cgroup.events`，返回 `ok=true, populated=null`；默认排空函数在同样情况下把 `populated` 初始化为 0；公共判定仅拒绝值恰好等于 1。直接进程列表为空只说明当前层没有列出的进程；递归子树是否仍有进程由 `populated` 提供。建议两个读取入口共用严格解析，要求有效 PID 列表和唯一的 0/1 排空读数。缺失、非法值及读失败分别留档；只有有效空列表且 `populated===0` 才接受末快照。本轮在正格直接判定中也确认，把有效末读数改成 null 仍得到 PASS。[快照读取](./scripts/verify_linux_cgroup_two_cells.mjs#L244) · [默认排空](./scripts/verify_linux_cgroup_two_cells.mjs#L619) · [公共判定](./scripts/verify_linux_cgroup_two_cells.mjs#L322) · [Linux cgroup 文档](https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html)

本次负格的原始临时记录可与上表交叉核对。[正常对照](/var/folders/vn/x8gswgsj77n_pby8mrd6_qwh0000gn/T/r34-local-Ja9Eky/control/neg_outer_record.json) · [超时且有 OOM](/var/folders/vn/x8gswgsj77n_pby8mrd6_qwh0000gn/T/r34-local-Ja9Eky/over-time/neg_outer_record.json) · [缺失排空读数](/var/folders/vn/x8gswgsj77n_pby8mrd6_qwh0000gn/T/r34-local-Ja9Eky/no-events/neg_outer_record.json)

## P2 · 两处故障记录需要收尾

- **建组部分成功时会留下空组。** 默认准备函数先建目录再配置两项限额，调用方在整个函数返回后才登记所有权。通过钩子注入“目录已创建、配置写入失败”，外层文件正确记录 `FAIL / preflight`，已建目录却仍在。建议在成功创建时登记所有权，让后续配置失败走相同回收路径。回归还应证明预先已存在的目录不会被移除。[准备函数](./scripts/verify_linux_cgroup_two_cells.mjs#L789) · [所有权标志](./scripts/verify_linux_cgroup_two_cells.mjs#L847) · [清理](./scripts/verify_linux_cgroup_two_cells.mjs#L951)
- **失败分类仍可能以 PASS 开头。** 在观测到 OOM kill 但排空未获确认的夹具中，持久记录顶层是 `FAIL`，分类却是 `PASS_KERNEL_OOM_KILL_OBSERVED`。汇总布尔值正确。建议由 `kernelIntervention` 单列观测到的事件，失败分类表达实际拒绝原因。[分类返回](./scripts/verify_linux_cgroup_two_cells.mjs#L534)

## 交接与停止点

下一轮仍由 Hydrogen 维护双格运行器及其无内核依赖回归。以表中成对输入修正判定，并复测部分建组回收；保留已通过的五组。准入条件为：正常样例继续通过，两个负格反例及正格超时样例都被拒绝，失败记录中的分类、计量和清理结果一致。通过后再向可写委派 cgroup v2 的 Linux 宿主交付冻结版本，按 p042、p090 各一次采集。此次没有修改实现、提交代码或使用真实 Linux 两格及 16 题长跑额度。
