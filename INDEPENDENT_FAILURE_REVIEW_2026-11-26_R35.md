# R35 独立复审｜双格运行器可转入 Linux 实测

**裁决：关闭 R34 的 2 项 P1 和 2 项 P2，接受当前候选用于真实 Linux 双格采证。** 独立复跑版本化逻辑套件 **6/6 通过**。另外验证了一个容易漏掉的边界：当显示用的毫秒数仍是 10,000 时，准确耗时只多 1 纳秒，两格都会拒绝通过。现在需要的是 Linux 现场的两份原始记录。600 秒、2 GB 下的题库成绩仍待测量。[R34 验收卡](./INDEPENDENT_FAILURE_REVIEW_2026-11-26_R34.md)

## 四项关闭依据

| R34 问题 | 本轮复核结论 |
|---|---|
| P1 正负格组外截止 | 默认启动路径从单调钟取得原始纳秒差值，并传到两格共用的判定函数。定时回调尚未触发时，实测耗时越界也会失败。有 OOM 的超时负格同时保留内核事件和超时原因。[时间采集](./scripts/verify_linux_cgroup_two_cells.mjs#L765) · [共用判定](./scripts/verify_linux_cgroup_two_cells.mjs#L415) |
| P1 排空缺测误报 | 快照与默认排空路径共用读取函数。独立输入空 PID 列表但缺少 `cgroup.events`，得到 `ok=false, populated=null, drainedEmpty=false`；只补上 `populated 0`，默认排空函数即确认空组。末快照判定也要求合法空列表及显式零。[排空读取](./scripts/verify_linux_cgroup_two_cells.mjs#L191) · [末快照判定](./scripts/verify_linux_cgroup_two_cells.mjs#L472) |
| P2 部分建组后的清理 | 默认路径在目录创建成功后、写入限额前登记所有权。第 6 组注入配置失败，验证本次创建的空目录已删除并留有失败记录；已有目录触发 EEXIST 时，哨兵文件内容完整。[所有权登记](./scripts/verify_linux_cgroup_two_cells.mjs#L1013) · [成对测试](./scripts/verify_linux_two_cells_logic.mjs#L784) |
| P2 失败分类仍显示 PASS | 同一 OOM kill 增量在预算内通过，超时后返回 `FAIL_OUTER_TIMEOUT_WITH_KERNEL_EVENT`；排空证据不足则返回失败分类。`kernelIntervention` 独立保留事件类型。[分类逻辑](./scripts/verify_linux_cgroup_two_cells.mjs#L670) |

### 独立纳秒边界检查

直接调用公开正格和负格判定函数。固定其余证据、10,000 ms 上限、显示耗时 10,000 ms，并令超时与主动终止标志都为 false。负格固定带有效的合成 OOM kill 增量。下表为夹具输入与实测函数输出。

| 原始耗时 | p042 型正格 | p090 型负格 |
|---:|---|---|
| 9,999,999,999 ns | PASS | PASS，保留 OOM kill |
| 10,000,000,000 ns | PASS | PASS，保留 OOM kill |
| 10,000,000,001 ns | FAIL，耗时越限 | FAIL，耗时越限，保留 OOM kill |

## 候选身份与验证边界

| 对象 | 本机核对值 |
|---|---|
| HEAD | `cdf8979d880bc7805e2de8517eb2881acbc5cfad` |
| 五文件 C++ 补丁 SHA-256 | `73ca6875456a0ab899e439d1b4f866bc234ca5fd03cb6dd7a7c33e7921d9c03b` |
| 监督器 / 监督器回归套件 SHA-256 | `827dc867c0f6f9870812c07ccdcfd39e2c0c837fd61bc969cfd4bc6ccdbf3821` / `25fa573bfcc91dad0bb0f654aad93e450eba9a37527e0546f0feb7522b2ff918` |
| 双格运行器 SHA-256 | `078134cdac10ce74d6f67c3c6bcf4b2cc2fd8162583614fbf2069f1a50aa542e` |
| 无内核逻辑套件 SHA-256 | `264d5bbff18da25b25daab0e49dfce0ff8c050594feb63d5d6dbf8e835208d42` |

本机为 Darwin 25.6.0 arm64。已查阅实现方原始输出并独立重跑本轮有改动的套件；冻结的 C++ 构建和监督器 12 组回归未重复运行。本机 Docker 服务只读查询无法连接，真实 Linux 两格均为 **NOT RUN**。本轮仅新增本报告，未提交代码或启动正式扫描。[实现方原始日志](</Users/go4ai/.gemini/antigravity/brain/409858d5-d8bb-46a6-96b1-acd16ced4db3/.system_generated/steps/2354/output.txt>)

## 唯一下一步

由 Hydrogen 在具备可写委派 cgroup v2 的 Linux 宿主核对上述候选，使用新的持久输出目录。保持默认参数，p042 正格 256 MiB、p090 负格 64 MiB、零 swap、每格组外工作窗口最多 10 秒，各一次。归档 manifest、两个 outer record、summary，以及正格的证明和回执。p042 要有原题 `original_root` 独立读回 PASS；p090 按预登记的 `oom_or_oom_kill` 目标检验同组事件增量。若只出现求解器软停，记录“未观察到目标内核事件”，当次到此结束。Astra 按实际产物复核后再裁定 Arm D 基线。16 题长跑另行决定。[默认配置](./scripts/verify_linux_cgroup_two_cells.mjs#L30) · [运行清单](./scripts/verify_linux_cgroup_two_cells.mjs#L1193)
