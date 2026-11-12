# LDProver 开发需求说明书

**版本**：v1.8（依据《LDProver设计说明文档》v1.9；联合审核裁定同步，2026-09-12）
**项目代号**：LDProver（Life-and-Death Prover，C++ 围棋死活精确求解器）
**文档性质**：需求规格说明（SRS）。本文档是设计文档的需求侧投影：**每条需求均可追溯到设计文档章节与验收测试，凡设计文档未定义的能力不进入本文档的需求集合**（列为 Won't/实验阶段/V2 登记）。

2026-10-18执行同步：新增§4.3说明独立阶段成果报告及G1研究边界，设计对应§13.4～13.5；不修改现有FR/NFR、NFR-6a原七题@10k门、规则/checker或机读验收状态，不授予运行预算。

---

## 0. 版本变更记录

### v1.7 → v1.8（联合审核裁定同步）

- 纠正前沿 PN/DN、SAT、TT 截断、KoDependent、历史快照、provider 和拓宽触发的契约/实现混用；不以 Benson 失败推出被杀，不豁免历史重放。
- 新增 FR-6.9 可发布闭包复用、FR-7.8 确定性/性能模式及 NFR-12 复用成本验证；与任务分解 v1.4 的 `REV19-T01`～`REV19-T09` 联动。
- M3 功能前置与 NFR-6a 性能门显式分开，既有 M9 功能/安全 passed、V1 总体验收 blocked 不变。新增要求为待开发/待验收，不凭文档修订宣告代码完成；具体状态见 §4.2。

### v1.6 → v1.7（M9 功能轨固化与产物/预算契约同步）

- 将 M9 功能/安全验证与 V1 总体验收拆为两个联动轨道：前者已通过外部复审，后者继续受 M3/NFR-6a 阻塞；功能轨通过不得改写总体验收状态。
- manifest 引导阶段的文件读取和 JSON DOM 解析均使用调用配置预算；清单成功加载后才以清单预算形成逐题有效配置。
- `result_<problem>.json` 明确纳入 `ArtifactsComplete/SgfFile/SgfChecksum`，续跑要求 proof/SGF 规范文件名、摘要和语义校验全部匹配。
- SGF 作为必交付显示产物，其 DAG 展开按输出字节、工作步数和 pending 栈三维预算在增长前计费；失败保留有效证明结论但返回产物交付失败。

### v1.5 → v1.6（M9 代码审计整改回写）

- FR-3.2/FR-9.2 澄清终局重放：目标定论不是任意后继状态的不变量；双 pass 严格禁止继续。
- FR-1.5/FR-8.1/FR-9.1 固化完整结果、原题 trace、配置 Ruleset、证明语义及 PN/DN 绑定。
- FR-5.7/FR-9.2 补查询 provenance 的 KoDependent 检查；NFR-5 覆盖解析和 checker 预算与失败口径。
- FR-10.3/NFR-11 补 candidateSet、可持久化基准摘要及分母；验收条款见新增 §4.1 和任务基线 v1.2。
- 本次不调整 NFR-6a，也不据整改测试通过宣告 M9/V1 通过。历史修订记录保留，现行规则以本版正文为准。

### v1.4 → v1.5（响应《设计审核by- GeminiSpark》复核结论）

| # | 修订内容 | 来源与裁定 |
|---|---|---|
| 1 | FR-5.2 明确征子/长程逃逸的实际证明依赖必须进入通用 RZ 回传；固定 ±45° 射线及未经 checker 重算的征子分析只能作 attention/排序启发 | 第三方意见 1，部分采纳 |
| 2 | 实验边界明确历史无关静态条件仅可预筛，不足以豁免 PatternTT 完整历史相等或 QueryState 重放 | 第三方意见 2，不采纳豁免结论 |
| 3 | 新增 FR-3.9：固化 `allow_ko`、外部劫材、双 pass 与传统劫活/劫杀标签的结果语义 | 第三方意见 3，采纳 |
| 4 | 新增 FR-4.10：FastCapture 仅作为确定性着法排序，不得改变合法着法集、PN/DN、终局或证书 | 第三方意见 4，采纳 |

### v1.3 → v1.4（响应第四轮复审）

| # | 修订内容 | 来源 |
|---|---|---|
| 1 | FR-5.5：RZ 外仅作为剪枝候选；在 SSK/PSK 下必须以被剪枝着法执行后的完整 `State + HistorySet` 重放源证明并全部通过，才可生成 Pruned* 结论；禁止仅凭“着点在 RZ 外/局部投影相同”跨历史定论 | 复审 P0-1 |
| 2 | FR-5.7/FR-4.8：KoDependent 见证在 V1 形成 `UNKNOWN(ko_dependent)` 屏障，不进入 Win/Loss 聚合和证明 TT；删除“继续搜索其余着法后可判 Loss”的不完整语义 | 复审 P0-2 |
| 3 | FR-8.3/FR-9.2：`lproof/1` 增加 `rootNode/rootOutcome`、`stateTable/historyTable` 及每节点 `stateId`；ttHit/pruned 同时记录查询状态与来源状态，checker 必须从查询状态真实重放引用证明 | 复审 P0-3 |
| 4 | Proof checksum 采用 RFC 8785 JCS；修正设计版本、LikePass 残留、历史集合措辞、PSK 比较口径及测试项数量 | 复审一致性 |

### v1.2 → v1.3（响应第三轮复审）

| # | 修订内容 | 来源 |
|---|---|---|
| 1 | FR-2.2/FR-6.1/FR-6.3：历史元素由哈希改为**规范局面**（黑白位图+toPlay），SSK/PSK 判重与历史集合相等在哈希索引命中后必须全量比较；FR-6.3 补 `consecutivePasses` 与历史句柄为 PatternTT 实际字段 | 复审 P0-1 |
| 2 | FR-5.7：KoDependent 由"按 LOSS 处理"改为**见证抑制**（不产生 Win、继续搜索；仅全覆盖证伪后才可 LOSS）；FR-3.2 补多组 AND/OR 三值聚合规则 | 复审 P0-2 |
| 3 | FR-5.5：删除 LikePassSelfAtari 硬剪枝触发（唯一触发=失败着 ∉ 证书 RZ），类 pass 条件降为排序启发并登记 §9 | 复审 P0-3 |
| 4 | FR-8.3/FR-9.2：证明文件按 §10.4.1 schema `lproof/1`（magic/版本/节点类型/稳定 ID 与拓扑约束/HistorySet·RZTable·PrunedCertificate 序列化/命中等价证据/规范字段顺序与 SHA-256 checksum 范围）交付与校验 | 复审 P0-4 |
| 5 | FR-1.5：跳过已有结果前须校验输入哈希、配置指纹、求解器版本与既有 ProofChecksum 一致；NFR-4：确定性测试使用固定节点预算并禁用时间限制 | 复审一致性 |
| 6 | 引用版本统一为设计 v1.4 | 复审一致性 |

### v1.1 → v1.2（响应第二轮复审）

| # | 修订内容 | 来源 |
|---|---|---|
| 1 | FR-6.1：BoardTT 命中在 SSK/PSK 模式下要求**完整历史局面集合相等**（仅比较当前一步禁着集不足）；FR-6.3：PatternTT 改两级命中（证明复用级须完整历史相等；启发级仅排序不得定论） | 复审 P0-1 |
| 2 | FR-2.4/FR-6.1/FR-6.3：`consecutivePasses` 进入状态与 TT 等价条件；FR-3.4 补"双 pass 终局判定先于 InPath"；FR-1.2 改为冲突默认拒题、禁止插 pass 校正 | 复审 P0-2 |
| 3 | FR-3.2 重写：统一四值终局接口 `evaluateTerminal()`，正向/负向叶均不可逆；**删除"眼位被 UCA 包围"KILL 判据**（新增 FR-3.7 禁止条款，实验准入） | 复审 P0-3 |
| 4 | FR-6.1/FR-6.3：已证条目携带稳定 `proofDagNodeId`；FR-8.3/FR-9.2：证明文件传递性包含全部 TT 来源（闭包）且头部保存完整规范化 ProofContext，checker 校验闭包 | 复审 P0-4 |
| 5 | FR-6.8 删除"证书失效联动"残留表述（证书自包含，GC 不牵连）；NFR-4 确定性范围限定为语义字段与证明 DAG（Time 等物理计量除外） | 复审 P1 |
| 6 | C-2 明确 V1 唯一验收规则组合（PSK/off 为内部实验开关）；C-7 引擎核心模板化小棋盘供穷举测试 | 复审 P1 |
| 7 | §1.2 补参考文件来源声明（本仓库缺位文件标注外部来源/交付阶段）；§8 追踪矩阵补 NFR-11；变更记录移除日期标注 | 复审 P2 |

### v1.0 → v1.1（响应《requirements与LDProver设计说明文档_审核意见_by_codex.md》）

| # | 修订内容 | 来源 |
|---|---|---|
| 1 | 新增 FR-2.6 目标令牌维护；FR-3.2 谓词改以令牌为单位并显式"不输出 DEAD/ALIVE 领域标签" | P0-3 / P0-8 |
| 2 | FR-6.1/FR-6.3 命中比较增加 **SSK 禁着集全等**与存活令牌投影（同盘同轮走方不同历史不得复用）；删除无限定表述"哈希碰撞只损失性能" | P0-6 |
| 3 | 新增约束 C-6：context_id 统一 `uint64_t`，指纹仅定位/快筛，命中后结构化全量比较 | P0-7 |
| 4 | FR-4.7 深度上限改为工程护栏（删除"2×盘面点数"数学断言）；FR-4.8 UnknownReason 枚举扩展（depth_limit/cycle/internal_error） | P1-1 / P1-2 |
| 5 | FR-5.6 改为证书自包含（TT GC 不牵连证书及派生结论） | P1-3 |
| 6 | NFR-1 强化"任何 PROVEN_* 必须附 proof DAG 且通过 checker"，并固化四不变量；NFR-5 增加默认内存预算 512MB；新增 NFR-11 benchmark_manifest | P2-10 / P1-4 |
| 7 | §9 边界登记扩充 V2 残留项：9/13 路、多规则集（TT/中国/日本）、Python API/多包、进度回调/ETA、完整 SGF 往返、可视化、多解分析、在线微调、Seki 数据库、KoProcessor/劫材预测、LadderEngine、MPR、18 通道特征 | P0-1 / P0-2 / P1-5 / P1-7 |
| 8 | §7 里程碑对齐设计 v1.2 的 M0–M9（历史安全 BoardTT 前置、RZ 排序与证书剪枝分离） | 审核第四步 |

### 基线声明（P0-1/P0-2 闭环）

v1.0 起本文档即与设计文档同基线（C++20 / 19 路 / CLI + JSON/SGF/Proof DAG / 单仓模块）；历史上并存过的 Smargo 增强型需求（Python 多包、9/13/19 路、多规则集等）**不属于本项目 V1 基线**，相关条目已在 §9 登记为 V2/实验边界。

---

## 1. 引言

### 1.1 目的

定义 LDProver V1 必须交付的功能需求、非功能需求、约束与验收标准，作为开发、测试与验收的依据；并通过需求追踪矩阵（§8）与《LDProver设计说明文档》v1.9（下称“设计文档”）及评审意见的裁定结论保持一致。

### 1.2 参考文档

| 文档 | 用途与来源声明 |
|---|---|
| `docs/LDProver设计说明文档.md`（v1.9） | 唯一设计依据，本文档全部需求的追溯目标 |
| `docs/LDProver设计说明文档_论文与实现交叉审核_2026-09-11.md`、`docs/LDProver设计文档_Gemini意见复核与联合审核_2026-09-11.md` | 本轮裁定依据；包括对 Gemini 报告的逐项采纳/不采纳，不以第三方评级直接替代规范 |
| `docs/LDProver设计说明文档_评审_by codex.md`、`docs/设计评审by Google Gemini.md` | 第一轮设计评审（已裁定落实） |
| `docs/requirements与LDProver设计说明文档_审核意见_by_codex.md` | 第二轮审核及其复审结论（v1.1–v1.2 修订依据） |
| `docs/围棋AI死活题研究进展.pdf` | 技术路线背景（不构成正确性依据） |
| `docs/设计说明文档.md`、`docs/实现分析文档.md` | 旧库（study-LD-RZ）语义参考与反面工程约束来源；源自 `study-LD-RZ-main` 仓库（随文档同步副本） |
| `tsumego/*.json`（117 题）、`candidate.list` | 输入数据集与回归基准；源自 `study-LD-RZ-main` 仓库（随文档同步副本） |
| `cfg/default.conf` | 已存在的默认配置；实际键以 ConfigRegistry 为准，新模式/指标须实现注册与契约测试后才可使用 |

### 1.3 术语

沿用设计文档附录术语表（RZ/ProofCertificateRZ、df-pn、PN/DN、UnexpandedCost、UCA/Benson、GHI、SSK/PSK、null move、KoDependent、ProofContext/context_id、soundness/completeness、NNAttentionMask/ProblemSearchMask 等）。

### 1.4 需求优先级与状态约定

- **Must**：V1 必须实现，缺失即验收不通过。
- **Should**：V1 应实现，允许在资源受限时延后，但须在验收报告中说明。
- **Could**：V1 可选增强，实现与否不影响验收。
- **Won't（V1）/实验阶段**：明确不在 V1 范围，准入条件见设计文档 §13.2；本文档仅登记边界，不定义需求。

优先级表示目标义务，不表示完成状态。新增 FR-6.9/FR-7.8/NFR-12 及 §4.2 的补证项均待实施，已有 Gate 证据仍按其原版本保存；新要求的实现完成需独立复审记录，不得直接把当前 ledger 改为失败或通过。

---

## 2. 产品概述

### 2.1 定位

LDProver 是一个 C++ 实现的围棋死活题（tsumego）**精确求解器**：以 df-pn（深度优先证明数搜索）在 AND/OR 树上给出严格的逻辑证明，辅以可选神经网络直觉导航；不是通用对弈引擎，不做全局胜率或目数优化。

### 2.2 用户与使用场景

- 研究者/开发者：批量求解死活题集、复现实验、分析 RZ 与证明树。
- 集成方：通过 CLI 与 JSON/SGF/proof DAG 输出对接下游工具（SGF 查看器、证明校验流水线）。

### 2.3 运行环境

- 桌面/服务器 Windows、Linux、macOS；无 GPU 也可完整运行（NN 为可选组件）。
- 依赖约束：CMake ≥ 3.16、C++20 编译器、标准库 + 线程库；NN 为可选 C ABI provider，真实 ONNX Runtime 由外部适配器提供，不能把测试 provider 当作模型效果验收（NFR-3）。

---

## 3. 功能需求（FR）

需求编号规则：`FR-<模块>.<序号>`；"来源"列指向设计文档章节（及评审条目）。每条 Must 需求的验收方式见 §7 与 §8。

### FR-1 题目输入与解析

| 编号 | 需求 | 优先级 | 来源 |
|---|---|---|---|
| FR-1.1 | 按 `tsumego/*.json` 契约解析题目：`masked_sgf_str`、`winning_color`、双方 `search_goal` 与 `crucial_stone` 为必需；`turn_color`、双方 `ko_rule`、`region` 为可选；`filename/category/rawsgf/answer_firstmove/mask_*` 等为忽略的元数据 | Must | §10.2 |
| FR-1.2 | 轮走方以 SGF `PL` 为准；`turn_color` 仅作交叉校验，不一致时**默认拒题**（配置 `turn_conflict_policy=warn_ignore` 可放宽为以 PL 为准、忽略冲突元数据并告警）；**禁止以插入 pass 校正**（会修改历史、劫状态与双 pass 终局语义） | Must | §10.2（复审 P0-2） |
| FR-1.3 | 解析失败必须拒题并输出结构化错误（必需字段缺失、非法坐标、未知 `ko_rule`/`search_goal` 枚举、`crucial_stone` 表达式内混用 `&` 与 `|`），**禁止静默使用默认值**；空关键子串按"该方目标恒假"处理并告警 | Must | §10.2 |
| FR-1.4 | 支持单题与批量模式：`--problem <file>` / `--dir <dir> --filter <list>`；批量遍历顺序确定（路径排序），保证可复现 | Must | §10.1、G5 |
| FR-1.5 | 批量模式可跳过已有结果文件，但必须先验证完整字段/类型/数值域、输入哈希、配置指纹、版本和规则一致；PROVEN 还须绑定真实原题 trace 与完整上下文，核对 ProofChecksum 并通过语义 checker。缺字段、超限、损坏或不一致即重算，internal_error 永不跳过；日志记录跳过/重算原因 | Should | 设计 §10.3～10.4，本文 §4.1 |

### FR-2 棋盘与规则引擎

| 编号 | 需求 | 优先级 | 来源 |
|---|---|---|---|
| FR-2.1 | 19×19 固定棋盘；落子合法性判定：占位、禁自杀、简单劫禁着 | Must | §4.1、§6.2 |
| FR-2.2 | 局面重复层默认 situational superko（SSK）：落子后局面（含轮走方）不得与任何历史局面重复；判重与历史集合比较使用**规范局面**——SSK 比较黑白位图 + toPlay，PSK 仅比较黑白位图；哈希仅作索引，命中后必须全量比较；`positional`/`off` 为内部实验开关（C-2） | Must | §4.1、§6.2 |
| FR-2.3 | pass 始终合法；连续两次 pass 终止棋局并交由终局判定器评估 | Must | §4.1 |
| FR-2.4 | `play/undo` 增量维护棋块、气位图、Zobrist（**必须包含轮走方与劫点**）、历史哈希索引 + 规范历史局面集合，以及**连续 pass 计数（`consecutivePasses`）**，支持任意深度回滚 | Must | §6.2（复审 P0-1/P0-2） |
| FR-2.5 | 提供 `violatesSuperko(move)` 查询，供搜索着法生成与 SSK 处理使用 | Must | §6.2 |
| FR-2.6 | 目标令牌维护：题目加载时为每个初始关键子创建不可复活令牌；play/undo 增量维护 `surviving_target_tokens`（按令牌初始坐标编码的位图）；令牌所在棋子被提即永久移除，同坐标新子不得"复活"令牌 | Must | §4.6（P0-8） |

### FR-3 终局判定器（规则与图论预处理层）

| 编号 | 需求 | 优先级 | 来源 |
|---|---|---|---|
| FR-3.1 | 实现 Benson 无条件活（UCA）判定：DSU 双分量、vital 区域判定、迭代剔除至收敛 | Must | §8.1 |
| FR-3.2 | 统一终局接口 `evaluateTerminal() -> {Win, Loss, NonTerminal, Unsupported}`。TOLIVE 的 Win 叶为存活令牌块 Benson UCA、Loss 叶为目标令牌全被提走；TOKILL 对偶。令牌不可复活，但 Benson 当前成立不等于任意后续走子均保持活结构。组间 AND/OR 按三值聚合；双 pass 时表达式成立→Win，否则→Loss。冗余目标终局证明按 §4.1 重算方向并完整重放，双 pass 后不得继续。输出相对根命题的 ProofOutcome，不输出 DEAD/ALIVE/SEKI 标签 | Must | 设计 §4.3、§4.6、§8.1 |
| FR-3.3 | 终局判定器每次给出 Win/Loss 定论时，必须同时产出**可复验证据**（Benson 证据或令牌提除记录）与对应方向的叶证明 RZ（`ProofCertificateRZ`）；无证据或无 RZ 的定论不得进入回传 | Must | §8.1（Gemini 2.1 + 复审 P0-3） |
| FR-3.4 | 静态双活判定**不得接入** V1 终局判定器；最多输出 `SEKI_CANDIDATE` 诊断信息（不产生任何 `PROVEN_*`） | Must（以"禁止"形式） | §8.2（Codex P0-4.6 裁定） |
| FR-3.5 | 盘角曲四不做静态判定，一律由搜索在规则集（ko_rule + KoDependent）下处理 | Must（以"禁止"形式） | §8.2 |
| FR-3.6 | 双活正解题在 V1 的 UCA 目标下可能与棋书标签不同；域外题须运行前以版本化 manifest 登记分类/排除理由，不得按失败结果事后删题。既定 candidateSet 的 UNKNOWN/拒题保留在验收分母；不自动改写 NFR-6a | Should | §8.2 |
| FR-3.7 | KILL"包围判据"（目标块眼位空间被对方 UCA 结构占据即判杀）**不得**作为 V1 终局——不充分（存在双活/外气反杀等反例空间）；仅可作排序启发；作为终局的准入条件见设计 §13.2（checker 可验证充分性证明 + 反例集） | Must（以"禁止"形式） | §8.1、§13.2（复审 P0-3） |
| FR-3.8 | 双 pass 终局判定（含其评估）必须先于 InPath 循环检测执行 | Must | §7.3（复审 P0-2） |
| FR-3.9 | 劫活/劫杀契约：`allow_ko` 仅取消该方的 KoDependent 见证限制，不授予外部劫材、不假定劫材数量/价值，也不把棋书标签直接映射为 `ProofOutcome`。求解仅使用输入棋盘、initialTrace/HistorySet、Ruleset 与真实合法着法；双 pass 时目标表达式未成立的分支按 Loss 处理，但不输出传统死活领域标签。劫题若纳入回归，manifest 必须固化规则、初始历史、根目标和本契约下的期望结果，否则仅登记为边界/诊断样本 | Must | §4.3、§8.1、§10.2（第三方意见 3） |

### FR-4 df-pn 求解核心

| 编号 | 需求 | 优先级 | 来源 |
|---|---|---|---|
| FR-4.1 | 当前前沿聚合：OR（min-PN / Σ-DN+U）、AND 对偶；U>0 时 min 侧必须包含隐式子值 1，`U=|A|−|S|`，P 已在 S 中不得重复计数。SAT 饱和不等于决定性状态，阈值减法钳 1。TT/PCN 正数值不能未经证明称为最终证明代价下界 | Must | §7.2～7.3 |
| FR-4.2 | 实现非对称定论条件：OR→Win 单见证、AND→Loss 单逃脱；OR→Loss 与 AND→Win 必须 `S = A` 全覆盖 | Must | §7.2（Codex P0-4.3） |
| FR-4.3 | OR/AND 对偶阈值递归、most-proving 与次优值均计入隐式子；任一阈值达到即截断（OR 条件）。Unknown 截断记录与决定性证明分开；TT Unknown 值恢复为一次性导航行为（v1.8：持久 floor 字段已按 REV19-T01 自然反例裁决移除）。R5 三臂独立评估已交付：5×5 双顺序及 p031+七题 60k 等预算中，1,040 次自然 Unknown 命中均未有效抬高当前值或触发额外截断，搜索/公平性字段一致；结论仅限受测范围，不外推为一般 no-op、完备性或公平性定理 | Must | §7.3 |
| FR-4.4 | 拓宽按 `K·2^ℓ` 单调升级；截断/无可下降子/重入防震荡/待补全/隐式最优子五类触发按设计 §7.4 校验，级别上限必须全展开 A；任何概率阈值不得永久删着。当前重入计数不等于工作量公平性保证 | Must | §7.4 |
| FR-4.5 | InPath 为保守循环护栏，粗哈希命中不等于完整状态/历史相同；按重复规则映射 internal_error/cycle，受污染调用不得写证明 TT 或以其数值定论。更精确键与推进论证见 REV19-T01 | Must | §7.5 |
| FR-4.6 | 并列最小值按稳定生成顺序破平；同输入同配置的强确定性须满足 NFR-4/FR-7.8 前提，不能仅靠固定种子/节点预算排除 NN 墙钟反馈 | Must | §7.3、§9.5、G5 |
| FR-4.7 | 资源护栏：节点/时间/内存预算任一耗尽 → 优雅返回 `UNKNOWN(原因)`；拓宽升级次数上限（超限强制 ℓ_max）；递归深度上限为**可配置工程护栏**（非数学断言），触发返回 `UNKNOWN(depth_limit)` | Must | §7.6、G6 |
| FR-4.8 | 三值输出 `PROVEN_WIN/PROVEN_LOSS/UNKNOWN` 相对根命题；UNKNOWN 区分 timeout/node_limit/memory_budget/depth_limit/cycle/ko_dependent/internal_error。`widening_stalled` 仅保留枚举，当前无可达独立触发，不得以全局发生升级归因根阻塞 | Must | §4.4、§7.6、§10.3 |
| FR-4.9 | 1+ε 阈值松弛仅列实验：当前无 dfpn_epsilon 配置；须另定 min/次优阈值方向、整数/SAT 边界、推进论证与回归，不采用旧 sum 侧草图 | Won't（V1 当前基线） | §7.3、§13.2 |
| FR-4.10 | FastCapture 仅作稳定排序（提子、紧气、关键气、连接/逃逸阻断及防守对偶）；不改 A 或 S/P/U 定义、覆盖义务，不直接写语义 PN/DN/status/RZ/证书。实际 S/P/U、导航值和证明路径可变化；两边均已定论时不得相反，有限预算允许一边 UNKNOWN | Should | §7.4、§9.2 |

### FR-5 Relevance-Zone 机制（空间隔离层）

| 编号 | 需求 | 优先级 | 来源 |
|---|---|---|---|
| FR-5.1 | 三类区域类型隔离：`ProblemSearchMask`（仅显示/诊断）、`NNAttentionMask`（仅排序与特征输入）、`ProofCertificateRZ`（唯一允许参与剪枝候选筛选与 PatternTT 的区域类型，但其本身不足以产生 Pruned*，仍须 FR-5.5 重放）；类型系统禁止隐式转换，证书 RZ 只能由证明回传创建 | Must | §5.3、§8.4 |
| FR-5.2 | 证明方向 RZ 回传：证明方着法侧影响闭包（相交才扩展、补气闭包、多块公共气）；对手方着法侧子 RZ 并集 + 三重安全闭包（自杀/对手边界可配/合法化）。征子、长气逃逸、引征与接应必须逐层经过同一通用规则；凡 Influence 相交或提子、气、劫/超级劫合法性成为证明依赖即并入 RZ，无关着法仍按不相交规则处理。固定 ±45° 射线不得充当充分或必要闭包。可选长程包络只许集合并，且仅在 checker 可重算时进入 ProofCertificateRZ，否则只能进入 NNAttentionMask/排序 | Must | §8.3-A/B（第三方意见 1，部分采纳） |
| FR-5.3 | 反证明方向对偶回传：OR 被证伪取子 disproofRZ 并集 + 防守方闭包；AND 被证伪取逃脱手影响闭包 | Must | §8.3-A'/B'（Gemini 2.2） |
| FR-5.4 | proof/disproof 双链独立存储与更新（节点双 RZ 索引），互不覆盖；RZ 更新只做集合并（单调不减） | Must | §6.4、§8.3 |
| FR-5.5 | null-move 证书剪枝：`着点 ∉ 证书 RZ` **仅是候选条件，不是定论依据**。对每个候选着法，必须先执行得到查询子状态，并在其完整规范历史下重放代表性源证明；仅当每一步合法性（含简单劫/SSK/PSK）、终局证据、OR 见证、AND 完整合法应手集、目标令牌和 KoDependent 约束全部复验通过，方可物化 `Pruned*`。PrunedCertificate 必须包含 query/source `stateId/historyId`、源证明引用、证书 RZ、context_id、代表性着法与 `reason=OutsideRZRevalidated`；失败则正常展开，禁止仅凭局部投影相同跨历史定论。LikePassSelfAtari 仍仅为排序启发 | Must | §8.4（四轮复审 P0-1） |
| FR-5.6 | 证书在 proof artifact 内闭包自包含：有效性仅取决于证书字段及其引用的不可变 StateTable/HistoryTable/RZTable/sourceProof；这些对象生命周期与题同界且随证明传递性输出。TT/PatternTT 淘汰不得使证书或派生结论失效；origin* 字段仅作溯源诊断 | Must | §8.4、§10.4.1 |
| FR-5.7 | KoDependent 安全边界（§4.5）：受限方的取胜见证一旦携带该标记，在 V1 中将受影响状态记为非决定性 `UNKNOWN(ko_dependent)`；该见证不得折算为 Win 或 Loss、不得作为全覆盖证伪子、不得写入证明级 BoardTT/PatternTT（仅可进入诊断/排序缓存）。若其他独立分支足以按普通规则定论可继续定论；否则该 Unknown 传播至根。禁止由 KoDependent 直接或间接推出 LOSS | Must | §4.5（四轮复审 P0-2） |

### FR-6 置换与记忆层

| 编号 | 需求 | 优先级 | 来源 |
|---|---|---|---|
| FR-6.1 | BoardTT 哈希仅定位；全量比较黑白棋子、轮走、ko、令牌、pass、结构化 ProofContext 和完整历史集合。SSK 比 B/W/toPlay，PSK 比 B/W；None 在规则一致前提下不使用历史。决定性条目带稳定来源锚，发布恢复另须完整闭包；Unknown 导航记录不得视为已证状态 | Must | §8.5、§8.8 |
| FR-6.2 | TT 上下文隔离：所有条目携带 `proofContextId`；**每题开始清空 BoardTT 与 PatternTT**；V1 无跨题复用 | Must | §4.2 |
| FR-6.3 | PatternTT 用存储 zone 投影查询局面，比较黑白空/禁着/令牌与控制字段、完整 Ruleset/上下文/GHI；历史全等得到 ProofReuse 候选分类，不自动授权发布恢复，仍须 FR-6.9。历史不同/KoDependent 诊断只作排序提示，不得恢复 status/RZ/证明；稳定来源 ID 不替代闭包 | Must | §8.6、§8.8 |
| FR-6.4 | PatternTT 索引：radix 式热点层级树（≤20 关键点、80% 热度覆盖、四边含 wildcard）、自适应重构（首 1000 条每 100 条、其后 1.1 倍增长）、增量查询时间戳；节点池分块按需增长 | Must | §8.6 |
| FR-6.5 | 复用范围限定：V1 仅同坐标匹配；**不得**实现平移/旋转/镜像归一化复用（实验阶段准入另议） | Must（以"禁止"形式） | §8.6（Codex P1-5.3 vs Gemini 3.1 裁定） |
| FR-6.6 | GHI 命中后校验默认开启：ghiFlag 与当前路径祖先同 RZ pattern 比对，可疑拒绝并计数 `NumGhiRejected`；KoDependent 候选不得进入证明级命中，仅允许启发级查询 | Must | §8.7、§4.5 |
| FR-6.7 | SSK 扩展：PatternTT 存储前枚举 superko 非法着，影响与 z 相交则闭包并入 | Must | §8.7 |
| FR-6.8 | PatternTT 满容量按 lastTouchSeq 确定性 LRU 批量淘汰至低水位、压实并推进世代；世代变化清空节点查询水位。GC 不牵连有效证明闭包，污染 purge 须撤销对应来源，两者不同 | Should | §8.6 |
| FR-6.9 | **部分实现（BoardTT 主体）**：正式发布模式的决定性 TT 复用同时满足 Board/History/Rule/Goal 兼容及不可变 ProofClosureAvailable，预算内原子挂接完整闭包 DAG 视图后才可跳过重搜。缺失/撤销/重放失败回退重证或启发；PatternTT 查询态重放导入仍待 T03-C，完整历史门不豁免 | Must（后续义务仍开放） | §8.8，REV19-T03 |

### FR-7 神经引导（可选层）

| 编号 | 需求 | 优先级 | 来源 |
|---|---|---|---|
| FR-7.1 | 三级降级链 `nn=full / policy-only / off`；`off` 模式功能完整（仅速度不同） | Must | §9.1、G2 |
| FR-7.2 | 架构隔离：NN 模块**无** status/RZ/证书写权限；NN 输出仅进入排序与导航值初始化 | Must | §9.1、§11.1 |
| FR-7.3 | Policy 输入：12 通道 19×19 特征（通道 6 为 NNAttentionMask 语义——祖先证明 RZ 投影或全零，非证书）；特征构造采用位并行向量化实现 | Must（通道定义）/ Should（向量化） | §9.2 |
| FR-7.4 | PCN 仅排序/正数导航，逐子 cost 可用时初始化到 [1,10^6]，否则 (1,1)；不得作为语义 PN/DN 界或制造定论。正数护栏不证明无饥饿，自定义 Alive/Dead/Seki/Ko 标签不等于论文模型或证明结果 | Must | §9.3 |
| FR-7.5 | 模型版本化：`model_manifest.json`（feature_version、规则/目标编码、输入尺寸、输出含义与范围、校准方式、训练数据版本）；不兼容 manifest 拒绝加载 | Must | §9.1（Codex P2-6.2） |
| FR-7.6 | 深度/预算门控（默认 D_nn=6 或 PN+DN 阈值）与微批推理（8/16） | Should | §9.5（Gemini 4.1） |
| FR-7.7 | 性能模式记录 NNInferenceRatio，超过 70% 时调整深度门控；70% 是治理目标而非硬上界。确定性模式只观测时间，不以时间改变导航；当前 NN 墙钟门属于性能行为 | Should | §9.5、M8 准入 |
| FR-7.8 | **待实施**：显式隔离确定性/性能模式并纳入配置指纹、result 与续跑；确定性模式只用固定逻辑预算门控/批次，性能模式可用墙钟反馈且不承诺逐字节复现。前者还需确定模型/provider 输出；未交付前正式强确定性验收使用 nn=off | Must（本轮后续交付） | §9.5，REV19-T05 |

### FR-8 输出

| 编号 | 需求 | 优先级 | 来源 |
|---|---|---|---|
| FR-8.1 | `result_<problem>.json`：包含设计文档 §10.3 全部字段，尤其是用于断点续跑校验的 InputHash/ConfigFingerprint/SolverVersion，以及 RootStatus、UnknownReason、NumNodes/Time、TT/Pattern/GHI/循环/剪枝/拓宽/NN 统计、RZSizeAtRoot、ProofFile/ProofChecksum、ArtifactsComplete/SgfFile/SgfChecksum、ResourceExhausted | Must | §10.3 |
| FR-8.2 | `uct_tree_<problem>.sgf`：沿用旧库着色约定（绿=proof RZ、红=活方胜着、浅黄=disproof RZ、灰=剪枝着法）；节点注释含 PN/DN/status/拓宽级别/PCN 估值；解答树文件名元数据统一为 `.sgf`；共享 proof DAG 的树展开必须在输出字节、工作步数和 pending 栈三维预算下 fail-closed | Must | §10.5 |
| FR-8.3 | `proof_<problem>.json` 证明 DAG：按设计 §10.4.1 schema `lproof/1` 交付。文件必须包含输入哈希与规范 `initialTrace`、`initialState/rootNode/rootOutcome`、完整 ProofContext、`stateTable/historyTable/rzTable`、稳定后序节点 ID；checker 先重放 initialTrace 建立可信初始历史，每个非初始 State 再以可回溯的 `parentStateId + move` 来源链扩展，禁止不可达的伪造历史；每个节点携带 `stateId`，detached TT 源证明有独立且可达的状态锚点；ttHit/pruned 同时记录 query/source state/history，并允许 checker 从查询状态完整重放源证明；文件闭包含全部 TT 来源。checksum = 删除顶层 checksum 成员后按 RFC 8785 JCS 序列化所得字节的 SHA-256 | Must | §10.4、§10.4.1 |
| FR-8.4 | 根节点证明 RZ 随证明输出（供 SGF 着色与 RZ 分析） | Must | §10.5、G4 |

### FR-9 独立 Proof Checker

| 编号 | 需求 | 优先级 | 来源 |
|---|---|---|---|
| FR-9.1 | `tprover check --proof <file> [--problem <original.json>]` 不复用搜索代码；带原题时核对语义输入哈希、规范初始 trace、由原题与本次配置 Ruleset 解析的完整 ProofContext，不从证明反向取得预期规则。不带原题时仅验证内嵌 initialTrace/ProofContext 命题；checksum 不构成原题真实性凭据 | Must | 设计 §10.1、§10.4 |
| FR-9.2 | 校验内容：按 §10.4.1 解析并校验输入哈希与 JCS checksum；先重放 `initialTrace` 并与 `initialState` 对照，再按 State 来源链重放全部被引用状态，验证每个 HistorySet 精确等于父历史加当前规范局面；随后从 `rootNode` 校验简单劫/SSK/PSK、双 pass、令牌、Benson、三值聚合及 AND 完整应手集；对 pruned/ttHit 必须在查询 State/History 上重新播放完整源证明，不得只比较局部投影；校验证明闭包、后序引用和根结果一致性 | Must | §10.4、§10.4.1 |
| FR-9.3 | 输出 `PASS/FAIL` 及失败节点定位；CI 中每道 `PROVEN_*` 题必须通过 checker（G1a 验收路径） | Must | §10.4、§11.2 |

### FR-10 CLI 与配置

| 编号 | 需求 | 优先级 | 来源 |
|---|---|---|---|
| FR-10.1 | 子命令 `solve` / `bench` / `check`，参数与语义按设计文档 §10.1（含 `--mode board-tt|pattern-tt`、`--nn`、`--node-limit`、`--time-limit`、`--memory-budget`） | Must | §10.1 |
| FR-10.2 | 配置文件 `key=value` 与 CLI 参数同名互斥覆盖（CLI 优先），消除旧库 conf_file/conf_str 双轨混乱 | Must | §10.1 |
| FR-10.3 | `bench` 输出批量 CSV；manifest 模式按 candidateSet 顺序执行，problems 为完整题库登记。指定 --out 时同时持久化 .summary.json，含 manifest/配置摘要、环境、重复次数、分母、分位数和 CSV checksum；summary 发布失败非零退出 | Must | 设计 §10.1，NFR-11 |

---

## 4. 非功能需求（NFR）

| 编号 | 需求 | 优先级 | 来源 | 验收方式 |
|---|---|---|---|---|
| NFR-1 正确性-可靠性（soundness） | 任何输出的 `PROVEN_WIN/PROVEN_LOSS` **必须附带 proof DAG 且全部通过独立 proof checker**；定论只能来自终局判定/全覆盖聚合/有效证书三类来源；启发式、置信度、NN 输出或低置信库命中只能影响搜索顺序（审核四不变量之四） | Must | G1a、§4.4（二轮 P2-10） | CI：全部 PROVEN 题过 checker（FR-9.3） |
| NFR-2 正确性-相对完备性 | 5×5/7×7 受限域与穷举 oracle 对照，资源不足只给 UNKNOWN，不得误报。有限状态与正数估计不自动保证终止；一般推进/TT floor/公平性由 REV19-T01/T08 补证，cycle/KoDependent 屏障不在必定求解承诺内 | Must | G1b、§4.4、§11.2-3 | 所测域对照与反例；不以测试外推通用定理 |
| NFR-3 构建与移植 | CMake ≥ 3.16 + C++20；Windows/Linux/macOS 构建；无 GPU/Caffe2 强依赖。当前可选 NN 为生产 ABI v2 provider（init/infer/infer_batch/memory_bytes 与 ABI 版本门）；缺失、初始化失败或零内存上报即拒载降级。外部 ORT 适配器单列验证 | Must | G3、§9.1 | 三平台接口/敌意 provider 测试；真实模型证据另列 |
| NFR-4 可复现性 | 确定性模式固定输入、配置、种子、逻辑节点预算及模型/provider 输出条件，禁用时间截止和墙钟反馈；比较语义统计、proof/SGF 字节，排除物理计量。性能模式不作强确定性承诺；FR-7.8 交付前正式对照使用 nn=off | Must | G5、§9.5、FR-4.6/FR-7.8 | 固定逻辑预算及注入延迟对照，不只关闭 timeout |
| NFR-5 资源与健壮性 | 默认内存预算 512MB、--memory-budget 可配置；搜索池、TT/RZ、输入读取、JSON 和语义验证均受相应预算约束。搜索耗尽返回 UNKNOWN；独立 checker 超限 FAIL/非零退出；续跑超限不跳过。失败路径不得伪报成功或崩溃，具体限额及失败语义见 §4.1 | Must | G6、设计 §6.5/§8.6/§10.3.1 | 搜索与 checker 内存/工作量压力测试 |
| NFR-6 性能 | （a）原 M3-P 卡口不变：七题 @10k，TT/RZ/NN/拓宽及 M5 排序均关闭；诊断 pin /8 不等于达标，论文也未保证此姿态收敛。（b）NN 同题对照 ≥10× 仅为观测目标，不作理论保证。（c）性能模式 70% 占比治理，超标记录降级 | Must（a）/ Should（b,c） | G2、§9.5、§13.1 | 原基线与全栈加速实验分开报告，不互相顶替 |
| NFR-7 数据兼容 | 117 题 `tsumego/*.json` 全部按 §10.2 契约完成解析（含拒题统计报告）；SGF 输出兼容旧库专用 viewer 的着色约定 | Must | G4 | 解析报告 + viewer 人工抽查 |
| NFR-8 可观测性 | 运行统计全量落盘：TT/Pattern 命中、GHI 拒绝、循环检测、证书剪枝、拓宽升级、NN 调用与占比、RZ 大小分布；拒题与告警结构化输出 | Must | G5、§10.3 | 结果 JSON 字段断言 |
| NFR-9 可测试性 | §11.2 十二类测试（含历史碰撞、未来合法性发散、KoDependent、劫题契约、长程征子依赖、FastCapture 等价性与 detached proof 状态锚点专项）全部可自动化执行并有明确通过判据 | Must | §11.2 | CI 测试套件 |
| NFR-10 可维护性 | 模块边界按 §5.2 目录结构落地；NN 模块与证明模块物理隔离（NN 头文件不得包含证明类型定义，静态断言约束）；配置项集中注册并带说明 | Should | §5.2/§5.3、§9.1 | 架构约束检查（脚本/CI） |
| NFR-11 基准可复验 | 性能与覆盖率类验收基准以版本化 `benchmark_manifest` 为准：题目 ID 清单与数据版本、规则集与先行方、期望结论、单题节点/时间/内存预算、UNKNOWN 与拒题分母口径、硬件与软件版本、重复次数与 P50/P95 分位数；Soundness 验收以独立 checker、穷举基准与反例集为主，**不依赖题库标签** | Must | §11.2-11（二轮 P1-4） | manifest 版本化 + CI 基准脚本 |
| NFR-12 复用成本可验证 | **待实施**：分表统计 Hit/Accepted/ProofReusable/SearchSkipped，按查询事件计数，分母为零给 null；原因可追溯。端到端搜索、重放、导入/导出、序列化、checker、SGF/I/O 分阶段计时且不重复加总；避免展开数仅作开关对照估计，不以源 DAG 大小冒充实测节省 | Must（本轮后续交付） | §8.8、§10.3.2 | REV19-T04/T09；真实发布链非空复用、字段与分母测试 |

---

### 4.1 M9 审计验收补充（现行规范，关联 FR/NFR）

以下补充与原编号共同构成验收条件，不替代或降低原有 Must 要求：

- **NFR-5/NFR-11**：manifest 加载后，其预算统一作用于题目读取/解析、搜索及证明重载/语义校验，summary 指纹反映有效配置；加载前的清单文件读取与 JSON DOM 解析使用调用配置预算，成功解析后才可采用清单覆盖预算。
- **FR-1.5/FR-8.1/FR-8.2**：SGF 发布失败保留有效证明及 PROVEN，但 `ArtifactsComplete=false` 且 solve 返回 2；成功时记录 `ArtifactsComplete=true`、`SgfFile/SgfChecksum`。续跑要求 `ProofFile=proof_<problem>.json`、`SgfFile=uct_tree_<problem>.sgf`，并对缺失、改名、损坏或缺少完整性字段的产物重新求解生成，不得静默跳过。显示产物失败不改写棋局结论。SGF 展开预算由有效 `memory_budget` 派生，对输出字节、工作步数和 pending 栈在增长前计费。

- **FR-3.2、FR-9.2**：终局方向必须在实际重放状态重新计算；目标已定论的冗余非叶可保留，但方向必须一致且完整重放。Unsupported 不得继续。双 pass 依据 atDoublePass 而非主证据类型判断；即使主证据为 Benson/提子/空目标，也拒绝后继 provenance 和非叶继续，允许有效终局叶。
- **FR-5.7、FR-9.2**：对每个决定性节点检查其 query provenance 的受限胜方提劫见证，包含 detached、ttHit、pruned；source 复验和后缀重放不能代替查询前缀检查。问题定义的 initialTrace 不自动视为搜索见证。
- **FR-8.1、FR-9.2**：proof 所有节点的 Win/PrunedWin 对应 (0,"SAT")，Loss/PrunedLoss 对应 ("SAT",0)，不符为 LP-N15。result 的 SAT 使用数值 1073741823；PROVEN 的 RootPn/RootDn 同向绑定、UnknownReason=null、ResourceExhausted=false。BestMove 使用 SGF 两字符坐标/pass/null；Time 秒、TimeMs 毫秒。字段全集与设计所指生产 writer 保持同步，新增字段须有契约测试。
- **FR-1.5、NFR-5**：结果和证明读取、JSON 分配、语义内存/工作量/重放深度均受限。独立 checker 超限为 FAIL/非零退出（语义错误 LP-S01、退出码 2），不得输出棋局 Loss；续跑校验超限为不可跳过；搜索资源耗尽为 UNKNOWN。具体阶段限额见设计预算小节，不将预算等同精确 RSS 上界。
- **NFR-11**：题库登记不等于执行集；总运行分母为 candidateSet×重复次数，UNKNOWN/拒题保留其中，耗时分位数仅以 decisive-runs 为分母。消费者校验 summary 的 csvChecksum；manifest 验收中 UNKNOWN/拒题/期望不符均使命令非零退出。117 题回归与七题性能基准分开报告。
- **状态边界（双轨）**：M9 功能/安全轨（T01～T08 及审计整改）已通过外部复审；M9/V1 总体验收轨仍因 M3/NFR-6a blocked。功能轨通过不得把 `acceptancePassed` 改为 true，也不得替代 M3 性能要求；当前状态由 benchmarks 下状态文件和验收报告联动记录，需求表保留最终目标要求。

### 4.2 联合审核的现状与增量验收边界（v1.8）

| 项目 | 当前事实/约束 | 本轮后续验收（均未由本次文档修改完成） |
|---|---|---|
| 目标与 ko | 非 Benson 不等于 Dead；V1 restricted 胜方成劫抑制不以 RZ 相交为前提，须检查 query 前缀 | REV19-T02：UCA/提子/双 pass 目标真值表、RZ 外成劫及仅历史导致失败的隔离控制组 |
| PN/TT | 隐式子取 1；截断条件为 OR；当前 ttPnFloor/ttDnFloor 为实现策略，不自动享有永久下界证明 | REV19-T01：可执行小树规范、SAT/阈值/访问顺序/TT 对照与推进论证 |
| 发布复用 | requireProofClosure 下 BoardTT 可导入经验证的驻留闭包；失败仍重证，PatternTT 仍降为提示；单独锚点不是闭包 | FR-6.9，REV19-T03/T04：BoardTT 主体 macOS 验证；PatternTT、跨平台新改动复验与完整成本漏斗仍开放 |
| NN | 当前墙钟门可改变搜索；C ABI 接口安全不等于真实 ORT/PCN 效果 | FR-7.8，REV19-T05：模式版本化、延迟注入确定性、目标/规则适用域与模型证据 |
| 历史与资源 | 增量指纹/部分 O(1) bytes 已有；并非所有历史已驻留共享，插入/登记仍可能线性或二次扫描 | REV19-T06：复制/比对/扫描计数与规模曲线；REV19-T07：跨阶段存活量预检，保留所有预算守卫 |
| checker 独立性 | 搜索决策独立，Position/Terminal/RZ 存在共享 TCB；JCS 哈希已有流式路径 | REV19-T02：独立原语/反例；REV19-T07：聚焦 DOM/证明/字符串共存峰值，不重复宣称新增流式哈希 |
| 拓宽与收益 | 重入阈值不是递归工作量额度，p031 depth=3 非全预算定理 | REV19-T08：参数化真实已知结论树和工作量实验；REV19-T09：原基线与加速姿态分报 |

新的字段/配置/序列化若需要schema或pin变更，由对应代码任务显式版本化并复审；v1.8当时的三份Markdown同步不代表代码交付。已有M4～M8/M9功能Gate保持历史范围，新契约完成另记，不自动使V1总体验收通过。

### 4.3 阶段成果报告与研究边界（2026-10-18，非新增验收门）

[ADR-003 B](./decisions/ADR-003-practical-solving-track-proposal.md)采纳独立阶段报告：冻结原题/规则/方向和批次姿态下，正确决定性结论+完整可交付证明+独立checker PASS计已解；UNKNOWN、深度/终局/激活计数及合同关闭不计已解。每批的题集/分母/资源须先固定，不能把未运行的成果轨报为0/117。此规则不替换NFR-6a、不改历史0/7，选项C的需求迁移仍须另裁。

当前[G1任务](./rev19_t08_g1_shallow_bound_task.md)只准备p088有界浅层下界/成本校准，不是已经证明门槛不可达。小下界不等于小证明或搜索可达，树界到实际访问须配置限定论证；正向策略仍欠完整checker链。棋盘运行资源包、七题扫描、新终局/启发及N2主测均未由本次文档同步放行。

## 5. 约束（C）与假设（A）

### 5.1 约束

| 编号 | 约束 | 来源 |
|---|---|---|
| C-1 | V1 单线程搜索（确定性优先）；并行 df-pn 列 V2 | §3.2、§13.2 |
| C-2 | 对外契约与验收基线固定 19×19 与**唯一默认规则组合**（禁自杀 + 简单劫 + SSK + 双 pass 终局）；`repetition = PSK/off` 等开关仅为引擎内部实验配置，其结果不进入验收基线；不引入规则集枚举之外的模式 | §4.1（复审 P1） |
| C-3 | 每题开始清空全部证明 TT（V1 无跨题复用） | §4.2 |
| C-4 | 旧库（study-LD-RZ）代码不直接复用；只迁移"已通过源码定位确认的语义"，并在新架构下重新测试 | §1、§2.3（Codex P1-5.1） |
| C-5 | 综述 PDF 不构成正确性依据；其建议中未通过评审裁定的（Top-K 永久剪枝、PCN 保证证明、静态双活/盘角曲四直接定论）不得进入实现 | §1（Codex 3.2 采信边界） |
| C-6 | `context_id` 统一 uint64_t，仅定位/快筛；命中必须结构化全量比较，每题清表也不能豁免此门。完整 Ruleset 同时绑定表、Position 与规范上下文 | §4.2、§8.8 |
| C-7 | 引擎核心（BitBoard/Position/df-pn/终局判定器）以模板参数支持 ≤19 任意尺寸，专供 5×5/7×7 穷举测试（§11.2-3）；NN 特征与对外 I/O 契约仍固定 19 路 | §4.1（复审 P1） |

### 5.2 假设

| 编号 | 假设 |
|---|---|
| A-1 | 输入题目均为"掩码后的完整 19 路题面"（`masked_sgf_str` 语义同旧库），题目本身数据错误由 FR-1.3 拒题兜底 |
| A-2 | 有限状态不能替代循环语义、阈值推进和公平调度证明；未完成补证前只声明所测域一致性与可靠性，不假定全题必终止 |
| A-3 | 模型/实际运行引擎由外部 provider 提供；三平台适配与模型校准须有真实证据，不能由 ABI 测试或官方包可用性推定 |
| A-4 | 双活等域外分类在运行前登记；既有 candidateSet 的解出率分母不因 UNKNOWN/拒题而减少 |

---

## 6. 外部接口需求

| 接口 | 方向 | 契约 |
|---|---|---|
| tsumego JSON | 输入 | §10.2 字段表（FR-1） |
| CLI | 用户 | §10.1（FR-10）；solve 正常结果（含资源 UNKNOWN）为 0，拒题/参数错误、必需产物交付失败或 check 失败为 2，内部异常为 3；manifest bench 验收未达标亦非零，不能套用 solve 的 UNKNOWN=0 口径 |
| result_*.json | 输出 | §10.3 字段全集（FR-8.1） |
| uct_tree_*.sgf | 输出 | §10.5 着色与注释约定（FR-8.2），兼容旧库 Windows viewer |
| proof_*.json | 输出/输入 | §10.4 证明 DAG 格式；同时是 `tprover check` 的输入（FR-8.3/FR-9） |
| model_manifest.json + onnx | 输入 | §9.1 版本化清单；不兼容即拒绝加载（FR-7.5） |

---

## 7. 验收标准（与里程碑绑定）

| 里程碑 | 验收内容 | 关联需求 | 准入条件（设计文档 §13.1，v1.2 重排） |
|---|---|---|---|
| M0 | 形式规则集、目标令牌、结果语义、证书/proof DAG 格式（含 root/state/history 锚点与 JCS checksum）固化为解析/序列化代码契约 + benchmark_manifest v1 | FR-4.8、FR-8.3、§4、§10.4.1、NFR-11 | 设计评审通过 |
| M1 | Position/着法生成/play-undo/Zobrist/令牌与历史维护 | FR-2.* | 性质测试通过（回放哈希一致） |
| M2 | Benson、目标谓词（令牌语义、四值终局接口）、JSON 契约解析 | FR-1.*、FR-3.1–3.9 | 独立终局测试 + 117 题解析报告 |
| M3-F / M3-P | 功能基线与 NFR-6a 性能门分开（概念标签，不改机读字段） | FR-4.1–4.8、NFR-6a | 功能为 M4+ 前置；原七题性能门独立阻塞 V1，不要求 M4 开发前解锁 |
| M4 | 历史安全 BoardTT（完整历史集合、令牌、连续 pass 全量比对 + proofDagNodeId） | FR-6.1–6.2 | 同盘异历史/异 pass 状态隔离 + 碰撞注入通过 |
| M5 | 启发式 RZ/FastCapture 排序（仅排序不剪枝） | FR-4.10、FR-5.1（排序语义） | 开关/逆序排序后逐局面结论一致 |
| M6 | 证书 RZ 双向回传（含长程战术实际依赖）+ 查询状态/历史下的源证明重放式 null-move 剪枝 | FR-3.3、FR-5.2–5.6 | 引征/长气逃逸与 SSK 历史发散反例不得误剪；静态历史快筛不得绕过重放；全部 Pruned* 可由 checker 在 QueryState 重放 |
| M7 | PatternTT、GHI 校验 | FR-6.3–6.7 | 历史/RZ/上下文隔离测试通过 |
| M8 | Policy + FastCapture 排序、拓宽、NN provider 与门控 | FR-4.4、FR-4.10、FR-7.* | 已有安全 Gate 保持；70% 为性能治理目标，新增双模式由 REV19-T05 另验 |
| M9 | proof DAG + checker + 回归基线 | FR-8.*、FR-9.* | 功能/安全轨：全部 PROVEN 题过 checker 且审计回归通过；总体验收轨：所有前置 Gate（含 M3/NFR-6a）及 T09 全量验收通过 |

M9 采用双轨状态：功能/安全轨可在不解除 M3 阻塞的前提下独立通过；最终验收（V1 完成定义）仍要求 M0–M9 全部准入条件满足，且 §11.2 十二类测试在 CI 全绿。

---

## 8. 需求追踪矩阵（需求 → 设计 → 测试）

| 需求组 | 设计文档章节 | 主要测试项（§11.2） |
|---|---|---|
| FR-1 输入解析 | §10.2 | 单元（契约字段/拒题）；回归（117 题解析报告） |
| FR-2 规则引擎 | §4.1、§4.6、§6.2 | 单元（play/undo 回放哈希、SSK、令牌存活/不可复活）；劫循环回归 |
| FR-3 终局判定器 | §4.3、§8.1、§8.2、§10.2 | 单元（Benson 基准局面含负例）；双活边界；allow_ko/双 pass 劫题契约 |
| FR-4 df-pn 核心 | §7.2–§7.6、§9.2 | 性质（升级义务/确定性/FastCapture 开关与逆序等价）；穷举基准；劫循环（InPath）；对抗 NN |
| FR-5 RZ 机制 | §5.3、§8.3、§8.4 | RZ 单调；长程征子/逃逸依赖；开关剪枝结论一致；QueryState/History 重放；历史发散候选必须回退 |
| FR-6 置换层 | §4.2、§8.5–§8.7 | 隔离测试（同盘异上下文、**同盘同轮走方异历史**）；碰撞注入；PatternTT 命中保真（含禁着/令牌投影双侧比较）；重构透明 |
| FR-7 神经引导 | §9 | 对抗 NN（全零/NaN/逆序结论不变）；manifest 拒载 |
| FR-8 输出 | §10.3–§10.5 | 字段断言；JCS checksum；root/state/history 闭包与确定性比对 |
| FR-9 checker | §10.4 | PROVEN 全过；伪造历史、detached 状态、非法 TT/RZ 重放及 checksum 故障注入 |
| FR-10 CLI | §10.1 | 冒烟（三子命令）；退出码约定 |
| FR-6.9、FR-7.8、NFR-12（新增） | §8.8、§9.5、§10.3.2 | REV19-T03/T04/T05/T09；真实发布复用漏斗、确定性模式与端到端成本 |
| 本轮补证与优化 | §4.4、§7.2～7.5、§8.5、§10.4、§11.2 | REV19-T01/T02/T06/T07/T08，详见本文 §4.2 和任务 §3.11 |
| NFR-1～12 | G1a/G1b、G2–G6、§11 | 见 §7 里程碑准入与 §4 验收方式列 |

---

## 9. Won't（V1 明确不做）/ 实验阶段边界登记

以下能力**不进入 V1 需求**，仅登记边界以防范围蔓延；准入条件见设计文档 §13.2：

| 项 | 边界说明 | 裁定来源 |
|---|---|---|
| 静态双活终局判定 | V1 禁止（FR-3.4）；实验准入需形式化充分条件+穷举+反例集+checker 复验 | Codex P0-4.6 vs Gemini 2.1 |
| KILL"包围判据"终局 | V1 禁止（FR-3.7）；实验准入需 checker 可验证的充分性证明 + 反例集 | 复审 P0-3 |
| LikePassSelfAtari 硬剪枝（类 pass 一子送吃等价剪枝） | V1 禁止；仅排序启发；实验准入需“后继子树合法着法集与目标谓词保持等价”的正式证书 | 三轮复审 P0-3 |
| 未经 QueryState/History 重放的 RZ 外硬剪枝 | V1 禁止；RZ 外仅作为候选，必须按 FR-5.5 对每个被剪枝状态重放完整源证明；放宽需形式化历史无关性证书 | 四轮复审 P0-1 |
| 以“封闭/无共享外气/当前无简单劫/RZ 内历史未变”直接豁免历史比较或重放 | V1 禁止；这些条件至多是构造正式历史无关性证书前的性能预筛，不能单独证明未来 SSK/PSK 合法性不受历史影响 | GeminiSpark 第三方意见 2，复核后收紧 |
| 禁劫形式化为着法合法性规则 | 实验准入：形式化定义 + 着法删除不引入假 LOSS 的完备性论证 | 三轮复审 P0-2 |
| PatternTT 跨历史证明复用 | V1 禁止（FR-6.3 证明复用级须完整历史相等）；实验准入需"历史无关性证书"（历史敏感点闭包进 z 并由 checker 复验） | 复审 P0-1 |
| D4 平移/旋转/镜像归一化复用 | V1 禁止（FR-6.5）；需坐标变换形式化语义（劫点/关键子/边界同步）+性质测试 | Codex P1-5.3 vs Gemini 3.1 |
| PCN 加权 PN/DN 聚合 | V1 禁止（FR-7.4）；需附可靠性/完备性证明 | Codex P0-4.4 |
| 跨题 TT 复用 | V1 每题清空（FR-6.2）；需 ProofContext 兼容校验形式化 | Codex P0-4.2 |
| 1+ε 阈值松弛 | 尚无生产开关，不作为已完成能力；须数学/推进论证与实验准入。现有 TT LRU/GC 不属此待准入项 | 设计 v1.9 §7.3/§8.6/§13.2 |
| 并行 df-pn、目数词典序目标、NN 训练管线 | V2/远期；训练数据方案仅为设计参考（§9.4） | §3.2、§13.2 |
| 9/13 路棋盘、多规则集（Tromp-Taylor/中国/日本枚举） | 旧 Smargo 需求残留：V2 经字段级 `RuleConfig` 形式化（含自杀/Ko/重复/pass/终局/盘角曲四/Seki 逐项定义）后再议；V1 固定 19 路单一规则组合 | 二轮 P0-2 |
| Python API / 多独立包（go-life-death、dfpn-core、tsumego-solver、go-ko 等）/ Python logging / 稳定库 API | 旧 Smargo 需求残留：V1 为 C++ CLI；库式形态列 V2 | 二轮 P0-1 |
| 进度回调与 ETA、完整 SGF 导入导出（注释/标记保留与往返）、可视化引擎、所有解/多解分析 | 旧 Smargo 需求残留，列 V2/远期 | 二轮 P1-7 |
| 在线/周期微调、Seki 持久数据库 | 旧 Smargo 需求残留：训练侧仅保留 §9.4 数据管线设计参考；微调不得用未证明路径产生确定标签 | 二轮 P1-6 |
| 独立 KoProcessor 与劫材预测、LadderEngine | V2/实验；劫材数量与征子结果**只能作启发排序**（劫材价值/先后手/真假劫均影响结论），不得作为定论规则，除非附完整符号证书。固定 ±45° 射线不是证明闭包；V1 的实际长程证明依赖按 FR-5.2 通用规则回传 | 二轮 P2-9 + GeminiSpark 第三方意见 1 复核 |
| Must-Play Region（MPR）过滤候选 | 无独立完备性证明前仅可作为 NNAttentionMask/排序提示，**不得作为过滤器**；证书化后按 FR-5.5 剪枝语义准入 | 二轮 P0-5 |
| 18 通道 NN 特征 | 与设计 12 通道冲突的旧表述作废；通道定义以设计 §9.2 张量表 + `feature_version` 版本化为准 | 二轮 P1-5 |

---

## 10. 附录：需求基线与变更

- 本文档 v1.8 与设计文档 v1.9、任务分解 v1.4 同基线；设计变更时同步编号、状态边界与追踪矩阵。本轮依据两份 2026-09-11 审核报告及复核讨论，不直接采纳未证实的 P0 定性。
- 需求变更流程：评审意见 → 裁定 → 设计文档修订（含变更记录）→ 本文档同步（新增/修改需求须标注来源评审条目与里程碑影响）。
