# LDProver 更新后独立复审（R2）

评审日期：2026-11-12（America/Los_Angeles）。本报告独立新增，不覆盖上一轮评审。

## 1. 结论：实质改进成立，形式化可靠性与 C++ 交付仍未完成

**当前版本可以认定为“部分修复、搜索表现可复现”，不能认定为“全链路修复完成、100% soundness、独立证明验收通过”。**

本轮确认了真实进展：16 题直接读取 JSON，旧的关键子 `qs` 回退已移除，活动区域内的初始占点可在提子后重新落子；旧超级链判活逻辑已移除；求解器内的 RZ 源证明重放开始枚举 query 合法应手；C++ 双 pass 已改为依据 UCA。p042 的 `PROVEN_WIN / sq / 2035 nodes / 285 prunes / checker PASS` 完整复现，SRS 7 题及额外开劫变体的结果也复现。

但阻断验收的问题依然存在，而且出现了明确的新构建回归：

- **TypeScript checker 仍接受错误证明**：伪造令牌状态、遗漏 AND 应手、非法走子边、根结论与根节点相反、错误 inputHash 都能得到总体 PASS。
- **C++ checker 仍接受循环自证**：单个 RZ 剪枝节点把自身作为源证明，真实局面 NonTerminal，检查仍 PASS。
- **当前 C++ 全新构建失败**：搜索器调用不存在的 `Position::DiagonalNeighbors`。
- **原题覆盖范围未闭合**：p042 原始 region 有 153 点，导入后活动区域仅 35 点；首手 sq 后白方有 140 个原 region 合法着，而搜索只枚举 23 个，另外 117 个没有在根证明中形成覆盖义务。
- **历史隔离、可独立下载验证的证据、手动局面重新求解仍有缺口**。不能用当前 checker 的 PASS 为这些路径背书。

这里没有断言 p042 的围棋结论错误；否定的是“现有产物已经独立证明完整原题”这一验收结论。

### 评审对象与边界

- 当前 HEAD：`fc2b3604334e35634ae4a5641df6156dcbe401c1`。
- 本轮重点检查 `c8369ac → fc2b360` 的 17 个变更文件，并沿输入、棋盘规则、终局、搜索、TT/RZ、证明序列化/checker、C++、前端调用链复核遗留问题。
- 附件是**待核验的完成声明与分析材料**；其中扩展规则、修复代码、开展进一步实验等建议没有被当作本次用户指令。
- 本次没有修改源码、依赖、配置或原报告；只新建本报告。测试脚本和构建目录位于 `/tmp`。
- 下面分别注明“实测”“源码确认”“尚未验证”。临时 TypeScript loader 只剥离类型、处理类型导入和 JSON 模块，没有替换求解或检查算法；它不等于 TypeScript 类型检查或浏览器构建。

## 2. 附件完成声明逐项核对

| 声明 | 复审判断 | 证据及限制 |
|---|---|---|
| 16 题直读真实 JSON | 已实现 | 目录直接导入全部 16 个文件；盘面来源不再是旧缩微手写盘面 |
| 清除 qs 回退，p222 恢复真实目标 | 已实现 | 当前 p222 为真实做活目标；本轮求解 2500 节点 UNKNOWN，不再是旧的一节点假杀 |
| 保留初始占点，支持倒扑反提 | 已实现，但区域仍裁剪 | 本轮 16 条原谱参考主变共 105 手均能合法回放、颜色一致且均在当前候选内 |
| 恢复“100% 纯经典 Benson” | 关键方向成立，表述过度 | 原始正交链、不动点、单区域单贡献已恢复；仍有不死墙公理、15 个空点上限等额外模型条件 |
| RZ 全覆盖源证明重放 | 求解器内部已有实质修复 | TS/C++ 都枚举 query 在传入 region 内的合法着；独立 checker 尚未执行等价的语义重放 |
| 独立 checker 已完整验证 | 不通过 | 下节 6 组 TS 绕过及 C++ 自引用剪枝反例 |
| 22 个失败分支 falseProofs=0 | 附件报告，未完整独立复跑 | 仓库未找到对应可执行回归脚本/逐例结果；本轮复验旧误判局面，不冒充完整 22 分支搜索结果 |
| SRS 7/7，p005 开劫变体正确 | 本轮复现 | 见第 7 节；UNKNOWN 不构成完备证明，当前 PASS 仍受 checker 缺口限制 |
| p042 2035 节点、285 剪枝 | 本轮精确复现 | 首手 sq，当前 checker PASS；原 region 全覆盖与独立证书验收未完成 |
| p031 手动 sr 后约 2058 节点 | 未复现，前端路径未实现 | UI 手动着不触发搜索；另做新子根试验 2500 节点仍 UNKNOWN，详见第 6 节 |
| 其余 15 题默认 UNKNOWN(NodeLimit) | 本轮全部复现 | 每题 maxNodes=2500；这只描述该配置下的搜索结果 |
| 15 题原谱终点 NonTerminal | 事实成立，但不足以解释失败 | 实际 16 题全部 NonTerminal，包括能求出的 p042 |
| D8 自动对齐及三处标签修正 | 映射/首手修正有依据，自动验证不完整 | 14 题 D8=2，p142/p351 D8=7；p351 仍缺失原图映射白子 pp |
| C++20 镜像已通过编译 | 当前版本不成立 | 全新 CMake 构建因缺少 DiagonalNeighbors 失败 |
| 类型校验通过、约 6 倍性能提升 | 本轮未验证 | 本地 tsc 不存在；没有同条件旧版基线、测量脚本及分阶段计时支持 6 倍结论 |

## 3. [P0] checker 的新检查仍不能阻止伪证明

### 3.1 TypeScript：重算了叶子，但没有证明这个叶子可达

[proofChecker.ts:223](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:223) 只比对根条目自报 Zobrist 与初始位置，并检查非根父 ID 顺序。[proofChecker.ts:286](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:286) 从 stateTable 自报的棋子、轮次、ko、pass 和 token mask 构造叶局面，再调用终局算子；**没有从原输入沿边重放以确认这些字段真实可达**。

这比旧版“完全不重算终局”有进步：上一轮直接把 p142 真实初始状态写成胜叶的反例，现在确实被 CHK-04 拒绝。但把同一个真实初始状态的 `survivingTokensMask` 改成 0，再声称目标已被提光、根为 PROVEN_LOSS，仍获 PASS。真实 p142 根保持 NonTerminal。本测试属于人工构造的无效证书，用于检验 checker 的拒绝能力，不是声称求解器自然产出了该假叶。

### 3.2 “全覆盖”只检查列出的孩子，不检查遗漏应手

[proofChecker.ts:329](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:329) 对全称节点调用 `childNodeIds.every(...)`，只检查已记录孩子是否与父结论一致，没有枚举合法应手、核验 childMoves 与孩子对应关系，也没有用真实轮次重算 AND/OR 类型。

基于本轮实际求得的 p042 报告进行以下测试。每次从完整报告独立复制，按当前序列化器重算 checksum，避免仅因字节变化而被拒绝：

| 无效证明改动 | 实测结果 |
|---|---|
| inputHash 改为 `deliberately-wrong` | 总体 PASS，同时 CHK-01=false |
| 节点 1 的 childMoves 改成非法坐标 999 | PASS |
| 只把 report.rootStatus 从 PROVEN_WIN 改成 PROVEN_LOSS | PASS |
| AND 节点 71 的 21 个孩子仅保留 1 个，删掉其余 20 个对应应手 | PASS |
| 剪枝节点 2 所指状态清空黑白棋子并置 token mask=0 | PASS |
| 另造 p142 单叶，保持根自报 hash，伪造 token mask=0、声称败 | PASS，所有审计项为 true |

错误 inputHash 的原因尤其直接：[proofChecker.ts:394](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:394) 的 `allPassed` 纳入 checksumValid，却没有纳入 inputHash 相等条件。根状态与根节点结论也没有绑定。这些都是可确定复现的问题，不是理论风险。

### 3.3 RZ 检查仍未独立重放

[proofChecker.ts:369](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:369) 检查 reason、源 ID 的范围/先后关系、源节点 outcome 是否相同。它没有在剪枝节点的真实 query 状态及历史下重放源证明。相反，求解器中的 [dfpnSolver.ts:665](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts:665) 已增加合法应手枚举、嵌套剪枝解包和劫限制；**内部搜索重放的改进没有自动补齐外部 checker**。

目前 `replayedPrunedCertificates` 是符合上述结构条件的节点数，不能解释为已完成独立语义重放的数量。checker 的 `Soundness = 100%` 文案不应作为正确性证据。

### 3.4 C++：一条主路径与自引用剪枝可绕过检查

[proof_checker.cc:216](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/proof/proof_checker.cc:216) 虽增加节点结论一致性，但叶终局只对根叶及至多 64 层的单条主路径复核。遇到剪枝节点、没有可选非剪枝孩子、达到深度上限都会停止路径循环，之后仍可返回 PASS。其他分支的状态、合法着和终局未全图验证。

本轮用**当前成功编译出的 core/terminal/rz/proof 库**构造 5×5 单黑子局面：真实终局为 NonTerminal；证明图只有 node 0，outcome=Win、pn=0、dn=SAT、`is_pruned_outside_rz=true`、`source_proof_node_id=0`。结果：`selfReferencedPrune=PASS passed=1`。源证明指向自身的循环自证没有被拒绝。测试不依赖构建失败的 dfpn 库。

**验收要求**：从可信输入恢复可达状态与历史；校验根绑定和节点类型；逐边检查合法性；对全称节点比较完整合法着集合；对 TT/RZ 复用建立无环、可重放闭包；任何审计项失败均导致总体 FAIL。上述无效证书即使重算 checksum 也必须失败。

## 4. [P0/P1] 历史隔离、输入范围与下载证书仍未闭合

### 4.1 frontier 绕开了历史隔离（P0，源码确认）

[dfpnSolver.ts:964](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts:964) 的 key 仍然是：

```text
zobrist : toPlay : koPoint : consecutivePasses : survivingTargetTokensMask
```

它不含 SSK/PSK HistorySet。缓存存储并复用孩子 pn/dn、outcome、stateId、dagNodeId、代表证明和 RZ，而不只是排序分数。即使 BoardTT 因历史不匹配而拒绝复用，后续仍可能取得另一历史的 frontier，并把旧的已定论孩子直接带入聚合。新增 BoardTT 回调没有封住这一独立通道。

C++ 遗留缺口也未修：[transposition_table.cc:81](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/tt/transposition_table.cc:81) 按历史**长度**相同更新旧条目的证明，却保留旧历史内容；[types.h:197](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/include/ldprover/core/types.h:197) 的 context 相等只比较 token 数量，不比较 token 内容。

以上是实现上的隔离缺陷。本轮没有构造完整历史碰撞搜索来证明 p042 已受到污染，因此不把这种可能性写成已发生事实。修复应让带证明内容的缓存遵循完整状态/历史身份，或跨历史仅复用启发式提示。

### 4.2 region 仍被裁剪，原题的全称义务没有恢复（P1）

[studyLdRzCatalog.ts:501](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/studyLdRzCatalog.ts:501) 的活动区域仍是目标侧锚点外扩两格所得矩形与 rawRegionSet 的交集。修复“保留初始占点”不等于保留原始 region。

实测 p042：raw region 153 点，活动 region 35 点；走 B[sq] 后，按同一个棋盘规则器，原 region 内白方合法着（含 pass）为 140，活动 region 中为 23，缺少 117 个，例如 `as`、`ls`、`mn`、`sa`。这些着在求解器生成候选之前已被过滤，因而不会进入后续 OutsideRZRevalidated 的逐应手检查。

这不证明其中某一手能推翻活棋；说明当前证据缺少“这些被删除的应手不影响命题”的证明。可以定义并导出一个明确的局部受限游戏，也可以提供可检查的区域外应手消除/原根包装证书；当前不能把前者的结果无条件标为后者。

### 4.3 导出的 lproof 尚不能独立恢复证据（P1）

[proofChecker.ts:38](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:38) 只导出 state/history 表的数量，没有表内容；没有完整绑定 region、immortalWallCoords；childMoves 等检查所需字段也未完整进入载荷。当前 checker 使用内存 SolveReport，不是从下载文件恢复所有必要证据。C++ [proof_checker.cc:42](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/proof/proof_checker.cc:42) 更只输出 contextId、根信息、初始哈希、节点数量等摘要，没有完整 DAG。

TypeScript 所谓 `sha256-jcs:` 实际是拼接 FNV 计算值，主体为普通 `JSON.stringify`，不是其注释宣称的 SHA-256/JCS 实现。checksum 不能代替语义重放，更不能弥补未进入文件的证据。后续应把状态、历史、规则/目标、区域与墙假设、根身份、复用闭包一并纳入版本化格式和真实性校验。

## 5. [P1] C++ 当前不可完整构建，也尚非可用 CLI 镜像

执行：

```sh
cmake -S cpp -B /tmp/ldprover-review-r2-cpp-build
cmake --build /tmp/ldprover-review-r2-cpp-build -j 4
```

配置成功；AppleClang 21.0.0.21000334 编译到 dfpn 时失败，退出码 2：

```text
cpp/src/search/dfpn_solver.cc:102:20:
error: no member named 'DiagonalNeighbors' in 'ldprover::Position<5>'
```

`Position<7>`、`Position<19>` 同样报错。[position.h:91](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/include/ldprover/core/position.h:91) 只声明了 OrthogonalNeighbors，新增评分代码却调用 DiagonalNeighbors。这是源码接口缺失，不能归因于缺少第三方库。没有修补源码后重试，也没有把旧二进制作为新版本验证结果。

其他仍未完成的交付路径：

- [tprover_main.cc:27](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/cli/tprover_main.cc:27) 对 solve/check/bench 只返回 READY。本轮单独编译当前 CLI 源文件，执行 `check --proof /tmp/definitely-missing-proof-r2.json`，不存在的文件也输出 READY 并成功返回；没有实际检查文件。
- [problem_parser.cc:79](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/core/problem_parser.cc:79) 仍不装载 AB/AW 和目标 token。本轮向 parser 提交含 AB[aa]、AW[bb]、关键子 aa 的样例，返回 `valid=1 black=0 white=0 tokens=0`。
- C++ 搜索没有接通 PatternTT 的查存调用；配置中存在 `enable_pattern_tt` 不等于功能已接通。
- 修复值得确认：单黑子双 pass 的 C++ 实测由旧 Win 改为 Loss，与“不满足 UCA 不判活”的新规则一致。

因此应分别记录“部分 C++ 库可编译和可测试”“完整 CLI 构建失败”“CLI 功能未接通”，不能合并为“镜像验证完成”。

## 6. 前端、契约与数据语义的剩余问题

### 6.1 p031 手动 sr 后的 2058 节点结论未被当前工作台支持（P1）

[App.tsx:143](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx:143) 的求解 useMemo 只依赖 currentProblem 和 solverConfig。[App.tsx:175](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx:175) 的 manualMoves 仅用于构造 displayedPosition，并触发盘面终局展示，不触发 solveProblem。原根报告与手动后的盘面同时显示，容易误认为已求解当前子局面。

本轮额外把 p031 落 B[sr] 后的棋子集合、白方轮次构造成**新的子根输入**，沿用默认配置求解，结果 `UNKNOWN / node_limit / 2500 nodes / best rs`，没有复现 2058。此试验重新初始化了历史，不能冒充从原根携带完整 HistorySet 的续搜，也不能排除附件曾用另一配置或版本获得该数字。附件没有给出足以绑定这条成绩的原始产物与配置，因此该数字仍待确认。

即使未来子根求解成立，仍需原根首手合法性、历史与 token 绑定、完整防守覆盖及证书包装，才能升级为原题结果。

[App.tsx:884](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx:884) 的“形式化证明通过 · 与原谱真解一致”横幅条件是 rootStatus=Win 且首手命中参考标签，没有检查 verificationReport.passed；故障注入使 checker 失败时也可能继续显示成功文案。应从真实校验状态派生该展示。

### 6.2 自动 D8 匹配是评分选择，不是输入等价证明（P2）

[studyLdRzCatalog.ts:255](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/studyLdRzCatalog.ts:255) 在 8 种变换中选同色匹配数最高者，没有要求全量匹配、排除多解或拒绝缺子。当前 14 题选择 180° 旋转，p142/p351 选择反对角，和附件一致；p040 的 ps、p142 的 ks、p147 的 os 也有原谱映射依据。

但 p351 原始白 dd 经映射得到 pp，masked 盘面仍无该白子。当前自动检测照样通过。三处标签纠正不等于所有题的 raw 与 masked 局面已等价；“100% 精确坐标映射/核验真解”应至少记录缺失/额外棋子和匹配置信条件。参考谱的标签、参考路径、搜索结论和完整原题证明应分别存储。

### 6.3 契约拒绝逻辑仍与展示不一致（P1）

[App.tsx:402](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx:402) 的契约测试面板按预设返回静态结果，未调用实际导入器。本轮实际调用 parseStudyLdRzJsonToProblemSpec：PL[B] 与 turn_color=W 冲突、混合 `nr&qr|pp`、活动关键子为空，均未被拒绝。混合目标中不存在于黑棋集合的坐标还被 buildProofContext 默认视作白棋 token。

移除 qs 回退修复了本批 p222 的具体错误，但没有建立完整输入有效性契约。应在解析边界验证轮次、目标表达式、目标实际棋子、范围与颜色，再给出明确的拒绝或降级状态。

### 6.4 劫开关、资源与性能声明的边界（P2）

[dfpnSolver.ts:267](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts:267) 用 `config.attackerAllowKo || problem.attackerAllowKo` 合并进攻方设置，用 `problem.defenderAllowKo && config.defenderAllowKo` 合并防守方。对当前题库默认组合能够工作，但题目强制 attacker=true 时 UI 不能关闭，题目 defender=false 时 UI 不能打开。若这是契约，应清晰展示锁定及有效配置；否则开关行为不符合通常的覆盖预期。

邻接预计算、增量哈希、epsilon 阈值和排序调整在代码中可见，但本轮没有同条件旧版性能基线，不能独立确认“约 6x”。memoryBudgetMb / memory_budget_bytes 仍没有搜索内预算执行路径；同步 React 搜索也仍存在。不要把配置项存在、耗时字段存在或单次很快等同于资源约束已实现。

## 7. 本轮实际验证记录

### 7.1 运行条件

TS：Node v24.18.0，当前源码经临时 loader 运行。真实题配置与 UI 默认一致：maxNodes=2500、maxDepth=48、memoryBudgetMb=512、pattern-tt、RZ/FastCapture/progressive widening 开启、wideningBaseK=8、deterministicMode=true、SSK、attackerAllowKo=false、defenderAllowKo=true。SRS 按各题显式设置或默认禁劫；p005 另加一次 attackerAllowKo=true。

本轮合计 25 次 solveProblem 调用：16 真实题、7 个 SRS、1 个 p005 开劫变体、1 个 p031 新子根。累计求解器报告节点数 **42,072**，没有增加任何单题 2500 节点上限。另有 105 手原谱回放、4 组旧误判局面回放、checker 定点变异、parser/D8/region 检查及 C++ 编译/小探针。节点数是当前求解器计数，不等价于唯一状态数。

第一组 TS 测试进程记录 maxRSS=333680 KiB（约 326 MiB）；这是该进程整体峰值，不是单题资源账本或 512 MiB 限制已受执行的证据。本轮未以耗时宣称加速倍数。

### 7.2 SRS 及额外开劫变体

| 题号 | 实测结论 | 首手 | 节点 | RZ 剪枝 | 当前 checker |
|---|---|---|---:|---:|---|
| p001_straight_three_live | PROVEN_WIN | ba | 8 | 0 | PASS |
| p002_tiger_mouth_conjunction | PROVEN_WIN | ca | 2 | 0 | PASS |
| p003_false_eye_poke_kill | PROVEN_WIN | db | 10 | 0 | PASS |
| p004_outside_rz_pruning | PROVEN_WIN | pass | 1 | 0 | PASS |
| p005_ko_dependent_barrier | UNKNOWN (ko_dependent) | ca | 4 | 0 | 拒绝 UNKNOWN |
| p005_ko_dependent_barrier-allow-ko | PROVEN_WIN | ca | 2 | 0 | PASS |
| p006_vital_capture_tesuji | PROVEN_WIN | da | 2 | 0 | PASS |
| p007_cramped_corner_proven_loss | PROVEN_LOSS | pass | 8 | 0 | PASS |

这些结果与附件一致。但 p004 名为 outside_rz_pruning，却在根终局 1 节点完成、0 次剪枝；不能用这题“通过”证明 RZ 检查路径得到覆盖。其余测试当前 PASS 的可信范围也受第 3 节限制。

### 7.3 16 道原题

| 题号 | 实测结论 | 首选着 | 节点 | 活动/原始 region 点数 | 原谱主变长度 | 主变终点 |
|---|---|---|---:|---:|---:|---|
| chao_vol1_p031 | UNKNOWN (NodeLimit) | os | 2500 | 28/153 | 3 | NonTerminal |
| chao_vol1_p037 | UNKNOWN (NodeLimit) | rs | 2500 | 40/153 | 3 | NonTerminal |
| chao_vol1_p040 | UNKNOWN (NodeLimit) | os | 2500 | 48/153 | 7 | NonTerminal |
| chao_vol1_p042 | PROVEN_WIN | sq | 2035 | 35/153 | 3 | NonTerminal |
| chao_vol1_p057 | UNKNOWN (NodeLimit) | os | 2500 | 36/153 | 1 | NonTerminal |
| chao_vol1_p060 | UNKNOWN (NodeLimit) | rs | 2500 | 30/153 | 3 | NonTerminal |
| chao_vol1_p088 | UNKNOWN (NodeLimit) | rr | 2500 | 30/153 | 3 | NonTerminal |
| chao_vol1_p090 | UNKNOWN (NodeLimit) | rs | 2500 | 30/153 | 5 | NonTerminal |
| chao_vol1_p098 | UNKNOWN (NodeLimit) | sq | 2500 | 30/153 | 8 | NonTerminal |
| chao_vol1_p101 | UNKNOWN (NodeLimit) | so | 2500 | 42/153 | 9 | NonTerminal |
| chao_vol1_p222 | UNKNOWN (NodeLimit) | ps | 2500 | 42/153 | 15 | NonTerminal |
| chao_vol2_p142 | UNKNOWN (NodeLimit) | ls | 2500 | 56/150 | 11 | NonTerminal |
| chao_vol2_p147 | UNKNOWN (NodeLimit) | mo | 2500 | 71/151 | 5 | NonTerminal |
| chao_vol2_p156 | UNKNOWN (NodeLimit) | mq | 2500 | 82/149 | 7 | NonTerminal |
| chao_vol2_p162 | UNKNOWN (NodeLimit) | qs | 2500 | 60/153 | 13 | NonTerminal |
| chao_vol2_p351 | UNKNOWN (NodeLimit) | mn | 2500 | 63/153 | 9 | NonTerminal |

p042 当前 checker PASS，RZ 剪枝 285 次。全表原谱路径均可合法回放；路径只是一个参考变化，不是双方所有选择的完备策略树。

旧误判复查：p162 `rs sp sr`、p156 `nr mq ls`、p147 `ms kn ks`、p351 `lr kr ms os ns` 均可合法回放，各步新终局均为 NonTerminal，没有复现旧的过早 UCA。该结论只覆盖所列具体局面，不等于完成附件 22 个分支的全部搜索回归。

### 7.4 构建与未验证事项

- CMake 配置成功；完整 C++ 构建失败，原因见第 5 节。
- 当前已成功构建的 core/terminal/rz/proof 库用于双 pass、parser、checker 自引用三个探针。
- `npm run lint` 实测退出 127：`sh: tsc: command not found`。工作区没有 node_modules；本轮没有安装依赖。此结果表示类型检查环境未就绪，**不能推断代码类型检查通过或存在具体类型错误**。
- 未执行浏览器交互 E2E、生产前端构建、完整 22 分支搜索、同条件新旧性能对比、完整历史碰撞搜索及全原 region 搜索。

## 8. 我的独立判断与后续优先级

**首要问题已从“有明显错误的终局启发式”转为“证明链是否真的覆盖并绑定所声称的命题”。** 本次删除超级链判活、隔离眼形启发式是正确方向；不应为了减少 UNKNOWN 再把未证明的形状潜力放回终局。

同时，附件对 UNKNOWN 的解释仍偏早：当前 16 条原谱终点全部 NonTerminal，而 p042 仍能在预算内完成搜索。因此 NonTerminal 只能说明“原谱结束不等于这个终局算子立即认可”，不能证明其余题必须引入某一种新定理，也不能区分排序差、区域模型差异、额外封口深度和终局规则能力不足。

代码称“纯经典 Benson”也应更精确：[bensonUca.ts:300](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts:300) 限制候选区域空点数不超过 15，带不死墙的己方连通链跳过两眼淘汰。这个实现包含明确的局部模型公理和保守过滤。它们未必都是错误，但应成为输入和证明的一部分；在未绑定这些前提时，不能用算法名称代替 soundness 论证。

建议依次完成以下有明确验收点的工作，本报告不实施这些修改：

1. **先恢复 checker 的拒绝能力并修复 C++ 构建。** 第 3 节所有无效证书必须 FAIL；C++ 自引用、缺子节点、只验证主路径、提前结束均不能 PASS；全新构建通过。
2. **闭合命题身份与历史边界。** 导出完整证据和区域/墙/规则假设；frontier 与 TT 严格隔离历史；从下载文件在独立进程验证；区域外合法应手有可检查的消除证书或明确限定为受限游戏。
3. **把结果与真实执行路径对齐。** 手动局面求解应有保存原始目标和历史的入口；UI 的证明标识受真实 checker 状态控制；parser 面板运行真实 parser；p351 的缺子差异单独处理。
4. **再分析未解题并引入可证明的扩展。** 在可信输入和 checker 下记录每题停止原因、未闭合义务、历史分支、终局覆盖及实际资源，再选择封口/见合/对杀证书。双劫、双活若涉及规则变化，先明确目标语义，不能仅为匹配参考谱而扩充胜负判定。

推荐下一次验收以“反例拒绝 + 原根完整覆盖 + 独立文件检查”作为主门槛；解题率和节点下降作为通过该门槛后的性能指标。现阶段 p042 适合作为可重复的候选证明样例，不宜作为全系统可靠性的背书。

## 附录 A：关键反例的复现方法

以下为对本轮 p042 内存报告的最小语义变异。使用项目实际 DfpnSolver、ProofArtifactManager 和默认 config，逐项从原报告复制；代码片段不需要改动项目源码：

```typescript
const solver = new DfpnSolver(config);
const r = solver.solveProblem(p042);
const ctx = DfpnSolver.buildProofContext(p042, config);
const pos = DfpnSolver.buildInitialPosition(p042, ctx);
const checker = new ProofArtifactManager();
const q = structuredClone(r);
const n = q.proofDagNodes.find(n =>
  !n.isOrNode && n.outcome === 'PROVEN_WIN' && n.childNodeIds.length > 1);
// 本版本命中 node 71，21 个应手变为 1 个。
n.childNodeIds = n.childNodeIds.slice(0, 1);
n.childMoves = n.childMoves.slice(0, 1);
q.proofChecksum = checker.serializeLProofJson(pos, ctx, q).checksum;
checker.verifyProofDag(pos, ctx, q); // 本轮实测 passed=true
```

另外分别修改 `q.inputHash`、`q.rootStatus` 或 childMoves，可按第 3 节复现。伪造叶反例需保持根条目自报 zobrist 不变，把 stateTable 的 survivingTokensMask 设为 0，节点改成败叶 `(SAT,0)`，再重算 checksum。该反例的关键是 checker 信任了 token 字段，未验证它是否由合法路径产生。

C++ 自引用反例的关键字段为：真实初始局面只含黑 aa、目标 aa；单个 `ProofDagNode<5>` 的 node_id=0、source_proof_node_id=0、is_pruned_outside_rz=true、outcome=kProvenWin、pn=0、dn=kPnDnSaturation；report 根指向 0。调用当前 VerifyProofDag 返回 PASS。

临时复查材料（便于本会话复跑，`/tmp` 可能被清理；关键输入、结果和源码定位已经写入本报告）：

- [TS loader](/tmp/ldprover-review-r2-loader.mjs)、[核心探针](/tmp/ldprover-review-r2-probes.mjs)、[结果](/tmp/ldprover-review-r2-probes.json)。
- [15 题补充及新子根/D8 脚本](/tmp/ldprover-review-r2-batch.mjs)、[结果](/tmp/ldprover-review-r2-batch.json)。
- [region/parser 探针](/tmp/ldprover-review-r2-extra.mjs)、[结果](/tmp/ldprover-review-r2-extra.json)。
- [本轮 p042 完整内存报告](/tmp/ldprover-review-r2-p042.json)、[C++ 自引用探针](/tmp/ldprover-review-r2-cpp-checker.cc)。

## 附录 B：证据身份与文件改动

| 输入材料 | SHA-256 |
|---|---|
| failed_problem.md | `258c5975e213b5aa503e63fbff69d38163c6872355c52805dc3b0171e2f2e565` |
| unresolved_root_cause_report.md | `1771083db8395410da575478b75cc05293d8b84c98126c9f7f2db5d1a01324c9` |
| 本轮 Pasted text.txt 完成声明 | `24ee7863b98deca22cda095f3de7c307d4a96715e4cc7b6b8936714b15aab339` |

本轮只新增 `INDEPENDENT_FAILURE_REVIEW_2026-11-12_R2.md`。开始/结束对所有 Git 跟踪文件做 SHA-256 对比，内容无变化；既有未跟踪目录及原评审报告保留。源码问题在此报告中提出，没有修改实现。
