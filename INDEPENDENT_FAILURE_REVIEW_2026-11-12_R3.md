# LDProver 更新后独立复审（R3）

评审开始日期：2026-11-12；完成日期：2026-11-13（America/Los_Angeles）。对应本地提交 `95d59332cbf270b6317c490e26135c196a0a66b8`，对比 R2 对应提交 `fc2b3604334e35634ae4a5641df6156dcbe401c1`。本报告独立新增，不覆盖 R2。

## 1. 结论

**本次修复有显著且可复现的进展：R2 的六个 TS 篡改反例全部被拒绝，C++ 已能全新构建，23 题的 TS 基准确实是 7 个已定论、16 个 UNKNOWN，p042 已在完整 153 点 region 下求解并通过单独进程的 JSON 校验。**

但仍不能把当前实现验收为“所有声明的输入、区域和子局面均可独立验证”的完整交付。本轮发现以下可复现缺口：

| 编号 | 优先级 | 问题 | 直接影响 |
|---|---|---|---|
| F1 | P0 | TS/C++ checker 的存在性见证可落在声明 region 之外 | 无效证明在重算摘要后仍被接受；不是 R2 的旧缺分支反例 |
| F2 | P1 | C++ 将未定论孩子的默认 DAG ID 当作有效证明边导出 | 基础两眼题已经找到 ba 胜着，却被自己的 checker 拒绝 |
| F3 | P1 | 子局面导出/导入没有恢复根前历史、ko/pass/token 状态 | 合法子局面内存 PASS，JSON 复核 LP-S02 |
| F4 | P1 | `tprover check --problem` 参数被直接忽略 | 指定不存在的原题文件也 PASS，未绑定待验原题 |
| F5 | P1 | TS 与 C++ 的 `lproof/1` 是不兼容的两套格式 | 工作台导出的证明不能由当前 C++ CLI 检查，反向也失败 |
| F6 | P2 | 输入结构校验仍有缺口 | TS 校验 `null` 抛异常；C++ 接受缺右花括号的题目 JSON；TS 忽略 SGF 棋盘尺寸/结构错误 |

这些问题不否定本轮 p042 在当前模型下的搜索进展，也没有证据说明 p042 实际使用了区域外见证。F1 是人工构造的无效证书测试；F2、F3 则在正常求解/导出路径中复现。

**建议验收状态：R2 多项旧缺陷已关闭，原题 TS 正常路径通过；区域见证约束、子局面证书和 C++ 端到端交付仍未通过。**

## 2. 核验范围与方法

- 检查本次 23 个变更文件，并沿输入契约、棋盘/历史、Benson、df-pn、TT/RZ、证明序列化与重放、React 工作台、C++ CLI 复核关键调用链。
- 用户提供的改动清单作为待核验声明；未将其中修复建议视为修改源码的授权。继续遵守本任务“只评审，另建报告，不改代码”的要求。
- 以本地 HEAD 为评审对象；没有另行联网核验 GitHub 同步状态。
- TypeScript 使用 Node v24.18.0 和临时类型剥离 loader 运行当前源码。loader 只处理类型及 JSON 导入，不替换引擎算法。它不是 tsc、Vite 或浏览器 E2E。
- C++ 使用本机 AppleClang 21.0.0.21000334，在全新 `/tmp/ldprover-review-r3-cpp-build` 目录构建和运行；没有复用 R2 二进制。
- 全部测试脚本、证明样例与构建结果置于 `/tmp`。项目只新增本报告，没有改源码、配置、依赖和既有报告。

## 3. R2 修复闭环核对

| R2 问题/本次声明 | 核验结果 | 限定 |
|---|---|---|
| M1 错误 inputHash 总体仍 PASS | 已关闭：LP-C01 | 对 p042 报告改写后重算摘要 |
| M2 childMoves=999 未被拒绝 | 已关闭：LP-S09 | 当前 p042 节点 1 |
| M3 根结论反转仍 PASS | 已关闭：LP-R00 | rootStatus 改为 PROVEN_LOSS |
| M4 删除 AND 应手仍 PASS | 已关闭：LP-N22 | 节点 144，138 个孩子截为 1 个 |
| M5 伪造剪枝状态仍 PASS | 已关闭：LP-S02 | 节点 9 的棋子与 token mask 被篡改 |
| M6 p142 伪造 token mask=0 的败叶 | 已关闭：LP-S02 | 保留原始根 Zobrist；正确绑定根饱和值后测试 |
| C++ 自引用剪枝循环自证 | 已关闭：LP-R02 | 重编译并运行 R2 单节点自引用反例 |
| region 预裁剪 | 当前 16 题已取消 | p042=153/153；其余题数值见基准表；F1 是见证合法性的另一处缺口 |
| frontier 缺失历史键 | 指定源码缺口已修 | key 纳入棋子集合及轮次组成的完整历史字符串；未声称穷尽所有 GHI 情形 |
| C++ TT 按历史长度更新、context 只比 token 数量 | 指定源码缺口已修 | 比较历史内容和 token 字段；PatternTT 已接通搜索查存 |
| FNV 冒充 SHA-256、导出只有表数量 | 原根 TS 路径已实质修复 | 真实 SHA-256、快照池、状态表和节点已导出；四组摘要与 Node crypto 相符；非全面标准认证 |
| 从 JSON 独立复核 | 原根 TS 路径通过 | 单独进程只导入 checker，读取 p042 文件后 PASS；子根和跨语言失败见 F3/F5 |
| C++ 缺 DiagonalNeighbors 导致构建失败 | 已关闭 | 全新 CMake 构建退出 0，仍有未使用变量/重复库警告 |
| CLI 只输出 READY | 占位已移除 | 缺失 proof 返回 2；实际 solve/check 已执行；F2/F4/F6 未闭合 |
| parser 不加载棋子/目标 | 已实质修复 | C++ 输出包含正确 AB/AW 和目标；TS 拒绝轮次冲突、混合目标；结构边界见 F6 |
| 手动局面不触发求解 | 内存交互路径已接通 | 新按钮调用 solveFromPosition，传递实际历史；导出闭环仍失败 |
| 证明横幅无 checker 门控 | 源码已修 | 原根失败显示告警，手动盘面单独标识；未运行浏览器 E2E |
| 劫开关合并不对称 | 源码已修，代表变体通过 | useProblemDefaultKo 区分题目默认与交互配置；p005 开劫实测 Win、双 checker PASS |
| D8 不报告 p351 缺子 | 已报告差异 | 20/21 同色匹配，缺 W[pp]、额外 W[pq]，isExactBijection=false |
| memoryBudget 仅有配置未执行 | 仍未关闭 | TS 只有类型/UI 字段，C++ 只有配置和 CLI 赋值，没有搜索内存预算检查 |

值得肯定的是 p004 这次确实更改了测试棋形，不再是根已终局的一节点“剪枝测试”。本轮它用了 12 个搜索节点、触发 3 次剪枝，两个 checker 均 PASS。但这意味着它是更新后的测试用例，不能把前后成绩直接当作同题性能对比；目录描述的“4 个脱先全部剪枝”也不是本轮实际剪枝数。

## 4. F1 [P0] checker 只在全称枚举中使用 region，存在性见证可以越界

### 触发与实测

使用当前 SRS p001：根是直三眼位，原始候选区域 `[aa, ba, ca]`，求解结果 `PROVEN_WIN / ba`，2 个搜索节点。原始内存与 JSON 校验都 PASS。

复制这份真实证明，仅将声明的 region 改为 `[aa, ca]`，同步调整区域点数并重算当前标准摘要，保留证明里的首手 `ba`：

```text
声明 region = [0, 2]       # aa, ca
证明使用 childMoves = [1]  # ba，已不在声明的合法区域内
TS verifyProofDag                 -> PASS
TS verifySerializedLProofJson      -> PASS
```

这份证明至少有一条违反输入区域约束的边，所以应该被拒绝。无需先证明受限游戏最终胜负，便可以确定该证书无效。

C++ 也复现了相同问题：从一个经过控制验证、仅含 ba 胜见证的两节点证书出发，将 region 中的 ba 删除，重新计算摘要后，CLI 仍 `passed=true / PASS / exit 0`。原始控制证书也 PASS，排除了摘要或样例本身不合法造成的混淆。此处控制证书是从 F2 的导出结果中去掉错误 aa 边得到的，仅修改临时证据样例，未改求解器。

### 原因与建议

[proofChecker.ts:1191](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:1191) 检查 `playMove(mv).legal`，但 GoPosition 的棋盘落子合法性不包含外部 region。只有全称分支的 [proofChecker.ts:1242](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:1242) 调用 `generateLegalMoves(effectiveRegionCoords)`。存在性分支只要某个孩子合法落子并且结论匹配便被接受。

RZ/TT 源证明重放的存在性分支 [proofChecker.ts:772](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:772) 同样没有确认见证着在 query 的允许区域内。C++ 的 [proof_checker.cc:724](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/proof/proof_checker.cc:724) 与 [proof_checker.cc:613](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/proof/proof_checker.cc:613) 具有同类边界。

**修复验收点**：所有普通证明边和复用重放中的见证都必须同时满足棋盘规则与题目允许着法集合；PASS 按明确规则处理。应增加“有控制 PASS 的有效证明 → 排除其见证坐标 → 重算摘要 → 必须 FAIL”的回归。仅增加 AND 全称枚举不能修复这个问题。

## 5. F2 [P1] C++ 会把未完成搜索的孩子误挂到已有叶子

### 正常路径复现

本轮将与 SRS p001 相同的棋形写成临时 JSON。region 包含 aa/ba/ca 三个空点及五个黑方初始占点；这样白墙不死、黑目标可攻防，与手工 SRS 设定一致，合法空点仍是三个眼位。

```text
masked_sgf_str =
(;GM[1]FF[4]SZ[19]PL[B]
 AB[da][ab][bb][cb][db]
 AW[ea][eb][ac][bc][cc][dc][ec])
winning_color=B, turn_color=B, black_search_goal=TOLIVE
black_crucial_stone=bb
region=aa,ba,ca,da,ab,bb,cb,db
```

执行 `tprover solve --problem <该文件> --node-limit 3500 --out-proof <临时文件>`，返回 **exit 2 / LP-L04**。实际写出的证书记录：

```text
rootOutcome = PROVEN_WIN, bestMove = 1 (ba)
node 0: incomingMove=1, outcome=PROVEN_WIN, leaf
node 1: childMoves=[0,1], childNodeIds=[0,0], root
```

node 0 是 B[ba] 后的真两眼叶，却同时被挂在 B[aa] 下面。checker 先重放 aa，自然不能得到同一终局，拒绝了证明。只保留 ba→node 0 后，这个控制证书可通过 C++ 独立文件检查。

### 原因与影响

[dfpn_solver.h:104](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/include/ldprover/search/dfpn_solver.h:104) 将 SearchChild.dag_node_id 默认为 0；阈值截断返回 UNKNOWN 时没有产生对应证明节点，[dfpn_solver.cc:683](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/search/dfpn_solver.cc:683) 却仍置 expanded=true。随后 [dfpn_solver.cc:582](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/search/dfpn_solver.cc:582) 只看 expanded 就输出 child ID 和着法，未确保孩子已定论且对应 ID 有效，造成旧/默认 ID 误连。

这是实际 C++ 证明生成错误。checker 本次拒绝是正确保护，不应通过放松叶检查来“修好”。存在性证明应选择有效的已定论见证；全称证明必须为每个应手保留真实有效的证明节点。默认 ID 应使用明确的无效值，不能与合法 node 0 混同。

另需注意：[tprover_main.cc:170](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/cli/tprover_main.cc:170) 在自身 checker 之前写出 proof 文件。这个失败 solve 已留下无效 proof 产物。建议只在验收成功后发布正式证明文件，或明确把失败产物标为诊断文件。

用户声明的 `checkerFailedOnProven=0` 在本轮 TS 的 23 题集合中成立；它不能扩展成 C++ 引擎也满足同一性质。

## 6. F3 [P1] 子局面内存证明通过，导出后无法恢复根前历史

### 最小真实例子

对 SRS p001 的真实初始位置合法执行 B[ba]，保留 context、历史和目标掩码，调用当前新入口：

```text
solveFromPosition(p001, playedPosition, originalContext)
rootStatus=PROVEN_WIN, nodes=1, root history length=2
verifyProofDag(playedPosition, originalContext, report) -> PASS
verifySerializedLProofJson(report.lproofJson)           -> FAIL / LP-S02
```

不是伪造输入，也不是重置历史构造的新棋题；它就是手动落子后保留完整上下文的正常路径。

### 原因

[proofChecker.ts:302](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:302) 导出的 problemSetup 保存当前棋子和轮次，但没有完整定义子根的 koPoint、consecutivePasses、不可复活 token mask、原根身份和可验证的到达轨迹。虽然历史数据存在快照池中，[proofChecker.ts:575](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:575) 导入时仍调用 `setupInitialStones(...)`，把根历史重置成单快照，并将 ko/pass/token 状态按新初始盘面初始化。

随后 checker 正确发现 state 0 与重建根不一致，返回 LP-S02。对于曾提掉又在原坐标重落的目标、劫点或 pass 状态，问题不仅是历史长度。

**修复方向**：明确区分“原题初始根”和“从原题合法到达的子根”。子局面证书应携带原始 setup/context 与 initialTrace，由独立 checker 重放得到子根；或者定义有明确可信前提、可重建完整起始状态的独立子问题格式。不能简单信任 stateTable[0] 以绕过这个错误。

[App.tsx:167](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx:167) 的按钮和 activeSolvePosition 确实已经接通，所以 R2 的 UI 调用缺口可以关闭；但当前对子局面“独立证明”的交付还停留在内存上下文里。

## 7. F4 [P1] CLI 接受 --problem 却没有核验原题身份

[tprover_main.cc:213](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/cli/tprover_main.cc:213) 对 `--problem` 仅执行 `++i` 跳过路径。没有读取文件，也没有比较棋盘、目标、规则、墙、region 和证书声明。

本轮对一个合法 C++ 文件执行：

```sh
tprover check --proof valid-native.lproof.json   --problem /tmp/nonexistent-original-r3.json
```

仍返回 `PASS / exit 0`。若把路径替换成实际存在的另一题，代码同样不会读取它。

独立文件 checker 验证“证书自带的某个命题”可以是一种接口；当 CLI 已接受原题参数时，必须把它作为待验证命题进行身份绑定，或明确拒绝尚不支持的参数。当前行为会让调用者误以为已验证指定原题。

SHA-256 是对载荷的完整性摘要，不是原题身份认证。inputHash 当前仍主要是棋盘位置的 Zobrist；目标、劫规则、region、墙假设也必须与外部原题核对。单靠 `rawRegionPointCount` 或 `isFullRegionSearch` 的自报字段不能证明没有换题。

## 8. F5 [P1] TS 和 C++ 的 lproof/1 无法交叉检查

双向测试均失败：

| 证明来源 | 验证器 | 结果 |
|---|---|---|
| TS p001，TS 自身双检查 PASS | 当前 C++ `tprover check` | LP-J02，exit 2 |
| C++ 自身 roundtrip PASS 文件 | TS verifySerializedLProofJson | LP-J02 |

原因不是摘要数值偶然不同，而是 schema 本身不同：

- TS 的 boardSize 在 problemSetup 中；C++ [proof_checker.cc:1111](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/proof/proof_checker.cc:1111) 要求顶层 boardSize。
- TS 要求 stateTable 和历史池，C++ 导出以 DAG 重放为核心，没有相同顶层字段。
- TS 的 koRule/crucialStoneOp 是字符串、节点 toPlay 和 token stoneColor 为数值；C++ 对应字段使用另一套数值/字符串编码。
- 两端 Zobrist 实现和根状态编码也不能仅通过移动 boardSize 字段便认为已经互通。

C++ 通过重放 DAG 恢复状态的设计不一定需要显式存储每个状态表条目；问题在于两套不兼容格式都宣称同一个 `lproof/1`，而工作台导出 → CLI 独立检查这条自然交付路径实际不通。

建议先制定共同 schema 与版本/模型身份，建立 TS→C++ 和 C++→TS 的正反向样例。如果短期明确是两个独立协议，应使用不同版本/编码标识，并在产品中说明各自适用的 checker。

## 9. F6 [P2] 输入结构校验仍需在最外层失败关闭

三组具体结果：

1. `verifySerializedLProofJson('null')` 直接抛 `TypeError: Cannot read properties of null (reading 'snapshotPool')`。[proofChecker.ts:476](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:476) 在 `!parsed` 判断之前读取属性。数组与空对象能返回 LP-J02；null 却不走结构化错误路径。
2. C++ [problem_parser.cc:370](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/core/problem_parser.cc:370) 通过字段搜索提取字符串，没有先解析完整 JSON 对象。将合法题目文件最后的 `}` 删除，`tprover solve --node-limit 1` 仍接受并返回 UNKNOWN、exit 0。应在进入搜索之前返回输入错误 2。
3. TS validateStudyLdRzContract 对把 p042 的 `SZ[19]` 改为 `SZ[5]` 的输入仍返回 FR1-OK；对 `masked_sgf_str='garbage'` 且活动关键子为空的输入返回空目标告警并接受。[studyLdRzCatalog.ts:666](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/studyLdRzCatalog.ts:666) 在完整 SGF 结构与棋盘尺寸检查之前就可能因空目标返回成功。

本轮确认轮次冲突、混合目标、目标存在性这些指定旧反例已修。空目标的“显式常假 + 告警”也是当前明确设计，不在本报告中要求改成无条件拒绝；应修的是无效 JSON/SGF 或棋盘尺寸被该分支绕过的问题。

## 10. 本轮基准、构建与资源记录

### 10.1 TS 配置及结果

maxNodes=3500、maxDepth=48、memoryBudgetMb=512、pattern-tt、RZ/FastCapture/progressive widening 开启、wideningBaseK=8、deterministicMode=true、SSK、useProblemDefaultKo=true。按题目默认劫权执行完整 23 题，不用参考答案更改根着。

| 题号 | 实测结论 | 首选着 | 搜索节点 | region/原 region | 内存/JSON checker |
|---|---|---|---:|---:|---|
| p001_straight_three_live | PROVEN_WIN | ba | 2 | 3/3 | PASS / PASS |
| p002_tiger_mouth_conjunction | PROVEN_WIN | ca | 2 | 3/3 | PASS / PASS |
| p003_false_eye_poke_kill | PROVEN_WIN | db | 10 | 3/3 | PASS / PASS |
| p004_outside_rz_pruning | PROVEN_WIN | pass | 12 | 8/8 | PASS / PASS |
| p005_ko_dependent_barrier | UNKNOWN (ko_dependent) | ca | 4 | 1/1 | LP-U01 / LP-U01 |
| p006_vital_capture_tesuji | PROVEN_WIN | da | 2 | 3/3 | PASS / PASS |
| p007_cramped_corner_proven_loss | PROVEN_LOSS | pass | 8 | 2/2 | PASS / PASS |
| chao_vol1_p042 | PROVEN_WIN | os | 1310 | 153/153 | PASS / PASS |
| chao_vol1_p031 | UNKNOWN (NodeLimit) | sr | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol1_p037 | UNKNOWN (NodeLimit) | ss | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol1_p040 | UNKNOWN (NodeLimit) | rs | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol1_p057 | UNKNOWN (NodeLimit) | rr | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol1_p060 | UNKNOWN (NodeLimit) | os | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol1_p088 | UNKNOWN (NodeLimit) | qs | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol1_p090 | UNKNOWN (NodeLimit) | sr | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol1_p098 | UNKNOWN (NodeLimit) | sp | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol1_p101 | UNKNOWN (NodeLimit) | ns | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol1_p222 | UNKNOWN (NodeLimit) | ps | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol2_p142 | UNKNOWN (NodeLimit) | hq | 3500 | 150/150 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol2_p147 | UNKNOWN (NodeLimit) | ns | 3500 | 151/151 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol2_p156 | UNKNOWN (NodeLimit) | nn | 3500 | 149/149 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol2_p162 | UNKNOWN (NodeLimit) | os | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |
| chao_vol2_p351 | UNKNOWN (NodeLimit) | lr | 3500 | 153/153 | 未对 UNKNOWN 另作完整证明复核 |

合计 **6 个 PROVEN_WIN、1 个 PROVEN_LOSS、16 个 UNKNOWN**。7 个已定论报告均通过当前 TS 内存与 JSON 检查；p005 是 KoDependent UNKNOWN，其余 15 个 UNKNOWN 为节点预算耗尽。额外开劫 p005 变体为 Win、2 节点、双 PASS。

这支持用户声明的正常路径统计，但不能排除 F1 的无效证书接受：正例通过率和反例拒绝能力必须分别记录。

### 10.2 p042 全区域结果

本轮结果：`PROVEN_WIN / os / 1310 search nodes / 1832 search pruning events / region=153/153`。

- 求解函数端到端约 922 ms；内存 DAG 复核约 723 ms；JSON 解析、摘要及重放约 740 ms。
- 文件大小 7,474,552 bytes，约 7.13 MiB（十进制约 7.47 MB）。
- 另启动独立 Node 进程，仅导入 proofChecker 模块并读取该 JSON，返回 PASS；确认 1726 个可达证明节点、2017 个状态，实际重放 1568 个可达 RZ 剪枝证书。耗时约 861 ms，进程 maxRSS=348944 KiB（约 341 MiB）。
- 搜索剪枝计数和最终可达证明中的剪枝数量不是同一指标；没有把 1832 次搜索事件写成 1832 个已重放证书。

用户给出的 6.81s/5.36s/5.64s 与本机值不同，可能来自不同运行环境和计时条件，本轮不据此宣称额外加速。os 与参考谱首手 sq 不同，也不能仅凭这一点判错或判对；验收应依赖正确 checker 与绑定后的命题。

### 10.3 C++、类型检查和测试边界

- 全新 `cmake -S cpp -B /tmp/ldprover-review-r3-cpp-build` 与 `cmake --build ... -j 4` 均成功。构建隔离仍保持 proof 库不链接 dfpn。
- 当前 CLI 对缺失 proof 文件返回 2；C++ 自引用反例返回 LP-R02；原生合法终局文件可独立 roundtrip。
- 原生 p042 用当前 C++ 默认搜索配置、maxNodes=3500，结果 UNKNOWN、3500 节点、0 次剪枝。C++ 的 maxDepth/wideningBaseK 默认值与 TS 不同，此项不构成同条件性能对比，也不据此认定 TS 胜解错误。
- F2 的基础两眼样例在当前 C++ 正常路径失败，说明静态符号核验与编译通过还不足以证明镜像运行完整。
- 本机 `npm run lint` 返回 127：`tsc: command not found`；没有 node_modules，本轮没有安装依赖。因此未独立复现用户环境的 compile_applet/lint_applet 成功，也没有声称源码存在某个类型错误。
- 本轮 TS 共 25 次求解：23 题基准、1 次开劫变体、1 次合法子根，累计求解器报告 53,853 节点。C++ 测试单次上限 3500，输入拒绝探针为 1；编译和 checker 不计作搜索节点。
- 未进行浏览器 E2E、所有规则组合穷举、完整 GHI 历史碰撞搜索或大预算性能实验。`memoryBudget` 的执行仍未实现，进程峰值记录不能代替预算控制。

## 11. 独立见解与下一步验收门槛

当前重点已不再是重复修复 R2 的六个固定反例。它们全部失败关闭，说明状态重放和全称覆盖重构确实奏效；但新反例说明，还需要用**完整命题契约**来设计测试，而不能把六个案例视作 soundness 的充分条件。

建议下一轮集中于四个闭环：

1. **每条证明边的规则闭环**：棋盘合法性、region 合法性、劫权限和节点角色必须一致；普通边与 RZ/TT 重放见证使用同一明确契约。F1 必须从双 PASS 变为双 FAIL。
2. **每种根的导出闭环**：原根、手动子根、带 ko/pass 的根、已丢失 token 的根，导出后均能在独立进程恢复相同命题；原题和子题不能仅靠同一个 problemId 混用。
3. **每个语言端的交付闭环**：C++ 已证结果生成的所有证明边有效，正常 solve 成功后独立 check 也成功；TS/C++ 的格式互通或显式版本化；`--problem` 真正校验原题身份。
4. **负面输入与资源边界**：null、缺字段、损坏历史索引、截断 JSON、无效 SGF、非法棋盘尺寸应返回结构化错误；内存预算要么实现，要么明确不承诺执行。

建议把 F1 放在最高优先级，随后修复 F2/F3，再统一文件协议与原题绑定。保留本轮 p042 和 23 题结果作为基线，暂不以提高预算或继续加入新终局规则替代这些交付缺口。

## 附录 A：关键复现片段

### A1. TS 区域外见证（使用当前 p001 报告）

```typescript
const q = structuredClone(report);
q.regionCoords = q.regionCoords.filter(c => c !== 1); // 删除 ba
q.rawRegionPointCount = q.regionCoords.length;
q.proofChecksum = checker.serializeLProofJson(initialPos, context, q).checksum;
checker.verifyProofDag(initialPos, context, q); // 本轮 PASS，预期 FAIL
const text = checker.serializeLProofJson(initialPos, context, q).json;
checker.verifySerializedLProofJson(text);       // 本轮 PASS，预期 FAIL
```

这个变异没有删掉证明中的 ba 边，正是为了检查“声明区域禁止的落子不能作为胜负见证”。

### A2. 子根序列化

```typescript
const sub = originalInitialPos.clone();
sub.playMove(sgfToCoord('ba'));
const r = solver.solveFromPosition(p001, sub, originalContext);
checker.verifyProofDag(sub, originalContext, r); // PASS
checker.verifySerializedLProofJson(r.lproofJson); // LP-S02
```

### A3. C++ 基础样例与控制证书

[基础两眼 JSON](/tmp/ldprover-review-r3-native-p001-corrected.json) 用于正常 solve；其产出的根边 `[aa,ba]→[0,0]` 导致 LP-L04。仅删错误 aa 边的 [控制证书](/tmp/ldprover-review-r3-native-valid-single-witness.json) 可通过；再禁用 ba 的 [无效证书](/tmp/ldprover-review-r3-native-forbidden-single-witness.json) 本应失败，却仍 PASS。

这里删除证书边仅用于隔离 checker 缺陷，并未修补项目源码或把经过人工处理的证书冒充 solver 原始产物。

## 附录 B：本轮证据位置和文件改动

以下临时材料可供本会话复跑；`/tmp` 可能被系统清理，关键输入、条件、结果和源位置已在报告正文保留：

- [核心 TS 测试脚本](/tmp/ldprover-review-r3-probes.mjs) / [结果](/tmp/ldprover-review-r3-probes.json)。
- [其余 15 题脚本](/tmp/ldprover-review-r3-batch.mjs) / [结果](/tmp/ldprover-review-r3-batch.json)。
- [M6、契约、D8 与开劫补充脚本](/tmp/ldprover-review-r3-extra.mjs) / [结果](/tmp/ldprover-review-r3-extra.json)。
- [独立进程 JSON 检查脚本](/tmp/ldprover-review-r3-standalone.mjs) / [结果](/tmp/ldprover-review-r3-standalone.json)。
- [p042 原始 JSON 证明](/tmp/ldprover-review-r3-chao_vol1_p042.lproof.json)、[区域外见证 TS 文件](/tmp/ldprover-review-r3-outside-region.lproof.json)、[子根 TS 文件](/tmp/ldprover-review-r3-subroot.lproof.json)。
- [C++ CLI 基础检查记录](/tmp/ldprover-review-r3-cpp-tests.json)、[正常两眼题失败记录](/tmp/ldprover-review-r3-native-witness.json)、[C++ 正/负控制结果](/tmp/ldprover-review-r3-native-controls.json)、[无效 JSON 接受记录](/tmp/ldprover-review-r3-invalid-json.json)。

C++ 基础检查脚本的第一版小 region 夹具把黑棋也定义成不死墙，因此它的一节点 PASS 只用于 CLI 读写、格式与参数检查，不用作两眼搜索或“区域外见证”证据；F1/F2 使用的是包含黑方初始占点的修正夹具及独立正/负控制。

项目内仅新增 `INDEPENDENT_FAILURE_REVIEW_2026-11-12_R3.md`。结束时对所有 Git 跟踪文件与开始时的 SHA-256 清单逐项比较，内容无变化；原报告和用户既有未跟踪内容保留。
