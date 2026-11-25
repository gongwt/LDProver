# LDProver 失败题目与证明可信性独立评审

评审日期：2026-11-12（America/Los_Angeles）  
评审对象：本文件所在的工作台项目快照；不代表其他目录下同名 LDProver 项目的状态。  
范围：只读审查、临时目录中的定点验证、新建本报告。未修改项目代码、题库、配置或既有文档。

## 1. 我的主要判断

**当前优先级应是恢复“求解的是哪一道题、允许哪些着法、证明检查到底检查了什么”的可信性，然后才是提高解题率。** 现在的 UNKNOWN 可能是正常资源耗尽，也可能来自输入转换和着法生成缺陷；PROVEN_WIN 则可能受到终局误判、历史混用或不完整复核影响。把这些结果混在一起优化节点数，会使后续性能比较失去意义。

我总体赞同 `unresolved_root_cause_report.md` 对数据分流、Benson 启发式和 checker 缺陷的质疑，但不接受其中所有绝对化结论。`failed_problem.md` 中多处“已解决”“等价活棋手”“严格形式化证明”目前缺乏可接受的证据支撑。

本次确认的关键问题按优先级如下。P0 表示会直接破坏证明可信性，P1 表示会改变问题语义或阻断可靠验收，P2 表示性能或可观测性问题；不是生产安全漏洞评级。

| 编号 | 优先级 | 发现 | 本次证据 |
|---|---|---|---|
| R1 | P0 | checker 没有实际重放终局、状态转换或全称分支；输入哈希失败也可总体 PASS | 源码及伪造叶子定点测试 |
| R2 | P0 | 搜索区域只包含初始空点，提子后腾出的合法交叉点永久缺席 | p162 的合法 `rr` 回放与候选集对照 |
| R3 | P0 | Benson 超级链与眼数扩展接受了不可靠的活棋证据 | p162 活棋标记与停着后被提的反例；另三题终局回放 |
| R4 | P0 | 搜索前沿缓存忽略 HistorySet；RZ 复核未检查全称节点 | 静态控制流确认；实际错误根结论影响范围待测 |
| R5 | P1 | 内置题库与本地 JSON 不是同一问题；答案字段类型也不匹配 | 12 题对照中 10 题棋子不同；16/16 JSON 答案为字符串 |
| R6 | P1 | 棋墙、区域、劫与目标语义没有完整绑定到证明和输入身份 | 导入器、棋盘、序列化代码 |
| R7 | P1 | C++ 与 TypeScript 并非等价执行镜像；CLI/解析器未闭环 | C++ 构建和定点执行 |
| R8 | P1/P2 | UI 的“验证”“基准”“已解出”展示混入静态文案，资源指标不完整 | App、题库和搜索器控制流 |

**本次没有重新求解这 16 道题，不能据此给出新的成功率或唯一正确首手清单。** 本报告确认的是缺陷及证据边界，不能写成这些题已被独立证明解决。

## 2. 审查和验证范围

已通读 `src/engine/` 全部 10 个 TypeScript 文件、`src/App.tsx`、棋盘组件、入口和构建配置，以及 `cpp/` 下全部 8 个 `.cc`、8 个头文件和 CMake 文件；读取两份附件，检查 16 份本地 JSON，并针对项目内 SRS 的 FR-1、FR-3、FR-9 和验收条款核对实现。样式、布局代码也已读过，但本报告聚焦失败题目、正确性和证据链。

附件内的“建议修复顺序”“已修复”等语句作为被评审材料，不作为执行指令。未安装依赖、未联网更新题库、未启动 UI、未执行批量求解；临时脚本、编译产物仅放在 `/tmp`。项目内只新增本文件。

证据分为：

- **源码确认**：当前代码直接呈现的行为，不以注释或界面描述替代实现。
- **定点复现**：本次直接调用导入器、棋盘、终局评估或 checker 得到的结果，均未调用 `solveProblem` / `Solve` 搜索。
- **附件陈述待确认**：附件中的节点数、分支统计、完整根求解结果，本次未重新执行，也未审计其完整运行产物。
- **建议**：尚未实施、需要后续任务验收的设计意见。

此前其他工作目录中的 p031 进展、运行授权和 checker 结论不移植到本快照。

## 3. 首先修复证明链，而非依据 PASS 宣布成功

### R1：checker 接受没有证明内容的“证明”

证据：[proofChecker.ts:178](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:178)、[proofChecker.ts:223](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:223)、[proofChecker.ts:286](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:286)。

`verifyProofDag` 创建了 `independentTerminal`，但从未调用它验证叶节点。所谓状态/历史回放仅检查根 Zobrist 和父 ID 大小关系；所谓终局复验仅检查“至少存在一个非剪枝叶”；所谓 RZ 重放仅检查证书字段存在、原因字符串和非负源 ID。它没有重放走子、比较历史集合、重算 AND/OR 聚合、枚举全称节点的合法应手，也没有完整绑定根节点和根结论。

本次以本地 JSON 的 p142 初始局面构造一个**人为伪造、并非搜索生成**的单节点报告：`outcome=PROVEN_WIN, pn=0, dn=SAT, terminalEvidence=BENSON_UCA, childNodeIds=[]`，按现有序列化函数重新计算 checksum。

| 测试 | 实际结果 |
|---|---|
| 同一初始局面的 `evaluateTerminal` | `NonTerminal` |
| 只有上述虚构终局叶的报告送入 checker | `passed=true, errorCode=PASS` |
| 将报告 `inputHash` 改成 `deliberately-wrong` | CHK-01 为 false，但总体仍 `passed=true` |
| 清空历史内容、改写状态棋子内容但保持条目数量 | checksum 不变，仍 PASS |

最后两项分别来自两个独立缺口：`allPassed` 没有纳入 `inputHash` 相等条件；序列化仅记录 state/history 的数量，未覆盖其实际内容。它不是“能重算 Benson、只是共享了错误算法”，而是**根本没有执行这些语义复核**。

C++ 也存在同类问题：[proof_checker.cc:106](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/proof/proof_checker.cc:106) 只检查部分 PN/DN 和拓扑，`independent_terminal` 同样未使用，最后却声明全部历史和终局已验证。

建议：先建立可失败的语义 checker。必须独立从输入和证明恢复状态、合法着法、HistorySet、token、终局、全称覆盖及 RZ/TT 源证明闭包；任何审计项失败都不能总体 PASS。重新计算 checksum 是测试语义拒绝能力的必要步骤，不能只靠“篡改后 checksum 不匹配”证明 checker 有效。

### 证明文件本身还不自包含

证据：[proofChecker.ts:38](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/proofChecker.ts:38)、[dfpnSolver.ts:149](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts:149)、[proof_checker.cc:42](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/proof/proof_checker.cc:42)。

TypeScript 的 `lproofJson` 缺少完整 state/history 表、搜索区域、不死墙假设及部分复用边信息；C++ 的 JSON 更只含 context ID、根信息、初始哈希和节点数量，没有导出 DAG 内容。当前 checker 消费的是内存报告对象，并非从下载的证明文件恢复全部证据。

另有几个不能当作实现细节忽略的问题：

- `sha256-jcs:` 后实际是自定义 FNV 混合摘要拼接，只有 32 个十六进制字符；不是 SHA-256。`JSON.stringify` 也没有实现所宣称的 JCS 规范化。
- `inputHash` 只是初始棋盘 Zobrist，未绑定目标表达式、规则、区域和不死墙；改变这些内容可以改变命题而保持该哈希不变。
- `configFingerprint` 漏掉防守方 allow-ko、节点/深度/内存限制、排序和拓宽等配置，不能用于“同配置”性能比较。
- `artifactsComplete` 无条件设置为 true；SGF 输出是最多 20 步 PV，不是完整 AND/OR 解答树。

修好终局判定不会自动修好这条证据链。应把“文件完整性”“语义正确性”“输入身份相同”“规则假设可接受”分别验收。

## 4. 合法着法与终局：比排序更早的错误

### R2：固定的初始空点集合漏掉提子后的着法

证据：[studyLdRzCatalog.ts:254](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/studyLdRzCatalog.ts:254)、[position.ts:447](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/position.ts:447)、[dfpnSolver.ts:1088](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts:1088)。

`computeActiveTacticalRegion` 只有在 `!occupied.has(pt)` 时才加入区域。求解全过程复用这份数组。它因此表示“初始空点”，而不是“可搜索的棋盘区域”：初始有棋子的点即使后来被提空，也不会重新成为候选。

在真实 JSON 的 p162 上，顺序执行：

```text
B rs, W sp, B sr（提白 rr）, W sq
```

此时黑 `rr`：`playMove(rr).legal === true`，但 `generateLegalMoves(problem.regionCoords).includes(rr) === false`。这是一条无需完整搜索即可重现的缺陷。

遗漏自己的着法可能漏解；遗漏对手的合法反驳，则可能把不成立的全称命题错误证明为真。**把包围盒向左多扩几列并不能修好这一点，因为框内的初始占用点仍被排除了。** 建议区域描述固定几何点集合，当前空点与合法性在每个状态动态求交；特殊禁止点必须有独立且可导出的规则依据。

### R3：Benson 扩展存在明确不可靠证据

证据：[bensonUca.ts:201](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts:201)、[bensonUca.ts:383](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts:383)、[bensonUca.ts:542](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts:542)、[bensonUca.ts:759](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts:759)。

当前实现既合并非直接连通棋块，又给某些单腔体贡献两眼；合并后的气集合还参与眼位判断，并允许不死墙所属超级链跳过两眼淘汰。附件指出的方向成立，但“凡共享一口气就合并”略去了代码中的邻子/气数条件，精确描述应是：**这些局部条件不足以承担它所输出的无条件活证据。**

本次 p162 的直接证据更具体：

| 回放前缀 | 当前判定 | `rp/rq` 原始棋块的气 |
|---|---|---|
| `B rs, W sp, B sr` | Win / BENSON_UCA，局部眼 `rr`、`ss` | `rr,sq` |
| 再走 `W sq` | 仍 Win / BENSON_UCA | 仅 `rr` |
| 再走 `B pass, W rr` | `rq,rp` 被提，转为 NonTerminal | 无 |
| 另分支：`W sq` 后黑粘 `rr` | 合法，但转为 NonTerminal | 原“眼”已用于连接 |

这里对“无条件活”的质疑依据是**被标活棋块在己方停着时可被对方提走**，不是笼统要求 Win 在自己任意乱下后仍不变。后一种要求并不成立，本项目 SRS 也明确区分了这两件事。

这足以否定该叶子的 Benson 证据；由于目标表达式为 `qr,rp` 的 OR，不能仅凭提掉 `rp` 就推导整道题的所有黑方策略都失败，更不能据此宣称已完整证明 `rs` 必败。附件把“叶证据错误”“首手整体必败”合写为假证明时，应保留这个区分。

另三组回放也复现了附件指出的过早判活现象：

| 题目 | 回放 | 本次观测 | 证据限度 |
|---|---|---|---|
| p156 | `W nr, B mq, W ls` | 第 3 手 Win / BENSON_UCA；腔含 `or,ns,ms` 和黑 `os` | 原谱把 nr 所属路线标为失败；本次未穷尽 nr 的所有策略 |
| p147 | `W ms, B kn, W ks` | 第 3 手 Win / BENSON_UCA | 不能据此认证 ms；本次未另给完整杀棋证明 |
| p351 | `W lr, B kr, W ms, B os, W ns` | 第 5 手已 Win / BENSON_UCA | 直接否定附件一“提光前始终 NonTerminal”的描述；不等于证明此题一定死 |

建议先提供一个保守、可审计的 UCA 基线；超级链、见合、胀牯牛、对杀估值可以先用于排序或非零启发式数值。若要把某种棋形用于终局，必须给出明确前提与可独立检查的证据。**只把单腔体眼数改为 1 也不够**：超级链、vital 关系和不死墙豁免仍需分别处理。

## 5. 复用边界：BoardTT 谨慎不代表整条搜索安全

### R4a：前沿缓存直接绕过 HistorySet 隔离

证据：[dfpnSolver.ts:699](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts:699)、[dfpnSolver.ts:869](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts:869)。

`nodeFrontierCache` 的 key 只有 Zobrist、轮走、简单劫点、连续 pass 和 token mask，没有 HistorySet，也没有 hash 后的完整棋盘结构比较。缓存值却保存了合法子着法、pn/dn 定论、stateId、dagNodeId、剪枝证书。

同一棋盘可以通过不同历史到达，SSK 下合法应手不一定相同。当前路径可能在 BoardTT 因历史不同而未复用后，仍取得另一历史的 frontier；已定论孩子的数值可直接参与聚合，stateId 也可能继续引用旧 provenance。**不能只修 BoardTT，再宣称没有 GHI（历史交互）风险。**

这是源码确认的隔离缺陷；本次没有运行历史碰撞搜索来断言 16 题中的哪一个根结果已受污染。修复时应把前沿缓存纳入与证明复用相同的状态等价约束，或把跨历史内容严格降级为排序提示。

### R4b：RZ 复核在全称义务处直接成功

证据：[dfpnSolver.ts:488](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts:488)、[dfpn_solver.cc:88](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/search/dfpn_solver.cc:88)。

精确触发范围不是“所有 AND 节点”：OR→Win、AND→Loss 会递归尝试一个见证；**AND→Win 和 OR→Loss** 在源节点非叶、查询局面非终局时，直接 `return true`，不检查全部合法应手。递归到这一层就可能提前接受未复验的源证明。即使 Benson 完全正确，该缺口仍然存在。

此外，所谓 null-move 代表分支并不限于 pass，而是取首个符合条件的已证兄弟。任何兄弟替代都需要完整复核，不能依赖名称暗示其合法性。

C++ 还有独立的表更新问题：[transposition_table.cc:81](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/tt/transposition_table.cc:81) 仅按历史长度相同选择待更新条目，却更新证明字段、保留原历史；可能把新历史下的结论挂到旧历史上。其 [types.h:197](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/include/ldprover/core/types.h:197) 的 context 相等也只比较 token 数量，未比较 token 内容。这两项为源码发现，未声称已在当前题目触发。

## 6. 数据身份与规则契约需要一起修

### R5：两个来源加上实际导入类型错误

证据：[App.tsx:249](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx:249)、[studyLdRzCatalog.ts:283](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/studyLdRzCatalog.ts:283)。

本次逐项比较内置 12 题和同名 JSON：p031、p037、p040、p042、p057、p060、p088、p090、p101、p222 共 10 题的黑白棋子集合均不同，活动关键子也不同。p156、p162 的黑白棋子及活动关键子一致，但内置 rawsgf 被简化，不能当作原始棋谱副本。App 遇到已内置 ID 就直接选中，不读取本地 JSON。因此“选择同一个题号”不能确保复现同一道题。

内置 p222 尤其严重：黑方目标为 TOKILL，黑关键子为空，经 `|| 'qs'` 兜底后成为空点 qs；`buildProofContext` 又把不在黑子集合的点默认为白子。初始化 token mask 为 0，终局直接 Win / TOKENS_CAPTURED。本次只调用终局评估便确认此路径，不需要搜索。这不是 15 手题被加速解出。

**新增发现：全部 16 份本地 JSON 的 `answer_firstmove` 是字符串。** 接口却声明 `string[]`，解析器只接收数组，故直接导入它们时 `groundTruthFirstMoves=[]`、`expectedBestMoveSgf='pass'`。内置对象使用数组，掩盖了这个错误。它不直接决定搜索胜负，但会破坏题库比对、显示和基准判读；不是只有三道题的标签需要修。

建议将源 JSON 原文、规范化输入、人工修订、显示说明分开保存，并以稳定摘要关联。原始标签保留，修订需另列依据；不要为了让首手“对上”而改棋墙或关键子。

### R6：区域改变了游戏，不能只称作性能提示

证据：[studyLdRzCatalog.ts:207](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/studyLdRzCatalog.ts:207)、[position.ts:338](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/position.ts:338)、[bensonUca.ts:759](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts:759)。

导入器忽略 JSON 的 `region`，根据关键子和右下角假设另造包围盒，再把盒外初始棋子标记为不死墙。棋盘对含不死墙的整条链跳过提子，并允许其零气存留；终局也给予相关活棋豁免。与此同时，盒外空点仍参与气和眼区计算，却不允许搜索落子。

所以，这不只是“搜索少看几个点”。它改变了捕获、禁自杀的实际行为和对手可用着法，而证明文件又没有完整记录这些假设。扩大盒子还会改变哪些棋子不死，故两个区域大小的运行结果不宜直接作算法加速比较。附件一“裁区造成少气”的描述也不精确：当前实现仍在全盘上计算气，主要风险是不可填的外气、墙体豁免和缺失着法。

目标表达式方面，逗号被当成 OR，每个坐标单独成组，混合运算和目标点合法性没有严格校验。可以确认“本实现是 OR”，但在未核对数据集目标契约前，不能擅自改成全部存活。

劫方面，JSON 中做活方通常 `disallow_ko`、杀棋方 `allow_ko`，白先活题的允许方为黑。导入器丢弃双方字段，App 默认双方 false。应按颜色映射到 `rootAttacker=winningColor` 对应的角色，不能把 defender 固定理解为白。当前屏障只在特定定论见证上生效，不是禁着规则；存在一个 ko-dependent 分支，也不意味着任意 OR 根都永远不能由另一个无劫见证证成。

双 pass 方面，TypeScript 将未达到 UCA 的存活目标判作做活失败，C++ 则按 token 是否仍在盘上判活。哪种产品语义合适应先明确，并与本地 SRS、manifest 一致；“没有 UCA”不能直接翻译成普通棋理中的“死棋”。仅把 C++ 的 survival 规则复制到 TS 也不能自动解决双活/劫活识别。

## 7. C++ 工程与工作台执行路径存在实质差异

### R7：目前不能把工作台结果称作 C++ 引擎验收

证据：[App.tsx:147](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx:147)、[cppSourceRegistry.ts:6](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/cppSourceRegistry.ts:6)、[tprover_main.cc:17](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/cli/tprover_main.cc:17)、[problem_parser.cc:75](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/core/problem_parser.cc:75)。

App 在浏览器同步执行 TS `DfpnSolver`。C++ 文件通过 `?raw` 导入供浏览，并没有在该路径执行。源码标题中的“1:1 execution mirror”和报告里的 `solverVersion='...cxx20'` 不能替代实际实现身份。

本次 CMake Release 构建成功（AppleClang 21.0.0），但构建成功不等于功能完成：

| 定点检查 | 结果 |
|---|---|
| `tprover check --proof /tmp/nonexistent-ldprover-proof.json` | 退出 0，输出 `status: READY`，没有检查文件 |
| C++ parser 输入 `(;SZ[19]PL[B]AB[aa]AW[bb])` 和非空目标 | `valid=1`，却得到黑子 0、白子 0、token 0 |
| 5×5，黑 aa 为存活目标，连续双方 pass | C++ Win；TS Loss |

双 pass 差异来自 [benson_uca.cc:261](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/cpp/src/terminal/benson_uca.cc:261) 和 [bensonUca.ts:930](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts:930)。C++ 没有 TS 的超级链/不死墙实现，搜索也没有 TS 的 persistent frontier；C++ `enable_pattern_tt` 只在配置声明中出现，没有接入搜索查存路径。两端不能互相背书。

建议明确当前交付是工作台原型还是可独立使用的 C++ prover。若选后者，应先完成 CLI 输入→规范化→求解→导出→独立进程 check 的闭环，并给实现分别标版本。不要在两套语义未对齐时同时优化两个求解器。

## 8. 对两份附件中逐题结论的复核

以下“原谱首手”只表示本地 rawsgf 对应分支的标记，经初始棋子集合验证坐标变换后得到；**不是本次独立根证明，也不保证唯一性**。本次用保留父路径的 SGF 树解析检查 16 题、枚举 8 种棋盘对称；15 题存在唯一的零缺失初始棋子映射（raw 棋子为 masked 局面子集），p351 另有一子差异。

| 题目 | 本次可确认的判断 | 对附件结论的处理 |
|---|---|---|
| p031 | 内置与 JSON 不同；原谱标记首手 sr | 附件二 WIN/sr 为待确认的完整搜索结果 |
| p037 | 内置与 JSON 不同；原谱标记首手 qs | 同上，不认定内部 PASS 已建立可靠证明 |
| p040 | 原谱正解分支 `B[da]→ps`；失败图 `B[db]→pr` | 同意原标签与原谱冲突；“唯一正解”“严格形式化证明”未获本次认证 |
| p042 | 内置与 JSON 不同；本地答案字符串 os，原谱正解分支 os | 不能采用附件一“原题已解出”作为基线 |
| p057 | 内置与 JSON 不同；本地答案 rs | 未重跑根搜索；题库标签不能自行充当证明 |
| p060 | 内置与 JSON 不同；原谱标记首手 rs | 已解出/未解出的差异应先绑定输入 |
| p088 | 内置与 JSON 不同；原谱第一正解路径从 rr 开始 | 881 节点、补点即修复等陈述待同输入复现 |
| p090 | 内置与 JSON 不同；原谱 rr 路线与内置拷贝 PV 不同 | 固定 rr 后 675 节点及“只差排序”均待确认 |
| p098 | 胜方黑、白先，确为 AND 根；答案字符串 tt；rawsgf 包含参考图和双劫循环说明 | 不能以 12 条 PV 的节点估算推导完整全称证明成本；8,000+ 无已验证依据 |
| p101 | 内置与 JSON 不同；原谱 qs 路线包含弃子转换 | 1,753 节点和已解决状态不作验收结论；需检查提子后坐标回填 |
| p222 | 内置命题错误并可根终局 Win；JSON 黑先活，原谱首手 rr | 先恢复正确命题；15 手终局只是一条路径，非根全称证明 |
| p142 | 原谱首手是 `B[ai]`；唯一零缺失变换 `(x,y)→(18−y,18−x)` 得 ks | 否定附件一的 ls；支持附件二的坐标更正，尚未证明 ks 在当前规则下必胜 |
| p147 | 原谱正解首手 `W[ea]→os`；`W[ga]→ms` 是后续手 | 否定“引擎找到 ms 就纠正标签”；复现了 ms 路线上的不可靠终局判定 |
| p156 | 原谱 lr 正解；`W[fb]→nr` 的路线标为失败3，随后 `B[gc]→mq` | 不能以当前 checker 把 nr 认证为等价活棋手 |
| p162 | 原谱首手 sr，完整正解路径 13 手；复现 rs 路线的终局与着法生成问题 | 不能归结为仅左翼盒子缺点，更不能仅扩区域后宣告修好 |
| p351 | masked 局面在 `lr kr ms os ns` 第 5 手已判 Win；最优 D8 匹配仍缺 raw 白 dd 对应的 pp | 否定“提光前始终 NonTerminal”；原图与 masked 图差异需单独解释 |

关键坐标核验结果：

```text
p142：ks is ns js ls ms kr or oq os pr
p147：os ns ms ps ks                 （原谱正解1）
p156：lr or nq nn ls js ns           （原谱正解1）
p162：sr rs sq ms ns qs ks ps os sp ls ss rq
p222：rr rp ro so rq sp sq sn qq qs ps rs ss sr qr
```

p142 中 ks 按当前代码跳过 I 的人类列标为 **L1**；ls 为 M1。附件一把 ls 称作 L1，也混淆了 SGF 和人类坐标。

当前 `extractReferencePvFromRawSgf` 的正则不能保留嵌套树的父路径，且固定使用 180° 变换。p162 可抽到深层子分支而丢掉前 10 手；p351 的原谱主序列没有 `(;B...`/`(;W...` 形式的子树，也不适合这条提取路径。应使用真正的 SGF 树、完整 setup/轮走校验，并处理多解、参考图、修改记录和变换歧义。

p351 的差异不能隐去：raw 白 `dd` 在最优反对角映射下对应 `pp`，但 masked 的 pp 为空；其转换字段没有直接给出这颗白子的移除解释。本次记录为输入转换待确认，不宣称已查明数据集生成脚本根因。

## 9. 对“搜索结构才是根因”的保留意见

附件二关于分支大、pn/dn 统一初值、拓宽较快的观察可以成为性能研究线索，但以下推论应收窄。

1. **有限预算未解不等于加预算永远无效。** “4 万节点仍 UNKNOWN”最多说明被测配置在该预算下未成功；不能证明一切更大预算都无效。修复输入和证明问题之前，额外预算确实不值得作为首要措施，但这是工程优先级判断。
2. **pn/dn 初值 1 并不单独构成错误。** 它在本实现的大分支环境中可能让排序效果受限，需要测量首次有效终局深度、每层扩展数、重复访问数和完整根义务成本。`b^(d/2)` 只能是很粗的模型，不能据此推导这些题的必需节点数。
3. **扩窗条件有完整性目的。** 当前代码用窗口外每个隐式孩子的代价 1 参与聚合；当窗口内最佳值更大时扩窗，与此表示方式一致。不能只删掉 `bestMetric>1` 的条件，否则可能饥饿未探索分支或破坏阈值逻辑。建议把显式候选选择策略和隐式未展开义务一起设计、一起测。
4. **一条 PV 的终局不等于根证明深度。** AND 根必须覆盖所有合法白应手，OR 胜方也需覆盖所选策略下所有反驳；只固定首手后快速判赢，不能解释完整根为何失败，更不能忽略 RZ 复验缺口。
5. **“非 Benson”不是静态死亡判据。** 不建议把“眼位空间≤3”或简化对杀气数公式直接当 Loss/Win 叶；至少要排除连接、吃子扩眼、扑入、劫、共气和双活等例外，且让 checker 验证相应证书。暂作启发式更合适。
6. **失败图标签只适合作为告警线索。** 某条棋谱分支失败可能由于后续失误，未必意味着那个首手的所有策略均败；masked 图、目标 OR 和规则也可能不同。应把具备完整反驳且身份一致的反例设成硬回归，不能把所有“失败图首手”机械视为必败真值。

另有两个实际性能/观测问题：TS 搜索、排序、棋块泛洪及历史复制在 React `useMemo` 中同步执行，批量测试同步遍历；提高预算会明显加重主线程阻塞。`memoryBudgetMb` / C++ `memory_budget_bytes` 目前没有资源检查实现，也没有求解超时检查路径；报告 `timeMs` 只计到序列化前，不能当完整导出+checker 的端到端时间。

## 10. UI 和基准不能替代验证

证据：[App.tsx:401](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx:401)、[App.tsx:336](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx:336)、[App.tsx:760](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx:760)、[problemsCatalog.ts:250](/Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/problemsCatalog.ts:250)。

“契约测试器”根据 preset 直接返回预写的通过/拒绝文案，没有调用真实解析器；真实 TS 解析又允许默认值，故 UI 显示“空关键子不使用默认值”不能证明该保护存在。

题目列表的 PROVEN 来源于 `expectedOutcome`，不是本次 checker 成功。批量页展示结果和 checker 状态，却未把它们与版本化期望值作机器断言。默认题库是 12 个 study 条目 + 7 个 SRS 条目；四个其余真实题须动态加载才进入 `allProblems`，所以“全量”依赖当前会话。

“7/7 求解通过”还需定义分母与成功含义：p005 默认期望 UNKNOWN/ko_dependent，p007 期望 PROVEN_LOSS，不能理解为七道全部 PROVEN_WIN；checker 对 UNKNOWN 明确失败也可能是预期行为。当前没有 `test` 脚本或 CTest 回归套件来支撑这一验收叙述。

棋盘手动试下直接调用 `playMove`，可以走到搜索 mask 不允许的点；PV 回放忽略落子失败返回值，棋盘图层与步号又取根报告。它们有助于诊断，但不能将“能在 UI 回放/显示活棋”当作求解树合法覆盖的证据。

## 11. 建议实施次序及验收条件

本节仅给出后续建议，本次不执行修复。

| 顺序 | 工作 | 可审查的完成条件 |
|---|---|---|
| 1 | 冻结真实输入，校正导入与状态模型 | 16 题原文/规范化摘要；内置与 JSON 一致；字符串答案保留；空点目标和非法表达式拒绝；提子后的区域内交叉点恢复候选；规则及墙体假设显式记录 |
| 2 | 建立保守终局和真正独立的 checker | p162 误判叶被拒；虚构终局、错误 hash、删 AND 应手、改历史、伪造 RZ/TT 闭包即使重算 checksum 也必须失败；下载证书可在独立进程完整检查 |
| 3 | 统一历史隔离和 TS/C++ 语义 | frontier/TT/RZ 均在完整输入及历史下校验；两种历史同棋盘的反例；双 pass/目标/劫/墙规则逐项一致，或明确声明两种不同模式 |
| 4 | 建立有身份的覆盖率基线 | 同题、同规则、同区域、同预算；按正确证成、正确证伪、UNKNOWN、拒题、checker 拒绝分别计数；记录源码/实现/配置摘要和实际资源 |
| 5 | 在可靠基线上研究搜索效率 | 逐项消融排序、启发式 pn/dn、拓宽、复用和内存结构；保持完整性条件；性能提升与通过 checker 的根结果同时报告 |

若只派发一个下一步任务，建议是：**“真实输入与合法着法基线修复”**。范围限定为统一 16 题输入、修正答案类型、目标与规则校验、分离几何区域和初始空点、固化输入摘要；交付数据差异清单和有限回归结果。停止点为输入身份与合法着法一致性通过，不调整 Benson 判活，不扩预算追求解题率，不把现有 PASS 升格为已证明。这会为 checker 和终局修复提供稳定对象。

仍需决定的产品契约：普通死活标签与 UCA 目标的关系、双活/双 pass 定义、多目标 OR/AND 解释、不死墙是否为题目规则，以及 TS 原型与 C++ 引擎哪一个是当前验收主体。它们应形成版本化规范，而不是逐题靠“调到答案一致”确定。

## 12. 本次验证记录与可复核步骤

### 12.1 执行情况

- Node：v24.18.0。使用 Node 临时模块加载 hook 对 TS 去类型并转换 enum；仅移除类型导入，未替换任何引擎计算逻辑。初次加载因源码中接口以普通 import 导入而失败，调整临时 loader 后运行成功；这不是项目编译失败结论。
- 数据核验：12 个内置条目逐一比较黑白坐标和关键子；16 份 JSON 检查字段类型；16 份 rawsgf 解析树并比较 D8 变换。
- 棋盘回放：p162 两条分支、p156、p147、p351，共 22 次指定着法调用，另重放 p162 前 3 手确认标活集合包含 rp/rq（合计 25 次）；未展开搜索树。
- checker：3 次人为构造报告的拒绝能力测试；结果均错误 PASS，不属于真实求解证书验收。
- C++：`cmake -S cpp -B /tmp/ldprover-review-cpp-build -DCMAKE_BUILD_TYPE=Release`；`cmake --build /tmp/ldprover-review-cpp-build -j 2` 成功，存在未使用变量/参数及重复库警告。运行 1 个小型 parser/双 pass 探针和 1 次无效文件 CLI 检查。
- 两端双 pass 对照：5×5 单个黑 aa、目标 aa、TOLIVE、SSK，两次 pass；TS Loss，C++ Win。
- 实际 solver 根搜索次数 **0**；批量题库求解次数 **0**。未测 2,500/10,000/40,000 节点下的成功率、搜索最大深度或运行时峰值内存，也未测前端生产构建。

### 12.2 关键复核步骤

**候选遗漏与终局反例**：用 `parseStudyLdRzJsonToProblemSpec` 原样导入本地 p162 JSON，按 App 默认配置创建 context/position。逐手检查 `playMove` 返回合法；在 `rs sp sr sq` 后先查 `generateLegalMoves(regionCoords)` 是否含 rr，再在克隆位置直接 `playMove(rr)`。另从第 3 手后的克隆走 `sq pass rr`，核对捕获数组为 `rq,rp`，并检查第 3 手标活集合确实包含这两子。继续回放用于审查提前终止的可靠性，不是在宣称正规搜索应越过已接受的终局继续扩展。

**checker 伪造测试核心**：以 p142 初始位置创建单个 nodeId/stateId/historyId=0 的叶，`pn=0,dn=1073741823,outcome=PROVEN_WIN,terminalEvidence=BENSON_UCA`；报告根指向它，stateTable 根 Zobrist 与输入相同；调用 `serializeLProofJson` 获取 checksum 再 `verifyProofDag`。当前 checker 返回 PASS，而真实 `evaluateTerminal` 返回 NonTerminal。随后仅改 `inputHash`，可见 CHK-01=false、总体 passed=true。再恢复 hash、清空 historyTable[0] 并改 stateTable[0] 棋子内容，数量不变时仍 PASS。

**SGF 映射**：解析根 AB/AW，并保留完整父路径；对八种 D8 变换分别计算原始黑白棋子不在 masked 同色棋子集合中的数量。p142 反对角变换唯一零缺失；p147 180° 变换唯一零缺失。使用正解注释所在路径的第一手，而不是注释附近任意一手或最内层子树首手。

临时复核文件：`/tmp/ldprover-review-probes.mjs`、`/tmp/ldprover-review-probes.json`、`/tmp/ldprover-review-loader.mjs`、`/tmp/ldprover-review-sgf.py`、`/tmp/ldprover-review-sgf.json`、`/tmp/ldprover-review-cpp-probe.cc`。这些仅供当前会话追查，核心输入、步骤、输出已保存在本报告中，不依赖临时文件长期存在。

## 13. 快照身份与交付边界

本目录未发现 Git 元数据，故不伪造 commit ID。读取快照时，对 60 个既有文件计算 SHA-256（排除 `.env` 和 Git 内部文件）；以下为关键文件摘要。摘要清单的排序紧凑 JSON 的 SHA-256 为 `7c26eec4cdec5a47de6f99d200a08e78251eb6ea8d507dbc28ff45fdccbae6a3`。

| 文件 | SHA-256 |
|---|---|
| `src/engine/dfpnSolver.ts` | `49a8519f420bfba64035f7f3092a4444718114229dfefad32cbb583c1e136a98` |
| `src/engine/bensonUca.ts` | `3dda8ab1bfe3fb58d209c5c646975b83458bdc080d46ed4b322b8b4fee135a43` |
| `src/engine/proofChecker.ts` | `c76b23fd13d8b2ba6c0db9dc0860756294295fba8d08f9d27baf304a4277a7f3` |
| `src/engine/studyLdRzCatalog.ts` | `7251ec092f93b874e9a72ee59407408ad00ce474612658074c08de86c8513209` |
| `src/engine/position.ts` | `2d528acea8d9010920b6a554458c772531041fb956bf1dfc22a5c2e41498ad30` |
| `src/App.tsx` | `6c999f8425fbb97b4e463dee3a3d07366dcbcdf093f4c70afc330a728b50010f` |
| `cpp/src/search/dfpn_solver.cc` | `2f7bef524cf044bcffca44b1ec1b61fb0568e8fb6d88e5c1ff84358397071dcc` |
| `cpp/src/proof/proof_checker.cc` | `c83ee53ae6a63002d7a28c2814e9be6e32cb0e9ae1f8270af34e831c2b323616` |

附件摘要：

- `failed_problem.md`：`258c5975e213b5aa503e63fbff69d38163c6872355c52805dc3b0171e2f2e565`
- `unresolved_root_cause_report.md`：`1771083db8395410da575478b75cc05293d8b84c98126c9f7f2db5d1a01324c9`

交付前已复核 60 个既有文件的摘要，变化/删除数为 0；唯一新增项为本报告。报告中 35 个源码链接的路径与行号均已检查有效。

交付只包含本独立评审文件。原代码、数据及配置均保留；未把建议实施成补丁，也未将附件的运行结果改写为本次实测结论。
