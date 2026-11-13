# LDProver 未解决题目根因分析报告

> [!NOTE]
> 分析基于当前代码（`src/engine/*.ts`）和 `public/tsumego/*.json` 原始数据，并实际跑了求解器做复现（配置与 App 默认一致：`maxNodes=2500, wideningBaseK=8, pattern-tt, SSK, attackerAllowKo=false, defenderAllowKo=false`）。
> 复现脚本：[run.ts](file:///Users/go4ai/.gemini/antigravity/brain/409858d5-d8bb-46a6-96b1-acd16ced4db3/scratch/run.ts)（求解）、[leaf.ts](file:///Users/go4ai/.gemini/antigravity/brain/409858d5-d8bb-46a6-96b1-acd16ced4db3/scratch/leaf.ts)（逐手回放并打印 Benson 判定）。

## 0. 结论速览

`failed_problem.md` 把未解决的原因主要归结为"节点预算不够 / 包围盒截断 / 缺对杀评估"。实测下来，**真正的原因是另外四类，而且其中有几条结论本身就不成立**：

| # | 根因 | 影响 |
|---|---|---|
| A | **App 内置题库的局面是另一套数据**：12 道里有 10 道的棋子、关键子和 JSON 原题不一致 | p031–p101、p222 等在 UI 里解的不是真题 |
| B | **Benson 终局判定不可靠**：超级链合并 + "多虎口 / 4~6 格腔 = 2 眼"之类的启发式会把没活的棋判成活 | p156 `nr`、p162 `rs`、p147 `ms` 是**假证明**；p351 的静态判定也偏乐观 |
| C | **搜索结构撑不住，加预算没用**：分支约 40–57，pn/dn 全部初始化为 1，节点数到 1 万时深度只有 3~4、终局命中数是 0 | p090、p098、p222、p142、p351 以及（真实数据下的）p042/p057/p060/p088/p101 |
| D | **数据标签 / 文档本身有错**：p142、p147 的"真解"推导错了，报告里多道题的 PV 跟 rawsgf 对不上 | 结论失真 |

## 1. 实测结果（真实 JSON，2500 节点）

| 题目 | 结果 | best | 题库 | 判读 |
|---|---|---|---|---|
| p031 / p037 | WIN | sr / qs | sr / qs | ✅ |
| p040 | WIN | ps | pr | ✅（`pr` 确实是原谱「失敗圖2」，这一条报告说对了） |
| p042 / p057 / p060 / p088 / p101 | UNKNOWN | – | – | ❌ 报告里写"已解出"，用真实数据复现不了 |
| p090 / p098 / p222 / p142 / p351 | UNKNOWN | – | – | ❌ 到 4 万节点也没解出（见 §4） |
| p147 | WIN | **ms** | oa | ⚠️ 假证明，真解是 `os`（见 §3、§5） |
| p156 | WIN | **nr** | lr | ⚠️ 假证明，`nr` 是原谱「失敗3」 |
| p162 | WIN | **rs** | sr | ⚠️ 假证明，问题出在 Benson，不是"区域截断" |

## 2. 根因 A：UI 内置题库和 JSON 原题不一致

在 [App.tsx:255-263](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/App.tsx#L255-L263) 里，只要题号已经在内置目录中，就**直接用内置条目，不会读取 `public/tsumego/*.json`**。但 [studyLdRzCatalog.ts](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/studyLdRzCatalog.ts#L361) 里硬编码的 `masked_sgf_str` 和 JSON 对比如下：

- p031、p037、p040、p042、p057、p060、p088、p090、p101、p222：**黑白子和关键子都不同**（例：p090 的 JSON 关键子是 `pq`，内置是 `pr,qo`）。
- 内置 p222 被写成了"黑先**杀**、白关键子 `pr,qq`"，而 JSON 是"黑先活、关键子 `pr,qo`"。再加上 [studyLdRzCatalog.ts:334](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/studyLdRzCatalog.ts#L334) 的 `black_crucial_stone || 'qs'` 兜底，黑方关键子变成了空点 `qs`，于是**根节点直接判 WIN、best=pass、只用 1 个节点**（复现过）。
- 内置 p090 的 rawsgf 是从 p088 拷过来的；`extractReferencePvFromRawSgf` 的正则会匹配到最内层分支，p162 的参考 PV 因此取到了第 11 手之后的子分支。

结果是：报告里的节点数（881、675、1753 等）在两套数据上都复现不了，UI 展示的"已解出 / 诊断"跟真题对应不上。

## 3. 根因 B：Benson 终局判定会误判活棋（假证明）

[bensonUca.ts](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts) 里在经典 Benson 之上加了几条启发式，导致它判出的"无条件活"并不总是真的活：

1. **超级链合并**（[L542-L639](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts#L542-L639)）：几块棋只要共享一口气、或者有 ≥2 口公气，就被当成一块。同一个点**既算连接点又算眼**，被重复计算了。
2. **多虎口真眼**（[L383-L402](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts#L383-L402)）：没有考虑组成这条超级链的某一小块只有 2 气、可以被叫吃的情况。
3. **单个腔体记 2 眼**（Case 3/4、4~6 格纯空腔，[L201-L242](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts#L201-L242)、[L455-L496](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts#L455-L496)）：不管腔内敌子还有几口气、对方能不能点进去，一律记 2 眼。

逐题回放的证据：

| 题目 | 引擎给出的 PV | Benson 判活的依据 | 实际情况 |
|---|---|---|---|
| p162 | B rs, W sp, B sr（提 rr） | 眼 {rr}、{ss} | `rp-rq` 只有 `sq/rr` 两口气，白 `sq` 叫吃后黑只能粘 `rr`，`rr` 这只眼就没了 |
| p156 | W nr, B mq（原谱的反驳手）, W ls | 腔 {or,ns,ms}+黑 os，记 2 眼 | 黑 os 还有 2 口气，这不是两只眼；而 `nr` 在原谱里是「失敗3」 |
| p147 | W ms, B kn, W ks | 眼 {np}、{ls} | `no` 是孤子，黑可以叫吃它，逼白粘 `np` 后眼被破 |
| p351 | W lr, B kr, W ms, B os, W ns | 腔 {nq,nr,mr}+黑 np，记 2 眼 | 第 5 手就判活，比原谱结束早；报告里"提光前 Benson 一直是 NonTerminal"的说法不成立 |

另外，RZ 剪枝复核 `revalidateSourceProofOnQueryState` 在 AND 节点直接 `return true`（[dfpnSolver.ts:540](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts#L540)），并没有真正复核，假证明会被继续传播。

> [!WARNING]
> Benson 一旦误判，后面的 proof checker 只校验 DAG 的结构和校验和，**拦不住**错误结论。所以"PROVEN_WIN + checker 通过"不代表答案正确。

## 4. 根因 C：搜索结构问题，不是预算问题

统计数据（1 万节点）：

| 题目 | 平均分支数 | 最大深度 | 非平凡终局命中 | 4 万节点结果 |
|---|---|---|---|---|
| p090 | 39 | 4 | 0（只有 1 次双 pass） | UNKNOWN |
| p098 | 38 | 4 | 0 | UNKNOWN |
| p222 | 49 | 3 | 0 | UNKNOWN |
| p351 | 47 | 4 | 0 | UNKNOWN |
| p142 | 57 | 4 | 0 | UNKNOWN |

`uniq ≈ nodes`，说明节点基本都是新节点，重复进入不是瓶颈。具体原因：

1. **pn/dn 全部初始化为 1，没有任何启发式初值**（[dfpnSolver.ts:703-720](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts#L703-L720)）。b≈40 时搜索接近宽度优先，要证到深度 d，量级约 b^(d/2)。原谱终局 Benson 需要：p098 8 手、p222 15 手、p351 5 手，p090/p142 的原谱终局 Benson **根本不判活**（实测是 NonTerminal）。
2. **渐进拓宽基本失效**：只要窗口内最好的子节点 pn>1 就扩窗（[L1045-L1049](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts#L1045-L1049)），每个子节点展开一次后窗口就从 8 扩到全部。
3. **胜负判定不对称**：做活方要等完全封闭的 Benson 两眼，杀棋方必须真的把关键子提掉，中间没有"已死"的静态判定。错误首手的 dn 收敛不了；正确首手又要证明对方 40 种应手（含区域内无意义的手和 pass）全部不行。
4. **pass 和双活**：双 pass 时只看 Benson（[bensonUca.ts:930](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/bensonUca.ts#L930)），**双活一律算做活失败**。p098 参考图里的"胀牯牛 / 双劫循环"本来就很难判。
5. **区域外的空点**：不能落子，但仍然算气、参与 Benson 的区域划分，凡是挨着区域边界的棋块都会多出"永远紧不掉"的外气（p142 的区域扩到第 f 列，外壳子不再是不死子）。
6. **劫的配置和数据集相反**：数据集是 `white_ko_rule=allow_ko`（杀棋方可以打劫），App 却是 `defenderAllowKo=false`。p090 的失败图里有劫，p098 有双劫循环，劫依赖的子节点会被标成 `koDependent`，pn/dn 卡在 SAT/2，这道题就再也证不出来。
7. **关键子是"任一存活"语义**：`a,b,c` 被解析成"任一存活"（Disjunction，[dfpnSolver.ts:231](file:///Users/go4ai/antigravity/LDProver-—-C++20-Go-Life-and-Death-Prover-&-Verification-Workbench/src/engine/dfpnSolver.ts#L231)）。在 p156 里这让弃掉 `jq` 的做活也能成立，需要和数据集的定义核对。

所以报告里"p098 需要 8000+ 节点、p351 需要 >6000 节点、p222 只是深度受限"的估计都不成立。**加预算不会解决问题。**

## 5. 根因 D：对报告中错误结论的更正

| 条目 | 报告的说法 | 实际（rawsgf 自动匹配 D8 变换后） |
|---|---|---|
| p142 | 原谱首手 `B[ha]`，真解 `ls` | 原谱首手是 `B[ai]N[下邊]`，变换为 (18−y, 18−x)，得到 **`ks`**（L1）。题库的 `ka` 是行翻转写错了 |
| p147 | `W[ga]`→`ms`，引擎"纠正了"标签 | 原谱首手是 `W[ea]N[右下]`→**`os`**，题库 `oa` 同样是行翻转错误；引擎的 `ms` 是假证明（§3） |
| p156 | `nr` 是"等价活棋手" | `nr` 是原谱「失敗3」，反驳手为 `B[mq]` |
| p162 | `B[rs]` 伪解来自区域截断 | 来自 Benson 超级链 / 多虎口误判（§3）；原谱 PV 应为 sr rs sq ms ns qs ks ps os sp ls ss rq |
| p222 | PV `rr sq qs sr…` | 实际为 rr rp ro so rq sp sq sn qq qs ps rs ss sr qr |
| p040 | `pr` 是失敗圖2，真解 `ps` | ✅ 正确，引擎在真实数据上也证出了 `ps` |

## 6. 建议修复顺序

1. **先统一数据源**：内置目录改为从 JSON 生成，删掉硬编码的局面；去掉 `|| 'qs'` 兜底；参考 PV 改成按 SGF 树解析，并自动识别 D8 变换。
2. **让 Benson 回到可靠的版本**：终局只用经典 Benson（不做超级链合并，单个区域最多记 1 眼），启发式的眼形判断只用来给 pn/dn 定初值或排序，不再作为终局证据；修好 AND 节点的 RZ 复核。
3. **改搜索结构**：pn/dn 按应手数或眼形潜力做启发式初始化；修正扩窗条件；补上"已死"的静态判定（例如眼位空间 ≤3 且对方先手可以点杀），以及对杀气数估值（作为启发式，不当作证明）。
4. **对齐数据集语义**：ko 规则按 `*_ko_rule` 逐题设置；明确关键子是"全部存活"还是"任一存活"；双活怎么算胜负。
5. **回归测试**：用 rawsgf 里标了 N[失敗…] 的首手做反例测试，引擎证出失败首手 WIN 就判为 bug（p156 `nr` 能直接当用例）。
