# LDProver 独立复审 R8

2026-11-21。评审提交为 `62380fbc9059a78817f66e600f5f9f796e9d9b2e`，与本次只读查询的 GitHub main 一致。对照版本为 R7 的 `3500133`。项目只新增本报告。

## 验收意见

**R7 中导致空区域证书不能往返、NULL_MOVE 败证被 TS 拒绝、等价 Unicode 转义被 C++ 拒绝的三个原始反例均已关闭。** TS 版本化回归 **130/130**，原生 C++20 Release 全新构建后 CTest **1/1**，目标内部 **84/84**。对正常题库的 13 份证明逐份交叉检查，两端均 PASS，输入摘要和规范 DAG 摘要逐份相等。

**外部原题契约仍有一个 P1。** 一道被两端接受的两子棋题，省略 `region` 后，TS 证出黑杀失败，C++ 证出黑杀成功，两份结果分别通过了本端校验。根因在原题载入时对区域和不朽墙的推导。此差异在 R7 也可复现。本轮修复了证书对三态的表达，尚未统一这一原题入口。

## 1. P1　同一份原题 JSON 在工作台与 CLI 上产生相反的已证结论

使用如下完整题面。棋盘左上角白 aa 被黑 ab 紧住，黑先，目标是提白 aa。两端均接受输入，TS 校验器返回 FR1-OK。

```json
{
  "masked_sgf_str": "(;GM[1]FF[4]SZ[19]PL[B]AB[ab]AW[aa])",
  "winning_color": "B",
  "turn_color": "B",
  "black_search_goal": "TOKILL",
  "white_search_goal": "TOLIVE",
  "black_crucial_stone": "aa",
  "white_crucial_stone": "aa",
  "black_ko_rule": "allow_ko",
  "white_ko_rule": "allow_ko"
}
```

| 用相同原题分别进入两端 | TS 工作台题目解析器 → 求解器 | C++ 原生 CLI | 证书在对端绑定同一原题 |
|---|---|---|---|
| 上述 JSON，省略 region，SGF 无 MA | 359 点区域，aa、ab 均为不朽墙。黑 ba 提不到 aa，**PROVEN_LOSS，1 节点** | 无区域限制、无墙。黑 ba 直接提 aa，**PROVEN_WIN，2 节点** | 两个方向均 LP-P01 |
| 仅加 `"region":"aa,ab,ba"` | 无墙，**PROVEN_WIN，ba，2 节点** | 无墙，**PROVEN_WIN，ba，2 节点** | 两个方向均 PASS |

第一行的两份证书若仅作自包含文件检查，对端也都 PASS；指定原题才发现差异。这样既排除了棋力和搜索预算因素，也解释了只做“求解 → 本端复验”为何会漏检。另以 R4 的 p001 同型原题交叉验证，省略 region 和写空串均触发绑定差异；恢复原非空 region 后双向绑定通过。

**原因。** 在 `src/engine/studyLdRzCatalog.ts:568`，没有原始 region 或 MA 标记时，TS 按棋盘绝对行列把已有棋子划为不朽墙；在第 617 行又把回退矩形用作合法着法区。C++ 在 `cpp/src/core/problem_parser.cc:618` 仅在实际读到点时设置掩码，在第 681 行依据该掩码推导墙。上例中的目标 aa 因而只在 TS 端变成不朽子。用 R7 的 TS 源码与已编译原生程序复测，仍得到同一对相反结论，这两处解析代码本轮没有改动。

**建议验收标准。** 给原题格式明确规定 region 缺失、空串、SGF 有 MA、显式非空四种情形，各端解析后先比较区域是否存在、有效坐标和不朽墙，再做根结论及双向外部绑定。若约定缺省为无限制，应去除这一路径中改变证明命题的矩形和墙推断；若题库确需特定回退模型，应将其明确写入契约并由两端共同实现。这道两子题可直接用作版本化测试。

## 2. R7 三项原反例的复核

| 场景 | 本轮实测 |
|---|---|
| p001 显式空掩码 | 原生着法生成器仅枚举 PASS；无掩码对照枚举 350 手。TS 与 C++ 分别在 **3 节点**证出该变体 PROVEN_LOSS。原生内存 → 原生导出 → 双端文件复核通过；TS 完整与紧凑编码均通过，两个 checker 对同一文件的规范摘要一致。 |
| 将上述败证改标成无限制，重算输入摘要 | 完整和紧凑两种编码均被两端以 LP-N22 拒绝。 |
| 将 p001 的 ba 胜证改标成显式空区域 | 两端都拒绝。紧凑编码均为 LP-R02；完整编码 **TS 为 LP-R02，C++ 为 LP-S11**。此次对照同时将 rawRegionPointCount 设为 0。 |
| p007 全称败根，bestMove=-2 | bestMoveSgf 为空字符串或 JSON null 时，两种编码均双端 PASS，规范摘要逐文件相同。搭配字符串 pass、ba 时均 LP-R02；数值、布尔、数组标签均 LP-J02。 |
| Unicode 字符串与键排序 | 对 contextId 为“围棋🎯”的同一文件，仅将 🎯 改写成代理对转义并保留原摘要，双端均 PASS、两种摘要都一致。文件同时含 🎯 与 U+E000 两个额外键，覆盖 UTF-16 与 UTF-8 排序会给出不同先后的情形。孤立高、低代理项分别得到双端 LP-J01。键排序依据见 [RFC 8785 §3.2.3](https://www.rfc-editor.org/rfc/rfc8785#section-3.2.3)。 |

**诊断码差异的范围。** 原生完整文件先重放状态表，ba 行在 `cpp/src/proof/proof_checker.cc:2615` 已触发区域转移错误；紧凑文件省去状态表，才首先命中根见证检查。原生版本化测试在 `cpp/tests/r5_regression_test.cc:448` 使用的是紧凑反例。两端均未放行越区证明。若承诺错误码一致，应明确多项违规时哪项优先，并给两个 checker 喂同一份完整文件；若协议只承诺拒绝，则应相应调整验收说明。

## 3. P2　矛盾区域在文件入口被拒绝，在 TS 对象入口会被静默改写

对文件中的 `hasRegionHint=false` 加非空 `regionCoords` 重新签摘要，TS 和 C++ 都返回 LP-J02。对 TS 的公开题目对象，以 p001 设置同样矛盾的 `hasRegionHint=false, regionCoords=[aa]`，走 `solveProblem` 后却得到 **PROVEN_WIN / ba**。导出文件已经变为 `false, []`，用原矛盾题目对象绑定复核仍为 PASS。另在内存报告上保留 `false, [aa]`，实际 `verifyProofDag` 也返回 PASS。

`src/engine/dfpnSolver.ts:152` 优先采用布尔值并在输出时清空坐标，`src/engine/proofChecker.ts:289` 与外部绑定分支也按同一优先级忽略坐标。因此，严格拒绝只在原始文件矛盾仍然可见时生效。建议在题目对象、内存报告和外部绑定对象上先检查字段是否相容，再做规范化与搜索。还可补充类型对照：两端当前都会将文件中字符串类型的 hasRegionHint 当作缺失字段，改按坐标数推断。历史文件未声明字段与已声明但类型错误宜区别处理。

## 4. 构建、基准与边界

- 使用 AppleClang 21.0.0.21000334 在全新临时目录构建原生 Release，实际运行 CTest。TS 运行版本化脚本，在当前提交的干净副本复用已有依赖，`npm run lint` 与 `npm run build` 均退出 0。Vite 提示配置兼容性和包体大小。本次工作台结论来自实际使用的题目解析、求解和验证函数，未运行浏览器交互 E2E。
- 本次 Git 差异包含 TS 搜索器传递区域掩码和 `generateLegalMoves` 区分空数组的改动。以 3500 节点、深度 48、512 MiB、SSK、默认劫权、PatternTT、RZ、扩窗基数 8 复跑原 23 题，TS **7 已定论 / 16 UNKNOWN**，C++ **6 已定论 / 17 UNKNOWN**。p042 仍由 TS 以 rs、1093 搜索节点、1574 DAG 节点成证，C++ 能复核该文件，自行搜索到限为 UNKNOWN。原生 p003、p004 分别为 11、12 节点，p004 有 3 次 RZ 剪枝。
- 本轮独立交叉复核覆盖 7 份 TS 完整证书与 6 份 C++ 紧凑证书。上述“摘要一致”均指两个实现核验同一份证书，或同一 DAG 切换编码；同题的不同证明无需得到同一摘要。
- 临时证据目录为 `/tmp/ldprover-r8.zwUwQC`。其中 `capture-absent.json`、`capture-explicit.json` 及两端导出文件可复核第一节；`matrix-results.json`、`reverse-exact.json`、`cross.json` 与原生 CTest 日志记录协议与回归结果。建议下一次优先由同一原题文件驱动两端独立解析和互验。
