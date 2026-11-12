# 围棋死活题求解算法与 Smargo 系统架构技术研讨全记录

> **整理说明**：本文档汇总整理了当前对话中关于围棋死活（Tsumego）算法研究、学术文献分析、数学证明可行性、算法缺陷审核、C++ / Python 核心数据结构与代码实现，以及借鉴 KataGo 与玄玄围棋实战经验的完整技术讨论记录。

---

## 目录
1. [围棋死活求解主要方案与最优混合架构](#一-围棋死活求解主要方案与最优混合架构)
2. [核心文献算法与相关资源汇总](#二-核心文献算法与相关资源汇总)
3. [评估算法预研（algorithm-research.md）审核与工程修正](#三-评估算法预研algorithm-researchmd审核与工程修正)
4. [死活问题的局部完全数学化证明理论](#四-死活问题的局部完全数学化证明理论)
5. [Python 核心算法原型实现（Benson + Niu Seki 联动）](#五-python-核心算法原型实现benson--niu-seki-联动)
6. [C++ 高性能基数树模式表（RZS-PT）数据结构与匹配算法](#六-c-高性能基数树模式表rzs-pt数据结构与匹配算法)
7. [玄玄围棋实测经验对比与现有算法改进](#七-玄玄围棋实测经验对比与现有算法改进)
8. [KataGo 源码提取与 semeye 眼形拓扑分类器设计](#八-katago-源码提取与-semeye-眼形拓扑分类器设计)

---

## 一、 围棋死活求解主要方案与最优混合架构

### 1.1 主要求解方案对比
* **传统知识启发式搜索**：依赖人工编写的规则与博弈树搜索（PNS/DFPN），终局通过 Benson 算法判定无条件活棋（UCA）。瓶颈在于依赖专家经验划定区域，复杂死活题通用性差。
* **相关区域搜索（RZS）**：自动识别并生成“相关区域（RZ）”，将外围落子视为 Null Move 剪枝。
  * **RZS-TT**：使用传统置换表（Zobrist Hash），全盘棋形精准匹配导致局部复用率低。
  * **RZS-PT**：采用基于基数树（Radix Tree）的 RZ 模式表，只存储局部棋形，解题速度比 RZS-TT 平均快 4.74 倍。
* **FTL（Faster-to-Life）神经网络引导**：预测在限制步数 d 内做活的胜率，强迫 AI 选择最短路径；配合分布式求解中的在线微调（Online Fine-Tuning）。
* **局部分析与 Seki（双活）数据库**：离线穷举 5–8 空间局部分形生成 Seki 库，在线搜索匹配即截断。在 7x7 Killall-Go 中将求解时间由天级缩短至 482 秒。

### 1.2 最优混合型层级认知求解器架构
* **核心引擎**：结合 PCN/FTL 网络引导的 MCTS / DFPN 混合搜索引擎，内嵌 RZS 区域划定与 RZ 模式表（Radix Tree）。
* **终局判定双引擎**：Benson 算法（UCA 判定） + Seki 数据库（双活快速匹配截断）。
* **AI 瓶颈改进**：数据增强（注入“石下”、“倒扑”等稀有棋形） + 双重特征面（活棋块定位 + 领地边界目数估算） + 收益塑形（Reward Shaping）。
* **COLMA 架构**：认知层级记忆反思回路，在线动态调大异动节点搜索权重或触发 LoRA 轻量微调。

---

## 二、 核心文献算法与相关资源汇总

### 2.1 关键论文与项目
1. **IEEE ToG / arXiv 论文**：《A Study of Solving Life-and-Death Problems in Go Using Relevance-Zone Based Solvers》
   * 提出 RZS 区域自动剪枝、FTL 步数约束网络、RZS-PT 基数树模式表及 PCN 网络。
2. **官方开源仓库**：study-LD-RZ (GitHub)
   * 包含 CGI 框架、MCTPS 求解器、PatternGenerator，基于 CMake 支持 RZS-TT 和 RZS-PT。
3. **7x7 Killall-Go 论文**：《Solving 7x7 Killall-Go with Seki Database》
   * 离线生成 254,342 个 Seki 模式（5-8 空间），双重 DFPN 验证。
4. **KataGo (Apache-2.0)**：
   * bensons.cpp 完整实现 Benson UCA 定理；search.cpp 包含 semeye（真眼/假眼/半眼）拓扑识别；CLI 支持 SGF 死活题输出 DEAD/ALIVE/KO/SEKI 四值结论。
5. **理论与现成工具/开源库**：
   * **Sensei's Library**：Ikeda（池田敏雄）死活形状表（标准公理出处）。
   * **银星围棋 / SharpSense**：职业级死活工具，修正过历史棋谱误判。
   * **GitHub 库**：yidao-go（KataGo 判题包装）、Reinforcement-Learning-in-Tsumego（MCTS+真假眼）、tsumego.js（JS 判题库）、weiqigo。

---

## 三、 评估算法预研（algorithm-research.md）审核与工程修正

### 3.1 预研报告亮点
* 清醒声明：学术指标不能直接作为工程验收指标，警示概率直接判定破坏证明确定性（Soundness = 100%）。
* 定性准确：死活题是二值逻辑 AND/OR 树数学证明，非概率估算。

### 3.2 四大工程硬伤与修正方案
1. **打劫（Ko）处理过于简化**：
   * 问题：19x19 下打劫引起节点震荡，简单的 pn/dn 调整无法收敛。
   * 修正：引入劫争特殊分支管理器（Ko Branch Manager），结合 Zobrist Hash 与劫争状态栈（Ko State Stack）维护提劫状态。
2. **Seki 数据库 19x19 边界效应**：
   * 问题：直接匹配局部模式易忽略外围块是否安全，导致误判。
   * 修正：增加安全外气验证（Safe Outer Liberties Check），要求外围块外气 >= C 或已达成 Benson UCA。
3. **在线微调（Online Fine-Tuning）算力灾难**：
   * 问题：每 1000 节点微调会导致 C++/Rust 引擎吞吐量断崖式下跌。
   * 修正：自适应瓶颈微调（仅当子树计算黑洞且开销 > 30% 时触发），并使用 LoRA 或仅更新 Policy Head。
4. **只求活棋不顾目数**：
   * 修正：升级为值域化证明数搜索（Value-Range df-pn），节点返回 (S, [M_min, M_max])，优先收敛最大目数分支。

### 3.3 演进路线图修正（生命线前置）
* 置换表（TT）必须在第一阶段 MVP 合入，否则同形节点会导致搜索树指数爆炸。

---

## 四、 死活问题的局部完全数学化证明理论

1. **局部完备性（RZS 剪枝定理）**：
   * 框定相关区域（RZ），对手区域外落子视为 Null Move 剪枝，将 19x19 退化为 N x M 闭合图。
2. **双活（Seki）数学证明（双重先手否定定理）**：
   * 在局部 z 内运行两次独立搜索：黑先手杀不掉白，且白先手杀不掉黑 <=> 唯一确认为 Seki。
3. **打劫（Ko）环路修正**：
   * df-pn(r) 算法进行环路惩罚；打劫结果表达为关于全局劫材差 K 的分段函数 f(K)。
4. **征子与全局依赖（Zone Dilation 区域自适应扩张）**：
   * 沿 +/- 45度 对角线拉伸 RZ，将引征子强行纳入局部闭合 RZ 中进行证明。

---

## 五、 Python 核心算法原型实现（Benson + Niu Seki 联动）

```python
from typing import Set, Dict, List, Tuple, Optional

class StoneBlock:
    def __init__(self, color: str, stones: Set[Tuple[int, int]]):
        self.color: str = color
        self.stones: Set[Tuple[int, int]] = stones
        self.liberties: Set[Tuple[int, int]] = set()
        self.adjacent_regions: Set['EyeRegion'] = set()

class EyeRegion:
    def __init__(self, points: Set[Tuple[int, int]]):
        self.points: Set[Tuple[int, int]] = points
        self.neighbor_blocks: Set[StoneBlock] = set()

    def is_healthy_for(self, block: StoneBlock) -> bool:
        return all(nb.color == block.color for nb in self.neighbor_blocks)

class BensonUCASolver:
    # Benson 算法：最大固定点迭代进行无条件活棋 (UCA) 消除
    def __init__(self, blocks: Set[StoneBlock], eye_regions: Set[EyeRegion]):
        self.X: Set[StoneBlock] = set(blocks)
        self.R: Set[EyeRegion] = set(eye_regions)

    def solve(self) -> Set[StoneBlock]:
        while True:
            initial_x_size, initial_r_size = len(self.X), len(self.R)
            self.R -= {r for r in self.R if not all(nb in self.X for nb in r.neighbor_blocks)}
            self.X -= {x for x in self.X if sum(1 for r in self.R if r.is_healthy_for(x) and r in x.adjacent_regions) < 2}
            if len(self.X) == initial_x_size and len(self.R) == initial_r_size:
                break
        return self.X

class NiuSekiDetector:
    # Niu 氏双重先手否定局部 Seki 检测
    def __init__(self, board_state, local_zone: Set[Tuple[int, int]]):
        self.board = board_state
        self.zone = local_zone

    def _local_dfpn_search(self, attacker_color: str, first_player: str) -> bool:
        pass

    def is_seki(self, black_block: StoneBlock, white_block: StoneBlock) -> bool:
        black_can_kill = self._local_dfpn_search("B", "B")
        if black_can_kill: return False
        white_can_kill = self._local_dfpn_search("W", "W")
        if white_can_kill: return False
        return True

class SmargoLifeEvaluator:
    # Smargo 统一生命评估器联动接口
    def __init__(self, board_state):
        self.board = board_state
        self.benson_alive_blocks: Set[StoneBlock] = set()
        self.seki_proven_zones: List[Set[Tuple[int, int]]] = []

    def evaluate_all_lives(self):
        blocks, eye_regions = self._parse_board_structures()
        self.benson_alive_blocks = BensonUCASolver(blocks, eye_regions).solve()
        suspicious_blocks = blocks - self.benson_alive_blocks
        for zone in self._segment_local_killing_zones(suspicious_blocks):
            b_block, w_block = self._get_representative_blocks(zone, suspicious_blocks)
            if NiuSekiDetector(self.board, zone).is_seki(b_block, w_block):
                self.seki_proven_zones.append(zone)
                self.benson_alive_blocks.update([b_block, w_block])
```

---

## 六、 C++ 高性能基数树模式表（RZS-PT）数据结构与匹配算法

```cpp
#include <vector>
#include <array>
#include <memory>
#include <cstdint>

enum class StoneState : uint8_t { EMPTY = 0, BLACK = 1, WHITE = 2 };

struct RadixNode;

struct RadixEdge {
    std::vector<StoneState> label;
    std::unique_ptr<RadixNode> target_node;
    RadixEdge(std::vector<StoneState> lbl, std::unique_ptr<RadixNode> target)
        : label(std::move(lbl)), target_node(std::move(target)) {}
};

struct RadixNode {
    bool is_terminal = false;
    uint32_t proof_number = 0;
    uint32_t disproof_number = 0;
    std::array<std::unique_ptr<RadixEdge>, 3> children; // 0: EMPTY, 1: BLACK, 2: WHITE
};

class RZPatternTable {
private:
    std::unique_ptr<RadixNode> root;

public:
    RZPatternTable() : root(std::make_unique<RadixNode>()) {}

    bool search(const std::vector<StoneState>& pattern, uint32_t& out_pn, uint32_t& out_dn) const {
        if (pattern.empty()) return false;
        const RadixNode* curr = root.get();
        size_t idx = 0;

        while (idx < pattern.size()) {
            uint8_t branch = static_cast<uint8_t>(pattern[idx]);
            const auto& edge = curr->children[branch];
            if (!edge) return false;

            const auto& label = edge->label;
            for (size_t i = 0; i < label.size(); ++i) {
                if (idx + i >= pattern.size() || pattern[idx + i] != label[i]) return false;
            }
            idx += label.size();
            curr = edge->target_node.get();
        }
        if (curr && curr->is_terminal) {
            out_pn = curr->proof_number;
            out_dn = curr->disproof_number;
            return true;
        }
        return false;
    }

    void insert(const std::vector<StoneState>& pattern, uint32_t pn, uint32_t dn) {
        if (pattern.empty()) return;
        RadixNode* curr = root.get();
        size_t idx = 0;

        while (idx < pattern.size()) {
            uint8_t branch = static_cast<uint8_t>(pattern[idx]);
            if (!curr->children[branch]) {
                std::vector<StoneState> rem_label(pattern.begin() + idx, pattern.end());
                auto leaf = std::make_unique<RadixNode>();
                leaf->is_terminal = true;
                leaf->proof_number = pn; leaf->disproof_number = dn;
                curr->children[branch] = std::make_unique<RadixEdge>(std::move(rem_label), std::move(leaf));
                return;
            }

            auto& edge = curr->children[branch];
            const auto& label = edge->label;
            size_t common_len = 0;
            while (common_len < label.size() && idx + common_len < pattern.size() && label[common_len] == pattern[idx + common_len]) {
                common_len++;
            }

            if (common_len < label.size()) { // 边分裂 Edge Split
                std::vector<StoneState> old_suffix(label.begin() + common_len, label.end());
                auto old_target = std::move(edge->target_node);
                auto middle = std::make_unique<RadixNode>();

                uint8_t old_branch = static_cast<uint8_t>(old_suffix[0]);
                middle->children[old_branch] = std::make_unique<RadixEdge>(std::move(old_suffix), std::move(old_target));

                std::vector<StoneState> new_suffix(pattern.begin() + idx + common_len, pattern.end());
                if (new_suffix.empty()) {
                    middle->is_terminal = true;
                    middle->proof_number = pn; middle->disproof_number = dn;
                } else {
                    uint8_t new_branch = static_cast<uint8_t>(new_suffix[0]);
                    auto new_leaf = std::make_unique<RadixNode>();
                    new_leaf->is_terminal = true;
                    new_leaf->proof_number = pn; new_leaf->disproof_number = dn;
                    middle->children[new_branch] = std::make_unique<RadixEdge>(std::move(new_suffix), std::move(new_leaf));
                }

                edge->label = std::vector<StoneState>(label.begin(), label.begin() + common_len);
                edge->target_node = std::move(middle);
                return;
            }
            idx += label.size();
            curr = edge->target_node.get();
        }
        curr->is_terminal = true;
        curr->proof_number = pn; curr->disproof_number = dn;
    }
};
```

---

## 七、 玄玄围棋实测经验对比与现有算法改进

1. **半开放缺口与 Zone Dilation**：二路开口引发逃逸时，通过自适应扩张将 RZ 沿联络路径拉伸封口。
2. **剔除无谓先手**：在 df-pn 中引入 (S, [M_min, M_max]) 评价与最佳步数限制，剔除无意义的先手交换。
3. **早停截断**：Benson UCA + Seki 数据库哈希双重早停，避免深层盲目搜索。
4. **SearchSession 会话缓存**：试走推演时进行 Re-rooting 根节点平移，提供 0.5s 内交互响应。

---

## 八、 KataGo 源码提取与 semeye 眼形拓扑分类器设计

### 8.1 KataGo semeye 四分类拓扑定义
* **TRUE_EYE（真眼）**：边界全被控，无关键断点风险，直接计入 Benson 眼区集 R。
* **FALSE_EYE（假眼）**：存在关键断点（Atari / 挤），在 Benson 中直接剥夺眼位资格（计 0）。
* **HALF_EYE（半眼）**：需要先手激活，在 df-pn 中作为高优先级 And-Or 条件节点。
* **SEMEAI_DAME（对杀公气）**：双方夹缝公气，交由 Niu 氏 Seki 检测处理。

### 8.2 C++ SmargoLifeEvaluator 集成实现

```cpp
#include <vector>
#include <set>

enum class EyeType : uint8_t { FALSE_EYE = 0, HALF_EYE = 1, TRUE_EYE = 2, SEMEAI_DAME = 3 };

struct StoneChain {
    uint16_t id;
    uint8_t color;
    std::vector<uint16_t> stones;
    std::set<uint16_t> liberties;
    bool is_uca_alive = false;
};

struct EyeRegion {
    uint16_t id;
    EyeType type;
    std::vector<uint16_t> points;
    std::vector<uint16_t> neighbor_chain_ids;
    std::vector<uint16_t> vital_points;
};

class SmargoLifeEvaluator {
private:
    std::vector<StoneChain> chains_;
    std::vector<EyeRegion> eye_regions_;

public:
    EyeType ClassifyEyeTopology(const EyeRegion& region) {
        int enemy_controlled_corners = 0;
        for (uint16_t p : region.vital_points) {
            if (IsEnemyControlledOrAtari(p, region)) enemy_controlled_corners++;
        }
        if (enemy_controlled_corners >= 2) return EyeType::FALSE_EYE;
        if (enemy_controlled_corners == 1) return EyeType::HALF_EYE;
        return EyeType::TRUE_EYE;
    }

    void RunBensonUCASolver() {
        std::set<uint16_t> active_chains, active_eyes;
        for (const auto& eye : eye_regions_) {
            if (eye.type == EyeType::TRUE_EYE) active_eyes.insert(eye.id);
        }
        for (const auto& chain : chains_) active_chains.insert(chain.id);

        bool changed = true;
        while (changed) {
            changed = false;
            std::vector<uint16_t> eyes_to_remove;
            for (uint16_t e_id : active_eyes) {
                for (uint16_t c_id : eye_regions_[e_id].neighbor_chain_ids) {
                    if (active_chains.find(c_id) == active_chains.end()) {
                        eyes_to_remove.push_back(e_id); break;
                    }
                }
            }
            for (uint16_t e_id : eyes_to_remove) { active_eyes.erase(e_id); changed = true; }

            std::vector<uint16_t> chains_to_remove;
            for (uint16_t c_id : active_chains) {
                int healthy_eyes = 0;
                for (uint16_t e_id : active_eyes) {
                    if (IsChainAdjacentToEye(c_id, e_id)) healthy_eyes++;
                }
                if (healthy_eyes < 2) chains_to_remove.push_back(c_id);
            }
            for (uint16_t c_id : chains_to_remove) { active_chains.erase(c_id); changed = true; }
        }

        for (uint16_t c_id : active_chains) chains_[c_id].is_uca_alive = true;
    }
};
```