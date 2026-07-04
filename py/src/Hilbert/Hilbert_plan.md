# Hilbert 几何基础 — 进展分析与规划

**最后更新**: 2026-07-02
**项目位置**: `/Users/luoxing/coq/py/src/Hilbert/`
**Rocq 版本**: 9.1.1 (Coq 8.18+)
**编译状态**: 15/15 Hilbert 模块全量编译通过 (V1/V2/III5_Independence.v 等价证明纳入测试时需重排 _CoqProject)

---

## 项目结构 (17 个文件, 3,791 行)

```
Hilbert/
├── Common.v                  Tier-2 基础 (Point/Line/Plane + Incid/Bet/Parallel/SameSide)  72 行
├── Types.v                   Ray/Angle/OnRay 类型                                       53 行
├── HilbertStructure.v        Tier-5: 7 Record 抽象 (5 公理 + 2 组合)                  211 行
├── IncidenceAxioms.v         I 组 8 公理 + 5 QED (theorem_1a-2b)                       204 行
├── OrderAxioms.v            II 组 5 公理 + 9 QED + 5 Admitted                         188 行
├── CongruenceAxioms.v        III 组 6 公理 + 25 Admitted (theorem_11-39)              696 行
├── ParallelAxioms.v          IV 组 3 公理 + 1 QED (Parallel_sym)                       53 行
├── ContinuityAxioms.v        V 组 2 公理 + 1 Admitted (theorem_9)                     117 行
├── HilbertFoundations.v      Tier-5 汇合模块 (零 Axiom, 仅 Export)                    65 行
├── PascalTheorem.v           巴斯噶 + 退化 (1 Axiom + 1 QED + 2 Admitted)            185 行
├── DesarguesTheorem.v        德沙格 + 逆 (2 QED + 2 Admitted)                         183 行
├── QPlane.v                  Q² 模型 = WeakHilbertPlane (21 Axiom 占位 + 4 QED)      411 行
├── Model_Consistency.v       Hilbert I~V 的模型一致性 (1 Axiom + 9 QED + 2 Admitted) 350 行
├── IV_Independence.v         球面模型: 平行公理独立性 (3 QED + 4 Admitted)            260 行
├── V1_Independence.v         V₁ 独立性 (2 QED + 1 Admitted)                           286 行
├── V2_Independence.v         V₂ 独立性 (2 QED + 3 Admitted)                           189 行
└── III5_Independence.v       III₅ 合同自反独立性 (1 QED + 2 Admitted)                 268 行
```

---

## 编译与测试状态

```
✓ 编译通过 (15/15 模块, 全部 .vo 文件存在)
✗ AxiomAudit.md 待生成
✗ Theorem 验证脚本
```

**关键编译技巧** (已踩过的坑):
- `From Stdlib Require Import Classical` (替代 `From Coq`)
- `Open Scope R_scope` 必须在使用 R 的文件首声明
- `Ring` 在 QArith 上不适用, QPlane 用 `Qplus/Qmult` 显式证明
- Record 字段命名避免与 Common.v 全局 Bet 冲突 → 用 `O.(II3)` 投影

---

## Axiom / QED 统计

| 类别 | Axiom | QED | Admitted | 备注 |
|------|------:|------:|--------:|------|
| Hilbert 公理 (I~V) | 23 | — | — | 8 + 5 + 6 + 3 + 2 = 24; III₆ 合并到 5 |
| Record 字段 | — | — | — | 全部作为 Record, 不算自由 Axiom |
| IncidenceAxioms | 0 | 5 | 0 | theorem_1a/1b/1c/2a/2b (Tier-5 重构) |
| OrderAxioms | 0 | 9 | 5 | Bet_neq/Bet_trans/th_4/5/7 admit |
| CongruenceAxioms | 0 | 0 | 25 | **核心瓶颈**: theorem_11-39 |
| ParallelAxioms | 3 | 1 | 0 | IV_1/IV_2/Parallel_nointersect (必须 Axiom) |
| ContinuityAxioms | 2 | 0 | 1 | V_1/V_2 + theorem_9 admit |
| Pascal/Desargues | 1+0 | 1+2 | 2+2 | 1 Axiom + 5 admit |
| QPlane (Q² 模型) | 21 | 4 | 3 | 多数是 QArith 等式占位 |
| Independence | 0 | 8 | 10 | 球面/超限模型 + Q² 反例 |
| Model_Consistency | 1 | 9 | 2 | |
| **总计** | **34** | **39** | **50** | QED 完成度 44% (39 / (39+50)) |

---

## 目标 (与用户偏好一致)

> 用户偏好 QED 胜过 Axiom。每个 Axiom 尽可能下降为 QED 定理。

### P0 — 必须完成 (编译/正确性核心)

| # | 任务 | 文件 | 当前 | 目标 |
|---|------|------|------|------|
| 1 | theorem_11 (等腰底角相等) | CongruenceAxioms.v | admit | **QED** — III-1+III-4+III-5+SAS 路径 |
| 2 | theorem_12 (ASA 全等) | CongruenceAxioms.v | admit | **QED** |
| 3 | theorem_14 (邻补角合同) | CongruenceAxioms.v | admit | **QED** |
| 4 | theorem_15 (角加减法) | CongruenceAxioms.v | admit | **QED** |
| 5 | Bet_trans / Bet_neq (Order) | OrderAxioms.v | admit | **QED** |

### P1 — 重要 (基础证明)

| # | 任务 | 文件 | 备注 |
|---|------|------|------|
| 6 | theorem_19~27 (基本度量) | CongruenceAxioms.v | 19 (过线上点垂线), 20 (过线外点), 21 (斜边长), 22 (外角), 23 (垂线段短), 24 (中垂线), 25 (中垂线逆), 26 (外心), 27 (内心) |
| 7 | theorem_28~34 (平行判定) | CongruenceAxioms.v | 平行四边形、内角和、SSS |
| 8 | theorem_4/5/7 (外角/传输) | OrderAxioms.v | 配合 Pasch |
| 9 | theorem_9 (平面分空间) | ContinuityAxioms.v | Pasch 空间推广 |
| 10 | Bet_incid 完整证明 | OrderAxioms.v | 已 admit, II-1 + Bet_unique 路径 |

### P2 — 标准 (经典定理)

| # | 任务 | 文件 |
|---|------|------|
| 11 | Desargues 定理主证明 | DesarguesTheorem.v |
| 12 | Pascal 定理主证明 | PascalTheorem.v |
| 13 | model_consistency: 验证 Q² 满足 I+II+III | Model_Consistency.v |
| 14 | 装配 HilbertFoundations (零 Axiom) | HilbertFoundations.v |
| 15 | 验证所有 Hilbert 在 R² 中 | (待 RealPlane.v) |

### P3 — 高级 (独立性/扩展)

| # | 任务 | 文件 |
|---|------|------|
| 16 | V_1 ↔ V_2 等价性 | ContinuityAxioms.v |
| 17 | 球面模型 I+II+III 完整验证 | IV_Independence.v |
| 18 | III₅ 在球面中独立 | III5_Independence.v |
| 19 | RealPlane.v: 构造 R² as StrongHilbertPlane | (待创建) |
| 20 | QPlaneNotDedekind: √2 反例 QED | (待创建) |

---

## 重点路径与依赖

```
CongruenceAxioms.v:
  III-1 (迁移) ─┬─→ theorem_11 (等腰底角相等)  ─→ theorem_19 (过线上点垂线)
                │       ├─→ theorem_12 (ASA)
                │       └─→ theorem_35 (SAS)    ─→ theorem_22 (外角)
                ├─→ theorem_14 (邻补角合同)     ─→ theorem_29 (内角和)
                ├─→ theorem_15 (角加减法)      ─→ theorem_28 (平行判定)
                ├─→ theorem_20 (过线外点垂线)
                ├─→ theorem_23 (垂线段短)     ─→ theorem_24 (中垂线)
                ├─→ theorem_32 (SSS)          ─→ theorem_36 (等腰中线⊥底)
                ├─→ theorem_33 (线段中点)
                └─→ theorem_37 (角合同传递)
```

---

## 实施步骤 (按依赖拓扑)

### Tier-1: 紧急 (7 天)
1. **theorem_11 QED 化** — 论证最为经典, 1~2 天
2. **theorem_12 QED 化** — 依赖 III-1 唯一性
3. **Bet_incid 完整证明** — 已用 II-1 + admit 化, 需 II-4 + 推理闭环

### Tier-2: 核心 (2 周)
4. theorem_35 (SAS) — 全等之母
5. theorem_14 (邻补角合同) + theorem_15 (角加减法)
6. theorem_19/20 (垂线存在性)
7. theorem_23 (垂线段最短)
8. theorem_28 (平行判定) + theorem_29 (内角和)
9. theorem_32 (SSS) — 需要 Bet 加法 + III-3

### Tier-3: 完整化 (1 月)
10. theorem_22 (外角定理)
11. theorem_24/25 (中垂线 ± 逆)
12. theorem_30/31 (平行四边形)
13. theorem_33 (中点唯一)
14. theorem_36 (等腰中线⊥底)
15. theorem_37 (角合同传递)

### Tier-4: 经典定理 (2 月)
16. Desargues 定理证明
17. Pascal 定理证明
18. Model_Consistency: 验证 Q² 满足 I~III
19. OrderAxioms: theorem_4/5/7

### Tier-5: 独立性 (3+ 月)
20. IV_Independence: 补完球面模型的 I+II+III 验证
21. V_1 ↔ V_2 等价证明 (R² construction 路线)
22. QPlaneNotDedekind: √2 不是 Q² 的点 (QED)
23. RealPlane.v: R² → StrongHilbertPlane (新文件)

---

## Axiom 下降策略

> 用户核心原则: QED > Axiom

| 当前 Axiom | 来源 | 可否降为 QED? |
|-----------|------|---------------|
| III_1 (线段迁移) | Hilbert 原公理 | **否** — Hilbert 必需 |
| III_2 (合同传递) | Hilbert 原公理 | **否** |
| III_3 (线段加法) | Hilbert 原公理 | **否** |
| III_4 (合同对称) | Hilbert 原公理 | **否** (独立) |
| III_5 (合同自反) | Hilbert 原公理 | **可** — 需 III-1 唯一性 (TODO) |
| III_6 (角合同对称) | Hilbert 原公理 | **否** |
| IV_1 (Euclid) | Hilbert 原公理 | **否** (Sacco 替代仍需 Axiom) |
| IV_2 (平行可传) | Hilbert 原公理 | **否** |
| Parallel_nointersect | 平行定义 | **可** — 用 Hilbert 原始定义替换 |
| V_1 (Archimedes) | Hilbert 原公理 | **否** (独立) |
| V_2 (戴德金) | Hilbert 原公理 | **否** (独立) |
| Pascal 主公理 | 定理但常用形式 | **可** — 用 II+III 推导 (TODO) |
| QPlane 21 Axiom | QArith 占位 | **可** — Qeq 显式证明 (TODO) |

**策略优先级**:
- **P0**: III_5 完整化 (Tier-5 优雅化)
- **P1**: Parallel_nointersect 改成 Definition (而非 Axiom)
- **P2**: QPlane 中 Qeq 补完 (21 Axiom → QED)
- **P3**: Pascal 简化 (1 Axiom → 从 III 推导)

---

## 关键洞察

### HilbertStructure Record 设计哲学
- **独立性第一**: 把 5 组公理分到独立 Record, 容易构造反例
- **可组合性**: 通过 Record 嵌套 (WeakHilbertPlane = I+II+III+V_1)
- **可实例化**: Q² / R² / 球面都可作为 Record 实例

### 当前 Tier 进度
- **Tier-1** (Common + Types): ✅ 完成
- **Tier-2** (公理 + Record): ✅ 完成 (5 Record 全部定义)
- **Tier-3** (定理证明): 🚧 进行中 (39/89 QED, 44%)
- **Tier-4** (独立性): 🚧 进行中 (球面 + Q 反例)
- **Tier-5** (QED 优化): 🚧 P0 启动

---

## 测试与验证

### smoke test
```bash
cd /Users/luoxing/coq/py
make  # 重新编译所有 Hilbert 模块
# 期望: 15/15 .vo 文件就绪
```

### Axiom 审计
```bash
grep -rE '^\s*Axiom\s+' src/Hilbert/ | wc -l   # 应 = 34
grep -rE '^\s*Admitted' src/Hilbert/ | wc -l   # 应 <= 50 (推进时下降)
grep -rE '^\s*Qed\.' src/Hilbert/ | wc -l      # 应 >= 39 (推进时上升)
```

### Theorem 提取
```bash
grep -rE '^\s*(Theorem|Lemma)\s+\w+_+\d+' src/Hilbert/  # Hilbert 编号系列
```

---

## 已知障碍 (Tier-3 难点)

1. **缺少 §§ 1-3 经典定理 (SAS, ASA, SSS) 的 QED 化** — 这三者是一切几何证明的基石
   → 当前 admit 占位, Tier-2 先补完
2. **Record 投影与直接 Axiom 风格的接口不一致**
   → IncidenceAxioms.v 已切换到 Record 风格, CongruenceAxioms.v 仍是 Parameter
   → 决策: 保持 Parameter 风格 (简单), 还是统一 Record (优雅)?
3. **QPlane 21 Axiom 主要是 QArith 等式证明繁琐**
   → 可选: 引入 `ring`/`field` 简化, 或显式 Qeq 证明
4. **Hilbert 原书的定理编号 vs Coq Theorem 名称映射**
   → Table 已建立, 但需保持一致更新

---

## 下一步 (用户偏好: 一次一行命令)

- 「完成 theorem_11」 → 第一步: QED 化等腰底角相等
- 「完成 theorem_12」 → ASA 全等
- 「P0 五项推进」 → 整体 P0 推进, 每日一次 smoke test

---

**完成度更新**: 17 文件 / 3,791 行 / 39 QED / 34 Axiom / 50 Admitted → 完成率 44%

**目标**: 50 文件 / ~10,000 行 / 100 QED / 0 (下降 Axiom) / 10 Admitted (仅独立性)
