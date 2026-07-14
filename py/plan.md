# Coq PDE/Hilbert 形式化项目 — 进展分析与规划

**最后更新**: 2026-07-14
**项目位置**: `/Users/luoxing/coq/py/`
**Rocq 版本**: 9.1.1

---

## 编译状态 (实测 2026-07-14)

**真实编译率: 57/60 (95%)** — 3 个 Hilbert 文件未通过编译。
(此前 plan.md 声称 57/57 = 100% 有误，因 _CoqProject 引用了已重命名文件导致 build 直接失败)

| 模块 | .v 主文件 | .vo 已编译 | 编译率 |
|------|-----------|-----------|--------|
| **CompactEmbedding** | 6 | 6 | 6/6 ✓ |
| **Gronwall** | 1 | 1 | 1/1 ✓ |
| **Hilbert** | 18 | 15 | 15/18 ⚠ |
| **Hopf** | 1 | 1 | 1/1 ✓ |
| **Ladyzhenskaya** | 15 | 15 | 15/15 ✓ |
| **LinearAlgebra** | 2 | 2 | 2/2 ✓ |
| **SphereClassification** | 17 | 17 | 17/17 ✓ |
| **总计** | **60** | **57** | **57/60** |

**已确认编译通过的模块**: Ladyzhenskaya 全部 15 个文件 ✓，SphereClassification 全部 17 个文件 ✓，LinearAlgebra 全部 2 个文件 ✓，CompactEmbedding 全部 6 个文件 ✓，Hopf 全部 1 个文件 ✓，Gronwall 全部 1 个文件 ✓。

**Hilbert 已编译 (15/18)**: Common, Types, HilbertStructure, IncidenceTheorem, OrderTheorem, ParallelTheorem, ContinuityTheorem, DesarguesTheorem, PascalTheorem, EuclideanTheorem, IV_Independence, V1_Independence, V2_Independence, III5_Independence, Model_Consistency。

---

## 未编译文件 (3 个)

### 1. CongruenceTheorem.v (P0 — 核心瓶颈)

**错误位置**: line 475, theorem_35 (SAS 全等定理)
```
HAC : CongAng I O C B C' A B' C'' A'
Expected: CongAng' A C' B A' C'' B' = CongAng I O C A C' B A' C'' B'
```
**根因**: `III7` (ASA) 调用返回的 `HAC` 角参数顺序为 `(B C' A B' C'' A')`，但 theorem_35 证明期望 `(A C' B A' C'' B')`。`III7` 返回第三个角时把 `B C' A` (原角 C) 作为参数，而非 `A C' B`。

**修复方向**: 在 `HAC` 之后加 `cong_ang_sym3` (∠BCA ≅ ∠B'C'A') 翻转角参数顺序，或修改 `III7` 调用让返回的 HAC 就是 A 角。

**依赖**: 这是 theorem_11~39 中唯一有实际 QED 尝试的复杂定理，其他 24 个 theorem 均为 `admit` 占位。

### 2. QPlane.v (P0 — Q² 模型实例化)

**错误位置**: line 246, `mkOrder` 构造函数
```
mkOrder Q2_Incidence (fun A B C => QBet A B C)
    ?II_1 ?II_2 ?II_3 ?Bet_sym ?Bet_nondeg
```
**根因**: `HilbertStructure.v` 中 `OrderStructure` Record 的字段数/顺序已变更 (增加了 `ray_through` 等字段)，但 `QPlane.v` 中的 `mkOrder` 调用仍使用旧的字段列表。

**修复方向**: 对照 `HilbertStructure.v` 中 `OrderStructure` 的 Record 定义，给 `mkOrder` 补充缺失的字段参数。

### 3. HilbertFoundations.v (P0 — 级联失败)

**根因**: 依赖 `CongruenceTheorem.vo`，因 CongruenceTheorem 未编译成功而级联失败。CongruenceTheorem 修复后自然通过。

---

## _CoqProject 修复 (已完成 2026-07-14)

**问题**: 文件引用了已重命名的旧文件名，导致 `make -f Interface` 启动即失败。

**已修复的映射**:

| 旧名 (_CoqProject 原引用) | 现名 (实际磁盘文件) |
|--------------------------|-------------------|
| IncidenceAxioms.v | IncidenceTheorem.v |
| OrderAxioms.v | OrderTheorem.v |
| CongruenceAxioms.v | CongruenceTheorem.v |
| ParallelAxioms.v | ParallelTheorem.v |
| ContinuityAxioms.v | ContinuityTheorem.v |

**新增引用** (此前缺失): HilbertStructure.v, EuclideanTheorem.v, QPlane.v

**_CoqProject 当前 Hilbert 顺序** (依赖拓扑):
```
Common.v → Types.v → HilbertStructure.v
→ IncidenceTheorem.v → OrderTheorem.v → CongruenceTheorem.v
→ ParallelTheorem.v → ContinuityTheorem.v
→ DesarguesTheorem.v → PascalTheorem.v → EuclideanTheorem.v
→ QPlane.v → IV_Independence.v → V1_Independence.v → V2_Independence.v → III5_Independence.v
→ Model_Consistency.v → HilbertFoundations.v
```

---

## Axiom / Admitted / QED 统计 (实测 grep, 2026-07-14)

| 模块 | 文件 | 行数 | Axiom | Admitted | Qed |
|------|------|------|-------|----------|-----|
| CompactEmbedding | 6 | 918 | 7 | 9 | 17 |
| Gronwall | 1 | 349 | 0 | 0 | 6 |
| Hilbert | 18 | 4034 | 39 | 28 | 45 |
| Hopf | 1 | 465 | 8 | 5 | 3 |
| Ladyzhenskaya | 15 | 4743 | 191 | 15 | 41 |
| LinearAlgebra | 2 | 829 | 13 | 14 | 21 |
| SphereClassification | 17 | 3751 | 54 | 10 | 67 |
| **总计** | **60** | **15089** | **312** | **81** | **200** |

**Ladyzhenskaya 是 Axiom 最大集中区** (191 个 Axiom):
- Uniqueness.v: 59 Axiom + 12 Admitted (等待 Sobolev 基础设施)
- MoserIteration.v: 22 Axiom (Moser L²→L^∞ + Harnack)
- SobolevSpace.v: 21 Axiom + 2 Admitted (Sobolev 嵌入 + 迹定理)
- HolderSpace.v: 19 Axiom (Hölder 范数公理 — 抽象 Parameter 接口，无法直接 QED)
- HopfBoundaryAnalysis.v: 14 Axiom (障碍函数 + Hopf 边界点引理)
- ABPCalderonZygmund.v: 13 Axiom (ABP + Calderón-Zygmund 分解)
- EllipticParabolicAnalysis.v: 11 Axiom (符号分析)
- Derivatives.v: 11 Axiom + 1 Admitted (偏导数性质)

**Hilbert 模块 Axiom 分布**:
- QPlane.v: 21 Axiom (QArith 等式占位 — 可 QED 化)
- CongruenceTheorem.v: 12 Axiom (Ray 构造公理 + Hilbert III 组公理)
- ParallelTheorem.v: 3 Axiom (IV 组公理)
- PascalTheorem.v: 2 Axiom (Pascal 公理)
- Model_Consistency.v: 1 Axiom
- OrderTheorem.v: 0 Axiom (所有 II 组公理已 QED)
- IncidenceTheorem.v: 0 Axiom (所有 I 组公理已 QED)

**Hilbert QED 率**: 45/88 = 51% (45 Qed / (45 Qed + 28 Admitted + 39 Axiom 不含公理本身)
注: 23 个 Hilbert 原公理 (I~V) 作为 Record 字段不算自由 Axiom。

---

## 工程问题

### 1. Hilbert 模块文件重命名未同步到 _CoqProject
- `*Axioms.v` → `*Theorem.v` (Incidence/Order/Congruence/Parallel/Continuity)
- 新文件 HilbertStructure.v, EuclideanTheorem.v, QPlane.v 未注册
- **已修复** (2026-07-14)

### 2. CongruenceTheorem.v theorem_35 SAS 证明有类型错误
- III7 返回的角参数顺序与期望不符
- **需修复** (P0)

### 3. QPlane.v mkOrder 构造函数字段不匹配
- OrderStructure Record 已更新，QPlane 未跟进
- **需修复** (P0)

### 4. ContinuityTheorem.v 是空桩 (21 行)
- 只有 Section 定义，无任何公理/定理
- **需补全** (P1)

### 5. 8 个孤立测试文件
- `src/Hilbert/test2.v`, `test3.v`, `test4.v`, `test_final.v`, `test_implicit.v`, `test_thm14.v`, `test_wrapper.v`
- `src/Gronwall/TestGronwallAxioms.v`
- `src/.test_hnot.aux` + 根目录 `test_hnot.v`, `test_hnot.glob`
- **可清理** (P3)

### 6. 4 个编辑器锁文件 (.#)
- `src/Hilbert/.#HilbertStructure.v`, `.#IncidenceAxioms.v`, `.#IncidenceTheorem.v`
- `src/LinearAlgebra/.#ex.v`
- **可清理** (P3)

### 7. src/Ladyzhenskaya/src/LadyzhenskayaDir/ 嵌套目录
- 6 个 .aux 文件，无对应 .v 文件
- **可清理** (P3)

### 8. From Coq → From Stdlib 弃用警告
- 约 50+ 处 `Require Import Reals/Lra/Classical` 等未加 `From Stdlib` 前缀
- Rocq 9.x 下会触发 deprecated-missing-stdlib 警告
- **低优先** (P4)

---

## 下一步优先级

| 优先级 | 任务 | 工作量 | 影响 | 状态 |
|--------|------|--------|------|------|
| **P0.1** | 修复 _CoqProject 文件名映射 | 5 分钟 | 解阻 build | ✅ 已完成 |
| **P0.2** | 修复 CongruenceTheorem.v theorem_35 类型错误 | 30-60 分钟 | 让 theorem_35 QED + 解阻 HilbertFoundations | ⏳ 待修 |
| **P0.3** | 修复 QPlane.v mkOrder 字段不匹配 | 15 分钟 | 让 Q² 模型实例化编译 | ⏳ 待修 |
| **P0.4** | 验证 HilbertFoundations.v 编译通过 | 5 分钟 | 验证 P0.2+P0.3 | ⏳ 待修 |
| **P1** | ContinuityTheorem.v 补全 (V 组公理 + theorem_9) | 1-2 小时 | Hilbert V 组完整化 | ⏳ 待做 |
| **P2** | OrderTheorem 5 Admitted + Congruence 24 Admitted QED 化 | 10+ 小时 | Hilbert QED 率 51%→80%+ | ⏳ 长期 |
| **P3** | 清理 8 个测试文件 + 4 个锁文件 + 嵌套目录 | 15 分钟 | 工程整洁 | ⏳ 待做 |
| **P4** | From Coq → From Stdlib 警告消除 (全项目) | 2 小时 | 编译清洁 | ⏳ 待做 |
| **P5** | Ladyzhenskaya 191 Axiom 降低策略 | 长期 | Ladyzhenskaya 主定理 QED | ⏳ 需前置 Sobolev 基础设施 |
| **P6** | 更新 README.md 反映真实状态 | 30 分钟 | 文档同步 | ⏳ 待做 |

---

## 用户偏好 (来自记忆)

- **QED > Axiom**: 每个 Axiom 尽可能降级为 QED 定理
- **诚实 Admitted 标记**: "honest Admitted, 等待基础设施" 模式
- **中文一行命令**: 直接执行 + smoke test
- **KillingHopf 模式**: monolithic Axiom → 分解为 3+ (D) Axiom + QED Lemma
- **4-tier scope decomposition**: skeleton → layered → subsystems → full

---

## 项目目标

基于 Ladyzhenskaya 1968 + Hilbert《几何基础》(1899) + Hamilton 1982:

1. **Ladyzhenskaya 主链** (核心): HolderSpace → Schauder → Galerkin → LadyzhenskayaMain + Uniqueness + Hopf
2. **SphereClassification 链** (Killing-Hopf 骨架): Topology → Manifold → Geodesic → HopfRinow → KillingHopf → SphereTheorem (17/17 ✓)
3. **CompactEmbedding 链** (Arzelà-Ascoli 紧性): MetricCompact → UniformBounded → Equicontinuity → ArzelaAscoli → CompactEmbedding (6/6 ✓)
4. **Hilbert 几何基础**: I-V 公理 + Desargues/Pascal 定理 + V₁/V₂/III₅/IV 独立性 + ℝ³ 模型相容性 (15/18 ⚠)

**当前完成度 (2026-07-14)**: 全量 57/60 = **95% 编译通过**。3 个 Hilbert 文件待修复 (CongruenceTheorem theorem_35, QPlane mkOrder, HilbertFoundations 级联)。
