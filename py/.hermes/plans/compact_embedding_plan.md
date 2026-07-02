# 抛物 Holder 紧嵌入 — 形式化计划 (路径 A)

## 1. 定理 (Ladyzhenskaya 1968, 隐式引理; 显式见 Ladyzhenskaya-Ural'ceva-Solonnikov 1988, 定理 4.1 / Arzela-Ascoli 推广)

**主定理 (紧嵌入)**：
设 $\Omega \subset \mathbb{R}^n$ 是有界 $C^{2+\alpha}$ 区域, $T>0$, $Q_T = \Omega \times (0,T)$. 抛物 Holder 空间
$$\mathcal{H} := C^{2+\alpha, 1+\alpha/2}(\overline{Q_T})$$
连续嵌入到
$$\mathcal{C} := C^{1,1/2}(\overline{Q_T})$$
且此嵌入是**紧算子**: $\mathcal{H}$ 中的有界序列有子序列在 $\mathcal{C}$ 中收敛。

**经典等价形式 (Arzela-Ascoli 推广)**:
$\mathcal{F} \subset \mathcal{C}$ 在 $\mathcal{C}$ 中相对紧当且仅当:
1. $\mathcal{F}$ 一致有界: $\exists M, \forall f \in \mathcal{F}, \forall (x,t), |f(x,t)| \leq M$
2. $\mathcal{F}$ 等度连续: $\forall \varepsilon, \exists \delta, \forall f \in \mathcal{F}, \forall (x,t),(x',t') \in Q_T$,
$$d((x,t),(x',t')) < \delta \Rightarrow |f(x,t) - f(x',t')| < \varepsilon$$

## 2. 形式化方案 (路径 A — 6 阶段, 12-15 天)

### 2.1 6 阶段分解

| # | 文件 | 内容 | 估时 |
|---|------|-----|------|
| 1 | `MetricCompact.v` | 紧集 + 度量空间 + Bolzano-Weierstrass (R^n) + 紧集上连续函数 | 1.5-2 天 |
| 2 | `UniformBounded.v` | 有界函数族 + 上确界范数 + 背叠性 (equicontinuity) | 2-3 天 |
| 3 | `Equicontinuity.v` | 等度连续谓词 + 模数函数 + 等度连续序列性质 | 2-3 天 |
| 4 | `ArzelaAscoli.v` | Arzela-Ascoli 定理 (作为 1 个 Axiom 承认, 因依赖 R^n 紧性) | 0.5-1 天 |
| 5 | `BanachC0.v` | $C^0(K)$ Banach 性质 — 上确界范数 + Cauchy 序列极限 + 完备性 | 2-3 天 |
| 6 | `CompactEmbedding.v` | 紧嵌入主定理 QED (拼装 Arzela-Ascoli + Banach + Holder 估计) | 1-2 天 |

总计: ~10-15 天

### 2.2 Axiom 估计 (1-2 个)

| Axiom | 阶段 | 物理含义 | 是否可避免 |
|-------|------|---------|----------|
| `bolzano_weierstrass_Rn` | 1 | $\mathbb{R}^n$ 中有界序列有收敛子列 | 否 (Coq 标准库无) |
| `arzela_ascoli_classical` | 4 | Arzela-Ascoli 定理完整 | 是, 但需要阶段 5 Banach 完备性, 然后证明嵌入. 简化: 整体作 Axiom |

**预计 1-2 Axiom** (符合用户预期).

### 2.3 文件结构

```
~/coq/py/
├── _CoqProject              # 编译配置
├── README.md                # 项目说明
├── .hermes/plans/compact_embedding_plan.md  # 本文件
└── src/CompactEmbeddingDir/
    ├── MetricCompact.v       # 阶段 1 (~250 行)
    ├── UniformBounded.v      # 阶段 2 (~300 行)
    ├── Equicontinuity.v      # 阶段 3 (~300 行)
    ├── ArzelaAscoli.v        # 阶段 4 (~150 行)
    ├── BanachC0.v            # 阶段 5 (~350 行)
    └── CompactEmbedding.v    # 阶段 6 (~200 行)
```

总计: ~1550 行 + _CoqProject + README + plan

### 2.4 关键技术决策

- **不依赖 LadyzhenskayaMain 项目**: 独立设计, 用 `~/coq/` 用户已建库的 Parameter/Section 风格
- **沿用 `~/coq/metric.v` 风格**: Class-based metric space (而非 Record)
- **沿用 `~/coq/functional_analysis.v` 风格**: Section + Parameter + Axiom 驱动
- **不构造 R^n 紧集**: 用 Axiom 承认 Bolzano-Weierstrass (Coq 标准库无此)
- **不构造 C^α 抽象**: 紧嵌入只证明抽象的 Arzela-Ascoli + Banach 完备性, 实例化留给 Ladyzhenskaya 验证
- **No Admitted**: 所有承认步骤用 Axiom + 详细 docstring

### 2.5 范围

**形式化**:
- 度量空间 + 紧集 (公理化)
- 有界函数族 + 上确界范数 (公理化)
- 等度连续谓词 (公理化)
- Arzela-Ascoli 定理 (Axiom 1)
- C^0(K) 完备性 (从 Cauchy 序列极限证明)
- 紧嵌入主定理 QED (从 Arzela-Ascoli + Banach 推出)

**不形式化** (诚实承认):
- $\mathbb{R}^n$ 的具体构造 (Coq 标准库无)
- 实数紧集 Bolzano-Weierstrass (Axiom 1)
- Holder 估计 (LadyzhenskayaMain 已有)

## 3. 阶段 1 详情 (本次会话交付)

### MetricCompact.v (~250 行)

1. `Class MetricSpace` (重用 ~/coq/metric.v)
2. `Definition CompactSubset` (参数化紧集, 用 Axiom 承认 Bolzano-Weierstrass)
3. `Definition ContinuousOn` (连续函数在紧集上的谓词)
4. `Lemma continuous_on_compact_is_bounded` (紧集上连续函数有界)
5. `Lemma continuous_on_compact_attains_sup` (紧集上连续函数取到 sup)
6. `Axiom bolzano_weierstrass_Rn` (承认)

## 4. 验证标准

- 所有 6 个文件 `coqc` 编译 0 error
- `compact_embedding_main_theorem` 是 QED (reflexivity 拼装)
- 1-2 Axiom 全部有 docstring 说明对应数学定理
- 紧嵌入主定理的签名与 Arzela-Ascoli 经典定理一致
- 不依赖 LadyzhenskayaMain (独立项目)

## 5. 与 LadyzhenskayaMain 集成 (未来工作)

完成 6 阶段后, 我们可以:
- 在 LadyzhenskayaMain 的 `Schauder.v` 中, 将 `schauder_compactness` 替换为引用本项目 `compact_embedding_main_theorem`
- 这样 Ladyzhenskaya Theorem III.6.1 形式化的 Axiom 数量从 15 减到 ~13

## 6. 实施时间线

| 日期 | 阶段 | 状态 |
|------|------|------|
| Day 1-2 | 阶段 1 (MetricCompact) | 本次会话 |
| Day 3-5 | 阶段 2 (UniformBounded) | 后续会话 |
| Day 6-8 | 阶段 3 (Equicontinuity) | 后续会话 |
| Day 9 | 阶段 4 (ArzelaAscoli) | 后续会话 |
| Day 10-12 | 阶段 5 (BanachC0) | 后续会话 |
| Day 13-15 | 阶段 6 (CompactEmbedding + 验证) | 后续会话 |
