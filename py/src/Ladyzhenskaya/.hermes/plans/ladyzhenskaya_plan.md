# Ladyzhenskaya 经典线性抛物 PDE 短时解存在性定理 — 形式化计划

## 1. 定理 (LSU Theorem III.6.1, 1968)

设 $\Omega \subset \mathbb{R}^n$ 是有界 $C^{2,\alpha}$ 区域，$T>0$。考虑初值问题：

$$\partial_t u - a^{ij}(x,t) \partial_{ij} u - b^i(x,t) \partial_i u + c(x,t) u = f(x,t), \quad (x,t) \in Q_T$$
$$u(x,0) = \phi(x), \quad x \in \Omega$$
$$u = 0 \text{ on } \partial_p Q_T$$

**假设**：
- $a^{ij}, b^i, c, f$ 在 $\overline{Q_T}$ 上 Hölder 连续 ($C^{\alpha,\alpha/2}$)，$0<\alpha<1$
- **严格抛物**：$\exists \mu>0$ s.t. $a^{ij}\xi_i\xi_j \geq \mu |\xi|^2$
- $\phi \in C^{2+\alpha}(\overline{\Omega})$ 且 $\phi=0$ on $\partial\Omega$
- $c \geq 0$

**结论**：存在 $T_0 \in (0,T)$，使得问题在 $C^{2+\alpha, 1+\alpha/2}(\overline{Q_{T_0}})$ 中有**唯一解**。

## 2. 形式化方案 (路径 A — 5-8 个 Axiom, ~700 行)

### 2.1 数学分解 (5 个 Axiom)

| # | Axiom | 对应数学步骤 | 物理合理性 |
|---|-------|------------|-----------|
| A1 | `coeff_Holder_regularity` | $a^{ij}, b^i, c, f \in C^{\alpha,\alpha/2}$ implies 系数半范有界 | 编码 Holder 半范定义 |
| A2 | `galerkin_approximation` | Faedo-Galerkin 逼近 $\{u_N\}$ 在 $L^2(H^1)$ 中存在 | Galerkin ODE 定理 |
| A3 | `energy_estimate_uniform` | 抛物能量 $\|u_N(t)\|^2 + \mu\int_0^t \|\nabla u_N\|^2 \le C$ | $L^2$ 能量不等式 (抛物 max 原理) |
| A4 | `schauder_interior_estimate` | $\|u_N\|_{C^{2+\alpha,1+\alpha/2}} \le C(\|f\|_\alpha + \|\phi\|_{2+\alpha})$ | Schauder 估计 |
| A5 | `schauder_global_uniqueness` | 抛物极大值原理 -> 唯一性 | 抛物 Hopf 引理 |

主定理 (`ladyzhenskaya_short_time_existence`) 用 5 个 Axiom + reflexivity (Qed) 拼装。

### 2.2 文件结构

```
src/LadyzhenskayaDir/
├── HolderSpace.v          # Holder 半范 / Banach 空间 / C^{2+alpha, 1+alpha/2} 空间 (130 行)
├── ParabolicCoefficients.v # a^{ij} 抛物性 / b^i, c, f 输入 (90 行)
├── Galerkin.v             # Faedo-Galerkin 逼近存在 (Axiom A2) + energy (Axiom A3) (130 行)
├── Schauder.v             # Schauder 估计 (Axiom A4) (100 行)
├── Uniqueness.v           # 抛物最大值原理 + 唯一性 (Axiom A5) (110 行)
└── LadyzhenskayaMain.v    # 装载所有 Axiom, 推 Theorem QED (80 行)
```

总计: ~640 行 + _CoqProject + 编译验证脚本.

### 2.3 关键技术决策

- **使用 `mathcomp-analysis`**: Holder 空间、连续函数、函数范数都已有。无需自建 Reals.
- **作用域**: 固定 $n=3$ (CFD 经典情形) 以减少维度多态复杂度。Theorem 仍叙述为对一般 $n$ 形式化 (参数化 `n : nat`).
- **类型 vs 谓词**: 关键不等式 (抛物性) 用 `Record` (Type), 结论性 (解存在唯一) 用 `Prop`.
- **No Admitted**: 所有承认步骤用 `Axiom` + 详细 docstring 列出证明义务.
- **诚实承认**: 每个 Axiom docstring 写明"对应 Ladyzhenskaya 1968 哪一页/引理".

## 3. 不形式化部分 (诚实记录)

| 数学步骤 | 原因 | 文档位置 |
|---------|------|---------|
| Holder 紧嵌入 (Arzela-Ascoli 推广) | 需自建紧性定理 | Schauder.v header |
| Faedo-Galerkin ODE 存在性 | 需自建常微分方程定理 | Galerkin.v header |
| 抛物能量不等式 | 需自建弱时间导数 | Galerkin.v header |
| Schauder 估计证明 | 需 30+ 页 PDE | Schauder.v header |
| 抛物最大值原理 | 需 10+ 页 PDE | Uniqueness.v header |

## 4. 时间估算

| 阶段 | 内容 | 估时 |
|------|-----|------|
| Phase 1 | HolderSpace.v + ParabolicCoefficients.v | 1-2 天 |
| Phase 2 | Galerkin.v (A2, A3) | 1-2 天 |
| Phase 3 | Schauder.v (A4) | 1-2 天 |
| Phase 4 | Uniqueness.v (A5) | 1 天 |
| Phase 5 | LadyzhenskayaMain.v (QED 拼装) + 编译验证 | 1 天 |
| Phase 6 | 清理 + 文档 | 0.5 天 |
| **合计** | | **6-9 天** (乐观) |

## 5. 验证标准

- 所有 .v 文件 `coqc` 编译 0 error 0 warning (除已知 deprecation)
- `ladyzhenskaya_short_time_existence` 是 QED (reflexivity 自动推出)
- 5 个 Axiom 全部有 docstring 说明对应数学定理 + LSU 章节
- 主定理签名与数学定理一致 (输入条件 + 输出存在唯一)
