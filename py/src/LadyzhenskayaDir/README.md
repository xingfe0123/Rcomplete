# Ladyzhenskaya 经典线性抛物 PDE 短时解存在性定理 — 形式化

目标定理: Ladyzhenskaya-Solonnikov-Ural'ceva, *Linear and Quasilinear Equations of Parabolic Type*, AMS 1968, **Theorem III.6.1** (p.320).

陈述：若 $a^{ij}, b^i, c, f \in C^{\alpha,\alpha/2}(\overline{Q_T})$，严格抛物，初值 $\phi \in C^{2+\alpha}(\overline{\Omega})$ 满足边界 $\phi=0$ 于 $\partial\Omega$，则存在 $T_0 \in (0,T)$，初边值问题

$$\partial_t u - a^{ij}\partial_{ij}u - b^i\partial_i u + cu = f, \quad u(x,0) = \phi, \quad u|_{\partial_p Q_T}=0$$

在 $C^{2+\alpha, 1+\alpha/2}(\overline{Q_{T_0}})$ 中有**唯一解**。

## 形式化方案 (路径 A — 5 Axiom 分解)

| Axiom | 对应数学步骤 | 物理合理性 |
|-------|------------|----------|
| `coeff_Holder_regularity` | $a^{ij}, b^i, c, f$ 的 Holder 半范有界 | 编码 Holder 空间定义 |
| `galerkin_approximation` | Faedo-Galerkin 逼近存在 | ODE 存在性 |
| `energy_estimate_uniform` | 抛物能量估计 | 抛物最大值原理 |
| `schauder_interior_estimate` | Schauder $C^{2+\alpha, 1+\alpha/2}$ 估计 | Schauder 定理 |
| `schauder_global_uniqueness` | 抛物极值原理 -> 唯一性 | Hopf 引理 |

主定理: `ladyzhenskaya_short_time_existence` **QED** (5 Axiom + reflexivity 拼装).

## 文件结构

```
src/LadyzhenskayaDir/
├── HolderSpace.v          # Holder 半范 / 抛物 Holder 空间
├── ParabolicCoefficients.v # 严格抛物性 + 输入系数
├── Galerkin.v             # Galerkin 逼近 + 能量估计
├── Schauder.v             # Schauder 内估计
├── Uniqueness.v           # 抛物最大值原理 + 唯一性
└── LadyzhenskayaMain.v    # 主定理 QED 拼装
```

## 编译

```bash
coq_makefile -f _CoqProject -o Makefile
make -j
```

或单文件：
```bash
coqc -Q src Ladyzhenskaya -Q src/LadyzhenskayaDir LadyzhenskayaDir src/LadyzhenskayaDir/HolderSpace.v
```

## 致谢

本形式化使用 [mathcomp-analysis](https://github.com/math-comp/analysis) 库 (1.3.1) 与 Coq 8.18.

详细计划见 `.hermes/plans/ladyzhenskaya_plan.md`.
