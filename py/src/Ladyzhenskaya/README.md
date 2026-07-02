# Ladyzhenskaya 抛物 PDE 存在性 — Coq 形式化

**目标定理**: Ladyzhenskaya-Solonnikov-Ural'ceva 1968 *Linear and Quasilinear Equations of Parabolic Type* Theorem III.6.1:
若 a^{ij}, b^i, c, f ∈ C^{α,α/2}(Q̅_T), 严格抛物, 初值 φ ∈ C^{2+α}(Ω̅), φ=0 于 ∂Ω,
则 ∃T₀∈(0,T) 使初边值问题在 C^{2+α,1+α/2}(Q̅_{T₀}) 中有**唯一解**.

**状态**: 骨架 — 主定理 QED 拼装完成, 依赖 5 个 D Axiom.

## 文件结构

```
src/Ladyzhenskaya/
├── HolderSpace.v           318行   抛物 Hölder 空间 C^{α,α/2}
├── Derivatives.v           267行   偏导数 + 抛物算子
├── ParabolicCoefficients.v 134行   严格抛物性 + 输入系数
├── SobolevSpace.v          386行   L² → H¹ → Rellich 紧性
├── EllipticParabolicAnalysis.v 275行   符号分析 + 极值点性质
├── CaccioppoliDeGiorgiSobolev.v 225行   Caccioppoli 不等式 + De Giorgi 迭代
├── HopfBoundaryAnalysis.v  303行   障碍函数分析法
├── MoserIteration.v        390行   Moser 迭代 + Harnack
├── Schauder.v              114行   Schauder 内估计
├── ABPCalderonZygmund.v    345行   ABP 估计 + Calderon-Zygmund
├── Galerkin.v              167行   Galerkin 逼近 + 能量估计
├── Uniqueness.v            1303行  最大值原理 + 唯一性 (最大文件)
├── DeTurck.v               172行   DeTurck trick → 抛物 PDE
├── RicciFlow.v             277行   Ricci 流存在性
└── LadyzhenskayaMain.v     68行   主定理 QED 拼装
```

## 编译

```bash
cd ~/coq/py
coqc -R src/ RicciFlow src/Ladyzhenskaya/HolderSpace.v
```

需先编译 HolderSpace.vo 等依赖。

## 依赖

- Coq 8.18
- mathcomp (部分文件)
- Ladyzhenskaya.HolderSpace 被多数子模块引用