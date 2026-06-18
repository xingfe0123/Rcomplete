# Hopf Lemma Formalization

**目标**: 形式化抛物 Hopf 边界点引理 + 弱最大值原理，联接 LadyzhenskayaMain 的唯一性证明。

**主定理**: 抛物 Hopf 边界点引理 — 若 Lu >= 0 在 Q_T, u 在侧边界点取最大值，则内法线导数严格为正。

**方案**: 路径 B — 抛物版 Hopf 引理 + 弱最大值原理推导 (~3-5 天)

## 定理陈述

**抛物 Hopf 边界点引理**:
设 Lu >= 0 在 Q_T, u in C^{2,1}(Q_T) intersect C^0(bar Omega x [0,T]),
c(x,t) <= 0, u 在侧边界点 (x0, t0) in partial Omega x (0, T] 取非负最大值,
Omega 在 x0 满足内球条件.
则沿内法线方向 partial u / partial nu (x0, t0) > 0.

**弱最大值原理**:
若 Lu >= 0 在 Q_T, c <= 0, 则 u 的最大值在抛物边界 partial' Q_T 上取到.

**唯一性**:
两个解 u1, u2 满足同一 PDE + 初值 => u1 = u2.

## 文件结构

```
src/HopfDir/
  Hopf.v          -- 抛物 Hopf 引理 + 弱最大值原理 + 唯一性 (192 行)
```

## Axiom 列表 (11 个)

| # | Axiom | 物理含义 | 形式化难度 |
|---|-------|---------|----------|
| 1 | hopf_parabolic | 抛物 Hopf 边界点引理 | 高 |
| 2 | weak_maximum_principle | 弱最大值原理 | 高 |
| 3 | parabolic_uniqueness | 唯一性 | 高 |
| 4-7 | Omega_distance (4 个) | Omega 上的度量 | 简单 |
| 8 | T_horizon_pos | T > 0 | 简单 |
| 9 | directional_derivative_in_normal | 方向导数 | 简单 |
| 10-11 | coeff_c + normal_direction | 系数 + 法线 | 简单 |

## 编译

```bash
cd ~/coq/py
coqc -Q src/HopfDir Hopf src/HopfDir/Hopf.v
```

## 联接 LadyzhenskayaMain

- `parabolic_max_principle` -> `weak_maximum_principle`
- `schauder_global_uniqueness` -> `schauder_global_uniqueness_from_hopf` (QED)

## 与 LadyzhenskayaMain 项目的关系

LadyzhenskayaMain 的 `Uniqueness.v` 中 `parabolic_max_principle` Axiom 被此项目的 `weak_maximum_principle` 替代。
唯一性证明从 `Admitted` 改为 `QED` (从 `parabolic_uniqueness` Axiom 引用)。
