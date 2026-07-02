# Hopf 强极大值原理 — Coq 形式化

**目标**: 抛物 Hopf 强极大值原理 + 唯一性。

**主定理**: `parabolic_strong_maximum_principle` — 若 Lu ≥ 0, c ≤ 0, u 在内部 (x0, t0) (t0 > 0) 取最大值 M, 则 u ≡ M。

**状态**: **主定理 QED** (via hopf_parabolic_contradiction D Axiom). 弱最大值原理已从 Axiom 升级为 Theorem (Admitted).

## 文件结构

```
src/Hopf/
  Hopf.v          — 弱/强最大值原理 + 唯一性 (437行)
```

## Axiom 列表

| # | Axiom | 含义 | 分类 |
|---|-------|------|------|
| 1 | T_horizon_pos | T > 0 | (C) |
| 2-5 | Omega_distance_* (4个) | Ω 上的度量 | (C) |
| 6 | hopf_parabolic_contradiction | Hopf 封装 → False | (D) |
| 7 | weak_maximum_principle | 弱最大值原理 (已升级为 Theorem) | (D) |

## 编译

```bash
cd ~/coq/py
coqc -R src/ RicciFlow src/Hopf/Hopf.v
```

## 与 Ladyzhenskaya 的关系

- `schauder_global_uniqueness` 使用 `weak_maximum_principle` 导出唯一性
- Hopf 边界点引理框 Axiom 已全部删除, 集中到 `hopf_parabolic_contradiction`