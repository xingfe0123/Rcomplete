# 球面分类定理 — Coq 形式化

**主定理**: Killing-Hopf — 紧致、单连通、常正截面曲率 3-流形 ≅ 3-球面 S³.

**状态**: 骨架 — 流形 / 度量 / 测地线 / 曲率 定义完备, 主定理为 Axiom stub.

## 文件结构

```
src/SphereClassification/
├── Topology.v             102行  拓扑空间
├── Manifold.v              81行  光滑流形
├── FundamentalGroup.v      78行  基本群 + 单连通
├── RiemannMetric.v        153行  Riemann 度量
├── RiemannTensor.v        339行  曲率张量
├── Geodesic.v             464行  测地线
├── HopfRinow.v             80行  Hopf-Rinow 定理
├── HadamardCartan.v        79行  Hadamard-Cartan 定理
├── KillingHopf.v          173行  Killing-Hopf 定理
├── BonnetMyers.v          168行  Bonnet-Myers 定理
├── InjectivityRadius.v    100行  单射半径
├── RiemannianVolume.v      97行  黎曼体积
├── SectionalCurvature.v       截面曲率 (待添加)
├── SphereTheorem.v         57行  球面分类定理 (已删除, 占位)
└── CheegerGromov.v        266行  Cheeger-Gromov 收敛
```

## 编译

```bash
cd ~/coq/py
coqc -R src/ RicciFlow -Q src/SphereClassification SphereClassification src/SphereClassification/Topology.v
```

## 与 Hamilton Ricci 流的关系

球面分类是 Ricci 流存在性证明的最终目标:
1. 抛物 PDE → Ricci 流存在性 (Ladyzhenskaya + DeTurck)
2. 曲率 pinching + 球面定理 → 流形分类
3. Hamilton 1982: 正 Ricci 曲率 3-流形 → 球面

当前 SphereTheorem.v 中的主定理已按用户要求删除 (不形式化).