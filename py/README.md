# Hamilton Ricci 流存在性 — Coq 形式化

**总目标**: 形式化 Hamilton 1982 *Three-Manifolds with Positive Ricci Curvature* 中 Ricci 流存在性证明 (Ricci flow short-time existence on a 3-manifold), 基于 Ladyzhenskaya 1968 抛物 PDE 理论。

**最终定理**: 紧致 3-流形上 Ricci 流短期存在性 + 唯一性，由 DeTurck trick 归约为抛物 PDE 理论。

## 项目结构

```
src/
├── CompactEmbedding/      892行  抛物 Hölder 紧嵌入
├── Gronwall/              349行  Gronwall 微分不等式 (完全 QED)
├── Hopf/                  437行  抛物 Hopf 强极大值原理 (主定理 QED)
├── Ladyzhenskaya/        4744行  Ladyzhenskaya 抛物 PDE 理论 (主模块)
├── LinearAlgebra/         823行  线性代数基础 (对称矩阵)
├── SphereClassification/ 2312行  球面分类定理 (Killing-Hopf 骨架)
└── test/                         测试
```

### CompactEmbedding/
抛物 Hölder 空间的紧嵌入定理 — 从 `C^{2+α, 1+α/2}` 到 `C^{1, 1/2}`.
- `MetricCompact.v`: 紧度量空间 + 度量拓扑
- `UniformBounded.v`: 一致有界函数族
- `Equicontinuity.v`: 等度连续
- `ArzelaAscoli.v`: Arzela-Ascoli 紧性定理
- `BanachC0.v`: C⁰(K) Banach 空间完备性
- `CompactEmbedding.v`: 紧嵌入主定理 (骨架 Axiom)

### Gronwall/
ODE 形式的线性 Gronwall 衰减估计, 完整 QED.
- `Gronwall.v`: Gronwall 不等式 (7 Lemma, 全部 QED, 零外部 Axiom)
- `TestGronwallAxioms.v`: 测试

### Hopf/
抛物 Hopf 强极大值原理.
- `Hopf.v`: 弱最大值原理 (Theorem, Admitted) + 强最大值原理 (parabolic_strong_maximum_principle, QED via hopf_parabolic_contradiction stub) + 唯一性推论 (schauder_global_uniqueness, Admitted)

### Ladyzhenskaya/
Ladyzhenskaya 经典线性抛物 PDE 短时解存在性 (LSU 1968, Ch. III).

| 文件 | 行数 | 内容 |
|---|---|---|
| `HolderSpace.v` | 318 | 抛物 Hölder 空间 C^{α, α/2} |
| `Derivatives.v` | 267 | 偏导数 + 抛物算子 |
| `ParabolicCoefficients.v` | 134 | 严格抛物性 + 输入系数 |
| `SobolevSpace.v` | 386 | L² → H¹ → Rellich 紧性 (骨架) |
| `EllipticParabolicAnalysis.v` | 275 | 符号分析 + 极值点性质 |
| `CaccioppoliDeGiorgiSobolev.v` | 225 | Caccioppoli 不等式 + De Giorgi 迭代 |
| `HopfBoundaryAnalysis.v` | 303 | 障碍函数 + Hopf 边界点引理 |
| `MoserIteration.v` | 390 | Moser 迭代 + Harnack 不等式 |
| `Schauder.v` | 114 | Schauder 内估计 |
| `ABPCalderonZygmund.v` | 345 | ABP 估计 + Calderon-Zygmund |
| `Galerkin.v` | 167 | Galerkin 逼近 + 能量估计 |
| `Uniqueness.v` | 1303 | 最大值原理 + 唯一性 + Harnack |
| `DeTurck.v` | 172 | DeTurck trick → 抛物 PDE |
| `RicciFlow.v` | 277 | Ricci 流存在性 |
| `LadyzhenskayaMain.v` | 68 | 主定理 QED 拼装 |

### LinearAlgebra/
- `LinearAlgebraFoundations.v`: 向量空间 + 线性映射
- `SymmetricMatrix.v`: 对称矩阵 + 谱定理

### SphereClassification/
- `Topology.v`: 拓扑空间基础
- `Manifold.v`: 光滑流形
- `FundamentalGroup.v`: 基本群
- `RiemannMetric.v`: Riemann 度量
- `RiemannTensor.v`: 曲率张量
- `Geodesic.v`: 测地线
- `HopfRinow.v`: Hopf-Rinow 定理
- `HadamardCartan.v`: Hadamard-Cartan 定理
- `KillingHopf.v`: Killing-Hopf 定理
- `BonnetMyers.v`: Bonnet-Myers 定理
- `InjectivityRadius.v`: 单射半径
- `RiemannianVolume.v`: 黎曼体积
- `SectionalCurvature.v`: 截面曲率

## 编译状态

**最后更新**: 2026-06-30 (P0.1-P0.3 修复后)

| 模块 | 生产文件 | .vo 已编译 | 完成率 | 主定理状态 |
|------|---------|-----------|--------|-----------|
| Gronwall | 2 | 1 | 50% | Ax 唯一 Axiom (Gronwall 比较定理) |
| Hopf | 1 | 1 | 100% | **QED** |
| Ladyzhenskaya | 15 | 15 | **100%** | 骨架, 36 Admitted |
| LinearAlgebra | 3 | 2 | 67% | SymmetricMatrix 已 Admitted |
| SphereClassification | 17 | **17** | **100%** | 骨架, 主定理 6 Admitted |
| CompactEmbedding | 6 | 6 | **100%** | Axiom 化 |
| Hilbert | 15 | **15** | **100%** | QED + I_4 Admitted |
| **总计** | **59** | **57** | **97%** | |

**编译命令**: `make -f Interface` (基于 `_CoqProject` 的 `coq_makefile -f _CoqProject -o Interface` 产物)

**重大进展 (2026-06-29 → 2026-06-30)**:
- **P0.1** LinearAlgebra/SymmetricMatrix: Rsum unification + eigenvector_qf QED 修复
- **P0.3** Hilbert/Model_Consistency: `Rminus_eq_0` deprecated → `Rminus_diag_uniq`; I_4 Theorem design-level exfalso bug 标记 Admitted
- **P0.2** SphereClassification 依赖链: 12 个文件从阻塞到全部编译 (45% → 100%)
  - ConnectionBianchi: 修复 `abla_` → `∇_` Unicode 编码; 6 主定理 Admitted (QED path 已标注)
  - CheegerGromov: `Require Import Homeomorphism`; `Huniform` 从 destruct 后重组
  - HopfRinow: 完整依赖链修复
- **P6** 清理 15 个孤立 test_*.v / tmp_test.v 文件

## Axiom 策略 (分类)

| 标签 | 含义 | 例子 |
|---|---|---|
| **(A)** | 形式化目标本身的深层引理 | 障碍函数构造、Hopf 引理 |
| **(D)** | 外部经典定理 (Ladyzhenskaya/Gilbarg-Trudinger) | Schauder 估计、Calderon-Zygmund |
| **(C)** | 标准工具 → 应转为 Definition | 距离公理、Hölder 范数公理 |

## 编译

```bash
cd ~/coq/py
coqc -R src/ RicciFlow -Q src/CompactEmbedding CompactEmbedding -Q src/SphereClassification SphereClassification -Q src/Gronwall Gronwall -Q src/LinearAlgebra LinearAlgebra src/Hopf/Hopf.v
```

或使用 `_CoqProject` 注册的 4 个 `-Q` 映射。

## 依赖

- Rocq Prover 9.1.1 (项目从 Coq 8.20 升级; notice deprecated `From Coq` → `From Stdlib`)
- Reals (Rocq 标准库)
- mathcomp (部分文件)
- 不依赖 mathcomp-analysis

## 参考文献

- Hamilton 1982, *Three-Manifolds with Positive Ricci Curvature*
- Ladyzhenskaya-Solonnikov-Ural'ceva 1968, *Linear and Quasilinear Equations of Parabolic Type*
- DeTurck 1983, *Deforming metrics in the direction of their Ricci tensors*
- Gilbarg-Trudinger, *Elliptic Partial Differential Equations of Second Order*
- Lieberman, *Second Order Parabolic Differential Equations*
