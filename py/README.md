# 抛物 Holder 紧嵌入 — Coq 形式化

**目标**: 形式化经典 Arzela-Ascoli 紧嵌入定理, 这是 Ladyzhenskaya 1968 抛物 PDE 短时存在性证明的核心组件.

**主定理**: $C^{2+\alpha, 1+\alpha/2}(\overline{Q_T})$ 紧嵌入到 $C^{1, 1/2}(\overline{Q_T})$.

**方案**: 路径 A — 6 阶段完整形式化, 12-15 天.

**Axiom 估计**: 1-2 个 (Bolzano-Weierstrass + Arzela-Ascoli 整合).

## 文件结构

```
src/CompactEmbeddingDir/
├── MetricCompact.v       # 阶段 1: 紧集 + 度量
├── UniformBounded.v      # 阶段 2: 有界函数族 + 背叠性
├── Equicontinuity.v      # 阶段 3: 等度连续
├── ArzelaAscoli.v        # 阶段 4: Arzela-Ascoli 定理
├── BanachC0.v            # 阶段 5: C^0(K) 完备性
└── CompactEmbedding.v    # 阶段 6: 紧嵌入主定理 QED
```

## 当前状态

- 阶段 1 (MetricCompact.v) **本次会话交付**
- 阶段 2-6 后续会话

## 编译

```bash
cd ~/coq/py
coq_makefile -f _CoqProject -o Makefile
make -j
```

或单文件:
```bash
coqc -Q src CompactEmbedding src/CompactEmbeddingDir/MetricCompact.v
```

## 依赖

- Coq 8.18
- Reals (Coq 标准库)
- 不依赖 mathcomp-analysis (本项目独立)

## 详细计划

见 `.hermes/plans/compact_embedding_plan.md`.

## 致谢

- Ladyzhenskaya 1968, "Linear and Quasilinear Equations of Parabolic Type"
- Ladyzhenskaya-Solonnikov-Ural'ceva 1968, *Linear and Quasilinear Equations of Parabolic Type* (Chapter III)
- Arzela 1882, Ascoli 1883 (紧性定理)
- 风格参照: `~/coq/metric.v`, `~/coq/functional_analysis.v`
