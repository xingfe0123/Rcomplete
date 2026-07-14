# Coq 数学基础项目 (/home/luoxing/coq) — 概览

**最后更新**: 2026-07-14 (100% 编译达成)
**项目位置**: `/home/luoxing/coq/`
**主项目**: `/home/luoxing/coq/py/` (Ladyzhenskaya/Hilbert 形式化)
**Rocq 版本**: 9.1.1 (Linux, ~/.opam/default)

---

## 项目结构

根目录包含早期探索性工作（草稿/研究笔记），主项目开发在 `py/` 子目录。

### 根目录文件

| 文件 | 状态 | 说明 |
|------|------|------|
| `topology.v` | ✅ 草稿完成 | 拓扑结构公理 + 紧性/正规空间定义 (1206 行) |
| `top.v` | ⚠️ 部分完成 | 光滑流形定义 + 函数芽空间 (416 行，含未完成的 germ_mul) |
| `functional_analysis.v` | ⚠️ 部分完成 | Frechet 空间 + 半范数 (722 行，多处 Admitted) |
| `analysis.v` | ⚠️ 部分完成 | 全序/域/有序域结构 + 上下确界 (418 行，Axiom 占位) |
| `metric.v` | ⚠️ 草稿 | 向量空间/度量空间/完备性 (119 行) |
| `tensor.v` | ⚠️ 草稿 | 张量 + 双线性映射 (217 行) |
| `analytic.v` | ⚠️ 草稿 | 实分析 + C¹ 函数 + R² 距离 (152 行) |
| `lie.v` | ⚠️ 草稿 | Lie 代数 + 同构 + 子代数 (118 行) |
| `hello_word.v` | ❌ 占位 | `Admitted` 占位 |
| `vector_space.v` | ❌ 空文件 | 0 字节 |
| `Type` | ❌ 空文件 | 0 字节 |
| `Hilbert_68_Theorems.txt` | ✅ 参考 | Hilbert 68 定理中文对照 (342 行) |
| `theories/ZornsLemma/` | ✅ 依赖库 | 序数/基数/Zorn 引理 (43 文件, 556KB) |

### 主项目子目录

| 子目录 | 说明 | 状态 |
|--------|------|------|
| `py/` | Ladyzhenskaya PDE + Hilbert 几何基础 (主开发) | **60/60 编译通过 (100%)** ✅ |
| `py/src/` | 7 个模块, 60 个 .v 源文件 | |
| `py/README.md` | 项目文档 | 存在 |
| `py/plan.md` | 详细进展与规划 | ✅ **本次已同步更新** |
| `py/AxiomAudit.md` | Axiom 审计报告 | 存在 (2026-06-19) |

---

## 当前编译状态 (2026-07-14 实测)

**里程碑: 100% 全量编译通过** ✅

- 修复 QPlane.v 后实现全量 60/60 编译
- 旧阻塞 (CongruenceTheorem 语法错误、QPlane mkCongruence 缺字段) 均已解决
- 所有 6 个模块、全部 60 个源文件编译通过

---

## 问题总结

1. **主项目**: `py/` 子目录已实现 **100% 全量编译**，详见 `py/plan.md`
2. **根目录草稿**: 多个 .v 文件包含大量 `Admitted` 和 `Axiom` 占位，未持续维护
3. **空文件**: `vector_space.v` (1 字节)、`Type` (0 字节)、`hello_word.v` (Admitted)
4. **锁文件**: `.#metric.v#`, `.#vector_space.v#` (编辑器锁)

## 建议

- 主开发在 `py/`，根目录文件可作为备用草稿或归档
- QPlane.v 修复后即可实现全量编译
- 下一阶段重点是 Admitted/Axiom QED 化 (81 Admitted, 312 Axiom)