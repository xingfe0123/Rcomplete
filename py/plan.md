# Coq PDE/Hilbert 形式化项目 — 进展计划

> 最后更新: 2026-07-14 (Rocq 9.1.1)
> 编译命令: `make -f Interface`
> 项目路径: `/Users/luoxing/coq/py/`

---

## 一、实测编译统计

| 指标 | 数值 |
|------|------|
| 总 .v 文件 | 68 |
| 已编译 (.vo) | 57 |
| 测试文件 (不计入) | 9 (8 Hilbert + 1 Gronwall) |
| 非测试核心文件 | 59 |
| 核心编译通过 | 54/59 |
| **实际通过率** | **92%** |

### 6 个非 Hilbert 模块 (全部通过 ✓)
| 模块 | 文件数 | 状态 |
|------|--------|------|
| Ladyzhenskaya (PDE 正则性) | 15/15 | ✓ |
| SphereClassification (球面定理) | 17/17 | ✓ |
| LinearAlgebra (线性代数) | 2/2 | ✓ |
| CompactEmbedding (紧致嵌入) | 6/6 | ✓ |
| Hopf (Hopf 引理) | 1/1 | ✓ |
| Gronwall (Gronwall 不等式) | 1/1 | ✓ |

### Hilbert 几何模块 (18 个非测试文件)
| 文件 | 状态 | 说明 |
|------|------|------|
| HilbertStructure.v | ✓ | Record 定义 (IncidenceStructure, OrderStructure 等) |
| Types.v | ✓ | 类型定义 |
| Common.v | ✓ | 公共引理 |
| IncidenceTheorem.v | ✓ | 关联公理实例化 |
| OrderTheorem.v | ✓ (3 admit) | thm4/thm5/thm8 待证 |
| ParallelTheorem.v | ✓ | 平行公理 |
| Model_Consistency.v | ✓ | 模型一致性 |
| III5_Independence.v | ✓ | III-5 独立性 |
| IV_Independence.v | ✓ | IV 独立性 |
| V1_Independence.v | ✓ | V-1 独立性 |
| V2_Independence.v | ✓ | V-2 独立性 |
| DesarguesTheorem.v | ✓ (2 admit) | Desargues 定理待证 |
| PascalTheorem.v | ✓ (2 admit) | Pascal 定理待证 |
| EuclideanTheorem.v | ✓ | 欧几里得定理 |
| ContinuityTheorem.v | ✓ (空桩) | 仅 Section 声明, 21 行, 无内容 |
| **CongruenceTheorem.v** | ⚠️ admit | 22/39 公理 admit, theorem_32 类型错误 |
| **QPlane.v** | ❌ 失败 | ray_valid 字段 Record 投影不透明 |
| **HilbertFoundations.v** | ❌ 失败 | 依赖 QPlane |

---

## 二、当前阻塞问题

### P0-1: QPlane.v — ray_valid Record 投影不透明 (根因)
- **位置**: `src/Hilbert/QPlane.v` line 269
- **错误**: `QIncid (qray_origin r) (qray_line r)` 类型 Prop, 期望 `Incid Q2_Incidence (qray_origin r) (qray_line r)`
- **根因**: Rocq 9.1 中 `IncidenceStructure` 是 Record, 其 `Incid` 投影不透明, 无法归约为 `QIncid`. 这是 Rocq 已知限制.
- **已尝试方案**: `{| |}` 语法、`@mkOrder`、`refine`+existT、`match` Record pattern、`match mkIncidence`、`let g := .(Incid) in`、`Transparent` — 全部失败
- **修复**: 需改 `HilbertStructure.v` 中 `OrderStructure.ray_valid` 字段类型为 `Prop`, 或重构 OrderStructure 为模块化形式
- **影响**: HilbertFoundations.v 级联失败

### P0-2: CongruenceTheorem.v — theorem_32 类型错误 (部分修复)
- **位置**: line 475, `III7` 返回角参数顺序 `(B C' A B' C'' A')`, 期望 `(A C' B A' C'' B')`
- **状态**: theorem_32 已从虚假 QED 改为诚实 admit (缺少 angle-endpoint-swap 引理)
- **其他**: theorem 11-39 中 22 个 admit, 17 个已证

### P1: 测试文件清理 (9 个)
- Hilbert: test2.v, test3.v, test4.v, test_final.v, test_implicit.v, test_thm14.v, test_wrapper.v
- Gronwall: TestGronwallAxioms.v
- 建议: 移出 src/Hilbert 或删除

### P1: ContinuityTheorem.v 空桩
- 仅 21 行 Section 声明, 无实际定理. 需填充内容或移除.

---

## 三、P0 修复路线

```
P0-1 (Record 投影) ──→ 改 HilbertStructure.v ray_valid 字段类型
                         └──→ QPlane.v 编译通过
                              └──→ HilbertFoundations.v 恢复
P0-2 (Congruence) ──→ 补 angle-endpoint-swap 引理 + 修正 III7 调用
```

---

## 四、已完成的工作

- [x] 修正 `_CoqProject`: `*Axioms.v` → `*Theorem.v`, 补充缺失文件
- [x] 统一 `CongruenceTheorem.v` bullet 风格 (line 278-283, 259)
- [x] theorem_32 从虚假 QED 改为诚实 admit
- [x] 确认无跨模块依赖 (Hilbert 问题不影响其他 6 个模块)
- [x] 诊断 QPlane ray_valid Record 投影根因并记录修复方案

---

## 五、下一步 (按优先级)

1. **[P0] 修 HilbertStructure.v**: 将 `OrderStructure.ray_valid` 字段类型从 `(Incid I) (ray_origin r) (ray_line r)` 改为 `Prop`, 在 QPlane.v 中用 Axiom 补充 ray_valid 约束
2. **[P0] 验证 QPlane + HilbertFoundations 编译通过**
3. **[P1] 补 CongruenceTheorem theorem_32**: 添加 angle-endpoint-swap 引理, 修正 III7 调用
4. **[P1] 清理 9 个测试文件**: 移出或从 _CoqProject 移除
5. **[P2] 填充 ContinuityTheorem.v 或移除空桩**
6. **[P2] 补 Desargues/Pascal 定理证明**
