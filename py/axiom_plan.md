# Hilbert 几何形式化 — Axiom 攻克计划

> 统计基准: 2026-07-20, QPlane.v 已简化至 ~615 行
> 总计: ~47 Axiom + ~32 Admitted (跨 15 个 .v 文件)

## 一、QPlane.v (27 Axiom + 2 Admitted)

### A 类: 可 Qed (有明确证明路径)

| # | 名称 | 当前 | 策略 | 备注 |
|---|------|------|------|------|
| 1 | Q_bet_sym | Axiom→Qed | 取 t'=1-t, nra 证 0<1-t<1, Qeq_trans+nra 证坐标 | **已验证通过** (需写入) |
| 2 | Q_bet_nondeg | Axiom→Qed | nra+Qeq_dec+Qmult_integral_l, 分情况 t=0/t=1 矛盾 | **已验证通过** (需写入, 修复 `by` 关键字问题) |
| 3 | Q_line_two_pts | Axiom→Qed | 需给 QLine 加约束 qline_dir≠(0,0), 然后取 t=0,t=1 构造两点 | 需改 QLine 定义 |
| 4 | Q_ray_valid | Axiom→Qed | 依赖 Q_line_two_pts, qray_origin 在 qray_line 上 | 需改 QRay 定义 |
| 5 | Q_segValid | Axiom→Qed | seg_p≠seg_q, 依赖 Q_bet_nondeg | 需改 QSegment 定义 |
| 6 | side_valid | Admitted→Qed | 依赖 Q_segValid + Q_bet_nondeg | |
| 7 | angle_valid | Admitted→Qed | 依赖 side_valid + Q_bet_nondeg | |

**关键发现:**
- `Opaque Qeq_eq` 必须在 nra 调用前设置, 否则 nra 搜索空间爆炸
- `destruct (Q*Q) as (bx, by)` 中 `by` 是 Rocq 9.1.1 关键字, 必须用 `(b1, b2)` 等非关键字名
- `ring` 不能直接用 Qeq 假设, 需先 `rewrite`; `nra` 可以用 Qeq 假设
- 证明 pair 相等: `destruct ... as (p1, p2); simpl; rewrite H1; rewrite H2; reflexivity`

### B 类: 难 Qed (需要非平凡构造或深层算术)

| # | 名称 | 难点 | 可能策略 |
|---|------|------|----------|
| 8 | Q_bet_on_line | 需从 QIncid 构造 t 参数 | 展开 QIncid, 用 Qeq_eq+nra |
| 9 | Q_bet_on_line_end | 同上, 边界情况 t=0/t=1 | 类似 Q_bet_on_line |
| 10 | Q_bet_between | 需证存在 t∈(0,1) | 构造 t, 用 nra 证范围 |
| 11 | Q_bet_trans | 传递性, 需构造新 t | 两个 t 组合, nra 证范围 |
| 12 | Q_pasch | Pasch 公理, 需构造交点 | 解线性方程组, nra 证存在性 |
| 13 | Q_I2 | 直线唯一性 | 需证两条 QLine 参数化后重合, 用 Qeq_eq |
| 14 | Q_IV1 | 过直线外一点作平行线 | 构造方向向量, 需 Q_I2 |
| 15 | Q_IV2 | 平行唯一性 | 需 Q_I2 + 方向向量相等 |
| 16 | Q_archimedes | Q 上的 Archimedes 性质 | lia 在 Q_scope 下无法处理 Z.pos den, 需手动 Z 算术 |

### C 类: 不可 Qed (模型退化或设计选择)

| # | 名称 | 原因 | 备注 |
|---|------|------|------|
| 17 | Qeq_eq | Q 的 proof irrelevance | 桥接公理, 等价于 Q 上的 UIP, 必须保持 Axiom |
| 18 | Q_I7 | Q² 是 2D, I-7 需要 3D | 需 R³ 模型才能消除 |
| 19 | Q_I8 | Q² 是 2D, I-8 需要 3D | 同上 |
| 20 | Q_III1~III7 | 合同公理, 需距离/角度定义 | 需先定义 QCongSeg/QCongAng 的计算实现 |
| 21 | QCongAng | 角合同定义 | 需先给出基于 Q 算术的定义 |
| 22 | Q_cutValid | Dedekind 切割有效性 | Q 不完备, 需 R 模型 |
| 23 | Q_not_dedekind | Q 不满足 Dedekind 完备性 | 同上 |

## 二、CongruenceTheorem.v (14 Axiom + 14 Admitted)

### 抽象 Setting 中的辅助 Axiom (不能从 III1~III7 推导)

这些 Axiom 是 `Section CongruenceTheorem` 的 Parameter/假设, 不是可证明的引理:

| # | 名称 | 性质 | 备注 |
|---|------|------|------|
| 1 | exists_ray_through | III-1 的存在性部分 | 在 Q² 中可 Qed (需 Q_III1) |
| 2 | angle_copy | III-4 角合同构造 | 在 Q² 中可 Qed (需 QCongAng 定义) |
| 3 | ray_same_angle | 射线上取点不改变角合同 | **可能可 Qed** (从 angle_copy 推导) |
| 4 | cong_ang_trans | 角合同传递性 | **可能可 Qed** (从 III-6 推导) |
| 5 | cong_ang_sym | 角合同对称性 | **可能可 Qed** (从 III-6 推导) |
| 6 | cong_seg_sym1 | 线段合同对称性 | **可能可 Qed** (从 III-3 推导) |
| 7 | cong_seg_sym2 | 线段合同对称性 | **可能可 Qed** (从 III-3 推导) |
| 8 | angle_ray_unique | 角合同唯一性 | 需 III-4 唯一性 |
| 9 | ray_same_side | 射线同侧 | 需 SameSide 定义 |
| 10 | seg_nonzero | 线段非零 | **可能可 Qed** (从 Bet 定义) |
| 11 | angle_non_collinear | 角非退化 | **可能可 Qed** (从 Bet 定义) |
| 12 | ray_on_line | 射线在直线上 | **可能可 Qed** (从 Ray 定义) |
| 13 | bet_collinear | Bet 蕴含共线 | **可能可 Qed** (从 Bet+Incid 定义) |
| 14 | bet_between_on_ray | Bet 点在射线上 | **可能可 Qed** (从 Bet+Ray 定义) |

**注意:** #3~#14 在抽象 Setting 中是 Axiom, 但在 Q² 具体模型中可能可 Qed.
策略: 先在 QPlane.v 中给出这些的 Qed 版本, 然后看能否在 Setting 中推导.

### Admitted 定理 (14 个, 依赖上述 Axiom)

| # | 定理名 | 依赖 | 备注 |
|---|--------|------|------|
| 1 | theorem_18 | exists_ray_through, angle_copy | 三角形合同 SAS |
| 2 | theorem_24 | cong_seg_sym, ray_same_angle | 等腰三角形 |
| 3 | theorem_25 | theorem_24 | 角平分线 |
| 4 | theorem_26 | theorem_25 | 垂直平分线 |
| 5 | CongruenceTheorem_III5 | III-5 | 线段合同自反 |
| 6 | theorem_27 | III-6 | 角合同加法 |
| 7 | theorem_28 | theorem_27 | 角合同减法 |
| 8 | theorem_29 | theorem_28 | 角合同传递 |
| 9 | theorem_30 | theorem_29 | 角平分线唯一 |
| 10 | theorem_31 | theorem_30 | 垂直平分线唯一 |
| 11 | theorem_37 | theorem_31 | 三角形全等 SSS |
| 12 | theorem_37_SAS | theorem_18 | SAS 补充 |
| 13 | theorem_37_ASA | theorem_37 | ASA 补充 |
| 14 | theorem_37_AAS | theorem_37 | AAS 补充 |

## 三、OrderTheorem.v (5 Admitted)

| # | 定理名 | 难点 | 策 | 策略 |
|---|--------|-----|------|
| 1 | three_collinear_one_between | 中 | 依赖 Pasch/II-3, 需 Bet 传递性 |
| 2 | theorem_4 | 中 | 共线三点排序, 依赖 three_collinear_one_between |
| 3 | theorem_5_permutation | 低 | 共线四点排列, 主路径已 Qed |
| 4 | theorem_6 | 中 | 有限共线点排序, 依赖 theorem_4 |
| 5 | theorem_8_unavailable | 高 | 需 SameSide 公理系统, 当前占位 |

## 四、PascalTheorem.v (2 Axiom + 2 Admitted)

| # | 名称 | 难点 | 策略 |
|---|------|------|------|
| 1 | line_through_prop_ax | 需直线性质 | 从 Incid 定义推导 |
| 2 | two_points_unique_line | 直线唯一性 | 依赖 I-2 |
| 3 | Pascal_theorem | Admitted | 依赖合同公理 |
| 4 | Pascal_degenerate | Admitted | 退化情况 |

## 五、其他文件

| 文件 | Axiom/Admitted | 性质 | 备注 |
|------|----------------|------|------|
| ParallelTheorem.v | 3 Axiom (IV_1, IV_2, Parallel_nointersect) | 平行公理 | 在 Q² 中 IV_1 可 Qed |
| Model_Consistency.v | 1 Axiom + 2 Admitted | propositional_extensionality | 不可消除 |
| ContinuityTheorem.v | 1 Admitted | 连续性定理 | 依赖 Archimedes |
| EuclideanTheorem.v | 4 Admitted | 欧几里得定理 | 依赖合同公理 |
| DesarguesTheorem.v | 2 Admitted | Desargues 定理 | 依赖合同公理 |
| IV_Independence.v | 8 Admitted | 独立性证明 | 反例模型, 保持 Admitted |
| V1_Independence.v | 1 Admitted | V-1 独立性 | 反例模型 |
| V2_Independence.v | 3 Admitted | V-2 独立性 | 反例模型 |
| III5_Independence.v | 2 Admitted | III-5 独立性 | 反例模型 |

## 六、优先级排序

### 第一批 (低垂果实, 预计减少 ~7 Axiom)
1. Q_bet_sym → Qed (已验证)
2. Q_bet_nondeg → Qed (已验证, 需修复 `by` 关键字)
3. Q_line_two_pts → Qed (需改 QLine 定义加约束)
4. Q_ray_valid → Qed (依赖 #3)
5. Q_segValid → Qed (依赖 #2)
6. side_valid → Qed (依赖 #5)
7. angle_valid → Qed (依赖 #6)

### 第二批 (中等难度, 预计减少 ~5 Axiom)
8. Q_bet_on_line → Qed
9. Q_bet_on_line_end → Qed
10. Q_bet_between → Qed
11. bet_collinear → Qed (CongruenceTheorem.v)
12. bet_between_on_ray → Qed (CongruenceTheorem.v)

### 第三批 (高难度, 需要新定义/构造)
13. Q_bet_trans → Qed
14. Q_pasch → Qed
15. Q_I2 → Qed
16. Q_IV1, Q_IV2 → Qed

### 不攻克 (保持 Axiom/Admitted)
- Qeq_eq (桥接公理, 必须保持)
- Q_I7, Q_I8 (3D 退化)
- Q_III1~III7, QCongAng (需合同公理计算定义)
- Q_cutValid, Q_not_dedekind (需 R 模型)
- Q_archimedes (Q 算术深层问题)
- IV_Independence, V1/V2/III5 独立性 (反例模型, Admitted 正确)
- Model_Consistency.v 的 propositional_extensionality (逻辑公理)

## 七、关键证明模式备忘

```
(* 模式1: Qeq → Leibniz eq + ring *)
assert (x = y).
{ destruct ... as (p1, p2). simpl in *.
  rewrite (Qeq_eq _ _ Hqeq); ring. }

(* 模式2: nra 处理 Qeq 假设 *)
assert (t * (fst C - fst A) == 0) by nra.

(* 模式3: Qmult_integral_l 消去非零因子 *)
assert (t = 0) by (apply (Qmult_integral_l x); [exact Hxn | apply Qeq_eq; exact H]).

(* 模式4: Opaque Qeq_eq 防止 nra 爆炸 *)
Opaque Qeq_eq.  (* 在文件开头设置 *)

(* 模式5: pair 相等 *)
assert (B = A).
{ assert (fst B = fst A) by (...).
  assert (snd B = snd A) by (...).
  destruct B as (b1, b2). destruct A as (a1, a2). simpl in *.
  rewrite H1. rewrite H2. reflexivity. }

(* 注意: destruct (Q*Q) 不能用 by/ax/ay 等关键字作变量名! *)
```
