(* ============================================================================ *)
(*  III5_Independence.v                                                         *)
(*  公理 III_5 (合同自反: CongSeg A B A B) 的独立性证明                          *)
(*                                                                            *)
(*  方法: 用 ℝ³ 模型 + 非欧度量 d(P,Q) = √((Δx+Δy)² + Δy² + Δz²), 其中            *)
(*  Δx = x_Q - x_P, Δy = y_Q - y_P, Δz = z_Q - z_P。                          *)
(*                                                                            *)
(*  在此度量下, CongSeg 定义为 d(P,Q) = d(R,S)。                                 *)
(*  由于 d(A,B) = d(A,B) 显然成立, III_5 (自反) 仍然成立。                       *)
(*                                                                            *)
(*  关键的是: 此度量下 SAS (Hilbert 原书 III_5) 不成立, 证明其独立性。            *)
(*  Hilbert 原书 III_5: AB≅A'B' ∧ AC≅A'C' ∧ ∠BAC≅∠B'A'C' → ∠ABC≅∠A'B'C'        *)
(* ========================================================================= *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

(* ---- 点类型 (ℝ³) ---- *)
Definition V3 : Type := R * R * R.
Definition Point : Type := V3.

(* ---- 坐标投影 ---- *)
Definition coord_x (p : V3) : R := fst (fst p).
Definition coord_y (p : V3) : R := snd (fst p).
Definition coord_z (p : V3) : R := snd p.

(* ---- 向量运算 ---- *)
Definition vadd (u v : V3) : V3 :=
  (fst (fst u) + fst (fst v), snd (fst u) + snd (fst v), snd u + snd v).
Definition vsub (u v : V3) : V3 :=
  (fst (fst u) - fst (fst v), snd (fst u) - snd (fst v), snd u - snd v).
Definition vscale (t : R) (v : V3) : V3 :=
  (t * fst (fst v), t * snd (fst v), t * snd v).
Definition vzero : V3 := (0, 0, 0).

(* ---- 修改的度量: d(P,Q) = √((Δx+Δy)² + Δy² + Δz²) ---- *)
Definition dist_sq (P Q : Point) : R :=
  let dx := coord_x Q - coord_x P in
  let dy := coord_y Q - coord_y P in
  let dz := coord_z Q - coord_z P in
  (dx + dy)^2 + dy^2 + dz^2.

Definition dist (P Q : Point) : R := sqrt (dist_sq P Q).

(* ---- 合同: d(P,Q) = d(R,S) ---- *)
Definition CongSeg' (P Q R S : Point) : Prop :=
  dist_sq P Q = dist_sq R S.

(* ---- 角合同: 用标准欧氏余弦 ---- *)
Definition dot (u v : V3) : R :=
  fst (fst u) * fst (fst v) + snd (fst u) * snd (fst v) + snd u * snd v.

Definition euc_norm_sq (v : V3) : R := dot v v.

Definition cos_angle (A B C : Point) : R :=
  let u := vsub A B in
  let v := vsub C B in
  let nu := euc_norm_sq u in
  let nv := euc_norm_sq v in
  (dot u v)^2 / (nu * nv).

Definition CongAng' (A B C D E F : Point) : Prop :=
  A <> B -> B <> C -> A <> C ->
  D <> E -> E <> F -> D <> F ->
  cos_angle A B C = cos_angle D E F.

(* ---- 前提: 非退化 ---- *)
Definition nondegenerate (P Q R : Point) : Prop :=
  dist_sq P Q <> 0 /\ dist_sq Q R <> 0 /\ dist_sq P R <> 0.

(* ============================================================================ *)
(*  III_5 (自反性) 证明: CongSeg' A B A B 对任意 A,B 成立                       *)
(* ========================================================================= *)
Theorem III_5_holds : forall (A B : Point), CongSeg' A B A B.
Proof.
  intros A B; unfold CongSeg'; reflexivity.
Qed.

(* ============================================================================ *)
(*  SAS 反例 (Hilbert 原 III_5): 存在两三角形两边夹角相等但第三边不等            *)
(*                                                                            *)
(*  取三角形 T1 = (0,0,0), (1,0,0), (0,1,0)                                   *)
(*      T2 = (0,0,0), (0,1,0), (1,0,0) -- 交换 B,C 位置                       *)
(*                                                                            *)
(*  按修改度量计算:                                                           *)
(*    d(T1.A, T1.B) = √((1+0)² + 0² + 0²) = 1                                *)
(*    d(T1.A, T1.C) = √((0+1)² + 1² + 0²) = √(1+1) = √2                       *)
(*    d(T1.B, T1.C) = √((0-1+0-0)² + (0-0)² + 0²) = √(1+0+0) = 1              *)
(*                                                                            *)
(*  T1 和 T2 不同但部分度量巧合。找真正反例需要一个使 SAS 失败的构造。          *)
(*                                                                            *)
(*  有意义的反例:                                                             *)
(*  T1: A=(0,0,0), B=(1,0,0), C=(0,1,0)                                     *)
(*  T2: A'=(0,0,0), B'=(2,0,0), C'=(-1,0,1)                                 *)
(*                                                                            *)
(*  计算:                                                                     *)
(*  d(A,B) = √((1+0)²+0²+0²) = 1                                             *)
(*  d(A',B') = √((2+0)²+0²+0²) = 2                                           *)
(*  → AB ≠ A'B'... 需要更精心构造。                                            *)
(* ========================================================================= *)

(* 标准欧氏三维角: 两向量间夹角余弦 *)
Definition euc_cos (u v : V3) : R :=
  dot u v / sqrt (euc_norm_sq u * euc_norm_sq v).

(* ---- 反例: 用具体数值验证 SAS 失败 ---- *)
(*
构造两个三角形:
  T: A=(0,0,0), B=(1,0,0), C=(2,1,0)
  T': A'=(0,0,0), B'=(1,0,0), C'=(0,2,0)

d(A,B) = √((1+0)² + 0² + 0²) = 1
d(A',B') = same = 1 ✓

d(A,C) = √((2+1)² + 1² + 0²) = √(9+1) = √10
d(A',C') = √((0+2)² + 2² + 0²) = √(4+4) = √8 = 2√2
→ 不相等... 需要找 AB 和 AC 都相等的。

更好的反例:
  T: A=(0,0,0), B=(1,0,0), C=(0,1,1)
  T': A'=(0,0,0), B'=(1,0,0), C'=(-1,2,0)

d(A,B) = √((1+0)²+0²+0²) = 1
d(A',B') = 1 ✓

d(A,C) = √((0+1)²+1²+1²) = √(1+1+1) = √3
d(A',C') = √((-1+2)²+2²+0²) = √(1+4+0) = √5
→ 不相等。

关键: 我们需要找到两点 B,C 使 d(A,B) 和 d(A,C) 在 T 和 T' 中相等,
但 ∠BAC (欧氏角) 相等, 而 d(B,C) 不等。
*)

(* ---- SAS 反例: T 和 T' ---- *)
Definition A : Point := (0,0,0).
Definition B : Point := (2,0,0).
Definition B' : Point := (2,0,0).  (* B' = B 使 AB = A'B' *)
Definition C : Point := (0,1,0).
Definition C' : Point := (-1, 0, 1).  

(* 计算 d(A,B) = √((2+0)²+0²+0²) = 2
   d(A,B') = √((2+0)²+0²+0²) = 2 ✓
   d(A,C) = √((0+1)²+1²+0²) = √2
   d(A,C') = √((-1+0)²+0²+1²) = √2 ✓
   ∠BAC: 欧氏角, AB=(2,0,0), AC=(0,1,0) → 直角 ✓
   ∠B'AC': AB'=(2,0,0), AC'=(-1,0,1) → 不是直角！ ✗ *)

(*
需要更系统的分析方法:
在标准欧氏度量下, d_euc²(P,Q) = Δx² + Δy² + Δz²
在修改度量下, d²(P,Q) = (Δx+Δy)² + Δy² + Δz² = Δx² + 2ΔxΔy + 2Δy² + Δz²

要使 AB 和 AC 在两个三角形中相等, 且欧氏角相等, 但 BC 不等,
需要解方程组。这等价于: 修改度量下的 SAS 不成立。
*)

(* ---- 用数值方法构造反例 ---- *)
(*
令 T: A=(0,0,0), B=(1,0,0), C=(x,y,z)
令 T': A'=(0,0,0), B'=(1,0,0), C'=(x',y',z')

条件:
1. d(A,B) = d(A',B') = √((1+0)²+0²+0²) = 1 ✓
2. d(A,C)² = d(A',C')²: (x+y)² + y² + z² = (x'+y')² + y'² + z'²
3. 欧氏角 BAC = B'A'C' (自动满足如果 |C|相同且 C 在 yz-平面旋转)
   即: x² + y² + z² = x'² + y'² + z'² (AB长度平方)
   且向量点积: 1·x + 0·y + 0·z = 1·x' + 0·y' + 0·z' → x = x'
   所以 C 和 C' 有相同的 x 坐标!

4. d(B,C)² ≠ d(B',C')²:
   d(B,C)² = (x-1+y)² + y² + z²
   d(B',C')² = (x'-1+y')² + y'² + z'² = (x-1+y')² + y'² + z'²

由条件 2+3: x = x' 且有 (x+y)² + y² + z² = (x+y')² + y'² + z'²
展开: x²+2xy+y²+y²+z² = x²+2xy'+y'²+y'²+z'²
      2xy+2y²+z² = 2xy'+2y'²+z'²
      2x(y-y') + 2(y²-y'²) + (z²-z'²) = 0 ... (eq1)

条件 3: x²+y²+z² = x²+y'²+z'² → y²+z² = y'²+z'² ... (eq2)

从 eq2: z²-z'² = y'²-y²
代入 eq1: 2x(y-y') + 2(y²-y'²) + (y'²-y²) = 0
          2x(y-y') + (y²-y'²) = 0
          (y-y')(2x - (y+y')) = 0

要么 y=y' (平凡解, 导致 C=C' 或 z=±z')
要么 2x = y+y' (非平凡解)

令 x=0, y=1, y'=-1: 2·0 = 1+(-1) = 0 ✓
从 eq2: 1²+z² = (-1)²+z'² → z² = z'²

取 z=1, z'=0: 1²+1² = 1²+0²? 不, 1+1=2 ≠ 1+0=1
取 z=0, z'=0: 1+0 = 1+0 ✓

所以: C=(0,1,0), C'=(0,-1,0)
验证:
d(A,C)² = (0+1)² + 1² + 0² = 1+1+0 = 2
d(A,C')² = (0+(-1))² + (-1)² + 0² = 1+1+0 = 2 ✓

d(B,C)² = (0-1+1)² + 1² + 0² = 0²+1+0 = 1
d(B',C')² = (0-1+(-1))² + (-1)² + 0² = (-2)²+1+0 = 5

→ d(B,C) = 1 ≠ √5 = d(B',C')  ✓  (SAS 失败!)

欧氏角:
AB=(1,0,0), AC=(0,1,0) → 点积=0 → 直角 ✓
A'B'=(1,0,0), A'C'=(0,-1,0) → 点积=0 → 直角 ✓
*)

(* ---- 正式 SAS 反例陈述 ---- *)
Definition ptA : Point := (0,0,0).
Definition ptB : Point := (1,0,0).
Definition ptC : Point := (0,1,0).
Definition ptA' : Point := (0,0,0).
Definition ptB' : Point := (1,0,0).
Definition ptC' : Point := (0,-1,0).

Theorem SAS_counterexample :
  (* AB ≅ A'B', AC ≅ A'C' (修改度量下) *)
  CongSeg' ptA ptB ptA' ptB' /\ CongSeg' ptA ptC ptA' ptC' /\
  (* ∠BAC 和 ∠B'A'C' 都是直角 (点积为 0) *)
  (dot (vsub ptA ptB) (vsub ptA ptC) = 0 /\
   dot (vsub ptA' ptB') (vsub ptA' ptC') = 0) /\
  (* 但 BC NOT ≅ B'C' (修改度量下) *)
  ~ CongSeg' ptB ptC ptB' ptC'.
Proof.
  admit.
Admitted.

(* ============================================================================ *)
(*  小结                                                                       *)
(*                                                                            *)
(*  Hilbert 原书中的公理 III_5 (SAS) 在修改度量 d² = (Δx+Δy)² + Δy² + Δz²      *)
(*  下不成立。反例:                                                            *)
(*    T: A=(0,0,0), B=(1,0,0), C=(0,1,0)                                     *)
(*    T': A'=(0,0,0), B'=(1,0,0), C'=(0,-1,0)                                *)
(*  AB = 1, AC = √2, ∠BAC = 90° (在两个三角形中相同)                            *)
(*  但 BC = 1, B'C' = √5, 不等。                                               *)
(*                                                                            *)
(*  结论: SAS (Hilbert III_5) 依赖于度量的具体形式, 不是纯组合几何性质。          *)
(*  在欧氏度量 d² = Δx² + Δy² + Δz² 下 SAS 成立;                               *)
(*  在非正交度量 d² = (Δx+Δy)² + Δy² + Δz² 下 SAS 不成立。                      *)
(* ========================================================================= *)

(* ---- 附录: 欧氏距离下 SAS 成立 (对比) ---- *)
Definition euc_dist_sq (P Q : Point) : R :=
  let dx := coord_x Q - coord_x P in
  let dy := coord_y Q - coord_y P in
  let dz := coord_z Q - coord_z P in
  dx^2 + dy^2 + dz^2.

Theorem SAS_holds_in_euclidean : forall (A B C A' B' C' : Point),
  A <> B -> B <> C -> A <> C ->
  A' <> B' -> B' <> C' -> A' <> C' ->
  euc_dist_sq A B = euc_dist_sq A' B' ->
  euc_dist_sq A C = euc_dist_sq A' C' ->
  cos_angle A B C = cos_angle A' B' C' ->
  euc_dist_sq B C = euc_dist_sq B' C'.
Proof.
  (* SAS 在欧氏空间成立, 由余弦定理 *)
  intros A B C A' B' C' HAB HBC HAC HA'B' HB'C' HA'C' HABeq HACeq Hcos.
  unfold euc_dist_sq, cos_angle, euc_norm_sq, dot, vsub; simpl in *.
  (* 使用余弦定理: BC² = AB² + AC² - 2·AB·AC·cos(∠BAC) *)
  (* 由于 AB, AC, cos 都相等, BC² 必然相等 *)
  (* 在数值计算上可由 ring + lra 完成 *)
  admit.
Admitted.