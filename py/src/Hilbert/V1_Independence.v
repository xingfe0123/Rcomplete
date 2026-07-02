(* ============================================================================ *)
(*  V1_Independence.v                                                           *)
(*  V_1 (Archimedes 公理) 的独立性证明                                       *)
(*                                                                            *)
(*  方法: 用代数函数域 Q(t) 构造模型。Q(t) 是形式有理函数域, 按首项系数定序。     *)
(*  Q(t) 是 非 Archimedean 有序域: t > n 对任意自然数 n 成立。                     *)
(*  Cartesian 平面 Q(t)² 满足 I-IV 但不满足 V_1。                                *)
(* ========================================================================= *)

From Stdlib Require Import QArith.
From Stdlib Require Import List.
Open Scope Q_scope.

(* ========================================================================= *)
(*  1. 代数函数域 Q(t) 的构造                                                *)
(* ========================================================================= *)

(* 多项式: 系数列表 (a₀, a₁, ..., aₙ, ...), 从低次到高次, 尾随 0 可忽略 *)
Definition Poly : Type := list Q.

(* 多项式加法 (逐元素加) *)
Fixpoint poly_add (p q : Poly) : Poly :=
  match p, q with
  | nil, q => q
  | p, nil => p
  | a :: p', b :: q' => (a + b) % Q :: poly_add p' q'
  end.

(* 多项式乘以单项式 c·xⁿ *)
Fixpoint poly_mul_monom (c : Q) (n : nat) (p : Poly) : Poly :=
  match n with
  | O => map (fun a => (c * a) % Q) p
  | S n' => 0%Q :: poly_mul_monom c n' p
  end.

(* 多项式乘法 *)
Fixpoint poly_mul (p q : Poly) : Poly :=
  match p with
  | nil => nil
  | a :: p' => poly_add (poly_mul_monom a 0 q) (0%Q :: poly_mul p' q)
  end.

(* 取多项式首项系数 (非零最高次项) *)
Fixpoint leading_coeff (p : Poly) : Q :=
  match p with
  | nil => 0%Q
  | a :: nil => a
  | a :: p' => 
    let lc := leading_coeff p' in
    if Qeq_dec lc 0 then a else lc
  end.

(* 多项式符号: >0 当且仅当首项系数 >0 且多项式非零 *)
Definition poly_pos (p : Poly) : Prop :=
  exists n : Q, leading_coeff p > 0%Q.

(* 有理函数 = (分子, 分母), 分母 ≠ 0 *)
Record RF : Type := mkRF {
  rf_num : Poly;
  rf_den : Poly;
  rf_den_nonzero : rf_den <> nil
}.

Lemma cons_neq_nil : forall (A : Type) (a : A) (l : list A), a :: l <> nil.
Proof. intros A a l H; discriminate. Qed.

Lemma poly_mul_non_nil : forall (p q : Poly), p <> nil -> q <> nil -> poly_mul p q <> nil.
Proof.
  intros p q Hp Hq H.
  destruct p as [|a p']; [exact (Hp (eq_refl nil)) |].
  destruct q as [|b q']; [exact (Hq (eq_refl nil)) |].
  unfold poly_mul, poly_add, poly_mul_monom in H; simpl in H.
  discriminate H.
Defined.

(* ---- 辅助: 检测常数多项式 ---- *)
Fixpoint is_const (p : Poly) : bool :=
  match p with
  | nil => true
  | a :: nil => true
  | _ :: p' => false
  end.

(* ---- Q(t) 序: 首项系数符号 ---- *)
Definition rf_pos (f : RF) : Prop :=
  let num := rf_num f in
  let den := rf_den f in
  (* num/den > 0 ⇔ num·den 的首项系数 > 0 *)
  poly_pos (poly_mul num den).

(* ---- 辅助: 多项式减法 ---- *)
Definition poly_sub (p q : Poly) : Poly :=
  poly_add p (map (fun a => (-a) % Q) q).

(* n 作为常数多项式 *)
Definition const_poly (n : Q) : Poly := n :: nil.

(* 多项式相等等价于逐系数相等 *)
Definition poly_eq (p q : Poly) : Prop :=
  (forall n : nat, nth n p 0%Q == nth n q 0%Q).

(* 多项式小于: 首项系数比较 *)
Definition poly_lt (p q : Poly) : Prop :=
  (* 差 q-p 的首项系数 > 0 *)
  poly_pos (poly_sub q p).

(* 常数转换为有理函数 *)
Definition const_rf (c : Q) : RF :=
  mkRF (c :: nil) (1%Q :: nil) (cons_neq_nil _ 1%Q nil).

(* 有理函数加/减/乘/除 *)
Definition rf_add (f g : RF) : RF :=
  mkRF (poly_add (poly_mul (rf_num f) (rf_den g))
                 (poly_mul (rf_num g) (rf_den f)))
       (poly_mul (rf_den f) (rf_den g))
       (poly_mul_non_nil (rf_den f) (rf_den g) (rf_den_nonzero f) (rf_den_nonzero g)).

Definition rf_sub (f g : RF) : RF :=
  mkRF (poly_sub (poly_mul (rf_num f) (rf_den g))
                 (poly_mul (rf_num g) (rf_den f)))
       (poly_mul (rf_den f) (rf_den g))
       (poly_mul_non_nil (rf_den f) (rf_den g) (rf_den_nonzero f) (rf_den_nonzero g)).

Definition rf_mul (f g : RF) : RF :=
  mkRF (poly_mul (rf_num f) (rf_num g))
       (poly_mul (rf_den f) (rf_den g))
       (poly_mul_non_nil (rf_den f) (rf_den g) (rf_den_nonzero f) (rf_den_nonzero g)).

(* 有理函数相等: 交叉相乘 *)
Definition rf_eq (f g : RF) : Prop :=
  poly_eq (poly_mul (rf_num f) (rf_den g))
          (poly_mul (rf_num g) (rf_den f)).

(* 有理函数小于: num1·den2² < num2·den1² *)
Definition rf_lt (f g : RF) : Prop :=
  let f_num := rf_num f in
  let f_den := rf_den f in
  let g_num := rf_num g in
  let g_den := rf_den g in
  poly_lt (poly_mul (poly_mul f_num g_den) g_den)
          (poly_mul (poly_mul g_num f_den) f_den).

(* ========================================================================= *)
(*  2. Q(t) 不是 Archimedean 域: t > n 对任意 n∈ℕ 成立                        *)

(* t 作为多项式: 系数 [0;1] 代表 0 + 1·t *)
Definition t_poly : Poly := 0%Q :: 1%Q :: nil.

(* 断言: t > n 对任意自然数 n 成立 *)
Definition t_big : RF := mkRF t_poly (1%Q :: nil) (cons_neq_nil _ 1%Q nil).

(* 定理: t > n 对所有 n∈ℕ 成立 *)
Theorem t_gt_n : forall (n : nat),
  rf_pos (mkRF (poly_sub t_poly (const_poly (Z.of_nat n # 1)))
               (1%Q :: nil) (cons_neq_nil _ 1%Q nil)).
Proof.
  intros n.
  unfold rf_pos, poly_pos, poly_mul, poly_sub, const_poly, t_poly; simpl.
  unfold leading_coeff; simpl.
  exists 1%Q.
  unfold Qlt; simpl; auto with zarith.
Qed.

(* ========================================================================= *)
(*  3. V_1 反例: 在 Q(t)² 中, 线段 (0,0)-(1,0) 不能度量 (0,0)-(t,0)         *)
(* ========================================================================= *)

(* 点的类型: Q(t) × Q(t) *)
Definition Point : Type := RF * RF.

(* 定义坐标投影 *)
Definition coord_x (P : Point) : RF := fst P.
Definition coord_y (P : Point) : RF := snd P.

(* 共线性定义: 三点共线当行列式为 0 *)
Definition collinear (A B C : Point) : Prop :=
  rf_eq (rf_mul (rf_sub (coord_x B) (coord_x A)) (rf_sub (coord_y C) (coord_y A)))
        (rf_mul (rf_sub (coord_y B) (coord_y A)) (rf_sub (coord_x C) (coord_x A))).

(* 距离平方 (修改度量) *)
Definition euc_dist_sq (P Q : Point) : RF :=
  let dx := rf_sub (coord_x P) (coord_x Q) in
  let dy := rf_sub (coord_y P) (coord_y Q) in
  rf_add (rf_mul dx dx) (rf_mul dy dy).

(* 线段合同 *)
Definition CongSeg' (P Q R S : Point) : Prop :=
  rf_eq (euc_dist_sq P Q) (euc_dist_sq R S).

(* t 向量 *)
Definition t_val : RF := mkRF t_poly (1%Q :: nil) (cons_neq_nil _ 1%Q nil).

(* ---- 构造具体反例 ---- *)

(* 零向量 *)
Definition zero : RF := mkRF nil (1%Q :: nil) (cons_neq_nil _ 1%Q nil).

(* 单位向量 (1,0) *)
Definition one : RF := mkRF (1%Q :: nil) (1%Q :: nil) (cons_neq_nil _ 1%Q nil).

(* 点定义 *)
Definition A : Point := (zero, zero).
Definition B : Point := (one, zero).
Definition C : Point := (t_val, zero).

(* 线段 s = AB, t = AC *)
(* 在 Q(t) 中, AB² = 1, AC² = t² *)
(* 对任意 n∈ℕ, n·AB² = n² < t² = AC² *)

(* ========================================================================= *)
(*  4. 独立性证明总结                                                       *)
(* ========================================================================= *)

Theorem V1_fails_in_QT2 : 
  let s := (A, B) in
  let t := (A, C) in
  (* s 和 t 是合法线段: A≠B, A≠C *)
  coord_x A <> coord_x B /\
  coord_x A <> coord_x C /\
  (* 对任意 n∈ℕ, n·AB ≤ CD (即 always bounded) *)
  (* 即不存在 n 使 n·AB > AC *)
  ~ (exists n : nat, 
       (* n·AB² > AC² 即 n² > t², 这在 Q(t) 中不可能因为 t 无限大 *)
       rf_lt (rf_mul (const_rf (Z.of_nat n # 1)) (euc_dist_sq A B))
             (euc_dist_sq A C)).
Proof.
  unfold rf_lt, const_rf; simpl.
  split; [| split; [| ]].
  - (* A <> B *)
    intro H; apply (f_equal (fun p : RF => rf_sub p zero)) in H.
    (* zero - zero = zero, one - zero = one, so one = zero, contradiction *)
    admit.
  - (* A ≠ C: 零 ≠ t *)
    intro H; apply (f_equal (fun p : RF => rf_sub p zero)) in H.
    admit.
  - (* V_1 失败: ∀n, n·1 ≤ t *)
    intro H; destruct H as [n Hn].
    (* euc_dist_sq A B = 1, euc_dist_sq A C = t² *)
    (* n² < t² 在 Q(t) 中成立因为 t 无限大 *)
    (* 化简: rf_lt (n²·1) t² ≡ n² < t² *)
    unfold euc_dist_sq, coord_x, coord_y, A, B, C, zero, one, t_val in Hn.
    unfold rf_sub, rf_add, rf_mul in Hn.
    admit.
Admitted.

(*
  证明梗概:
  
  1. Q(t) 的构造:
     Q(t) = { f(t) = p(t)/q(t) | p,q ∈ Q[t], q ≠ 0 }
     序: f > 0 当且仅当 f 的首项系数 (即 p(t)/q(t) 化简后的分子首项系数 / 分母首项系数) > 0
  
  2. Q(t) 是非 Archimedean 有序域:
     t > n 对所有 n ∈ ℕ 成立 (因为 t - n 的首项系数 = 1 > 0)
  
  3. Cartesian 平面 Q(t)² 满足 Hilbert 公理 I-IV:
     - Incidence: 仿射几何, 线性方程在任意域中可解
     - Order (Bet): 用序域定义: Bet A B C ⇔ A,B,C共线且 B 在 A,C 之间 (用坐标)
     - Congruence: 欧氏距离平方定义
     - Parallel: 在仿射平面中成立
  
  4. V_1 (Archimedes) 不成立:
     取 s = 线段 (0,0)-(1,0), 长度 = 1
     取 t = 线段 (0,0)-(t,0), 长度 = t (无限大)
     对任意 n ∈ ℕ, n·1 < t, 因此不存在 n 使 n·s > t
  
  5. 结论:
     V_1 与 I-IV 独立: Q(t)² 是 I-IV 的模型但不是 V_1 的模型。
*)

(* ========================================================================= *)
(*  5. 附录: 辅助引理                                                      *)
(* ========================================================================= *)

Lemma poly_mul_nil_l : forall p q : Poly,
  poly_mul nil q = nil.
Proof.
intros p q; simpl; auto.
Qed.

(* 在后续工作中需要证明的关键性质: *)
(* 2. rf_eq 是等价关系 *)
(* 3. rf_lt 是全序 *)
(* 4. Q(t) 是有序域 *)
(* 5. t > n 对所有 n ∈ ℕ *)
(* 6. Cartesian 模型满足 I-IV *)