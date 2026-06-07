Require Import Reals.
Require Import Classical_Prop.
Require Import Ensembles.
Require Import Reals Lra.
Require Import Ensembles Classical_Prop.
Require Import Rfunctions.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Nsatz.

Open Scope R_scope.
Section frechet.
  Parameter VR : nat -> Type.
  Parameter n : nat.
  (*Rn 是R^n 的开空间*)
  Definition Rn := (VR n).

  Parameter omega : (VR n) -> Prop.


  Parameter open : (Rn -> Prop)->Prop.
  Parameter compact : (Rn -> Prop)->Prop.
  Parameter interior : (Rn -> Prop)->(Rn -> Prop).
  Parameter continuous : (Rn->R)->Prop.
  Axiom continuity_minus:
    forall f g, continuous f-> continuous g -> continuous (fun x : Rn => f x - g x).
  Parameter supremum : (R->Prop)->R.
  Axiom supremum_ub : forall Sn x, Sn x -> x <= supremum Sn.
  Axiom supremum_lub : forall Sn M, (forall x, Sn x -> x <= M) -> supremum Sn <= M.
  Axiom supremum_ext:
    forall (X Y :R->Prop), (forall x , X x<-> Y x) ->  supremum X = supremum Y.

  Lemma supremum_sub:
    forall Sn  x, Sn x-> x >=0 ->
                supremum Sn >= 0.
  Proof.
    intros.
    assert (x <= supremum Sn).
    apply supremum_ub.
    exact H.
    lra.
  Qed.

  Parameter omega_is_open : open omega.
  Hypothesis omega_not_empty : exists x , omega x.
  Parameter K : nat -> (Rn -> Prop).

  Hypothesis K_nonempty_base : exists x, K 0 x.
  Hypothesis K_compact : forall k, compact (K k).
  Hypothesis K_cover : forall x, omega x -> exists k, K k x.
  Hypothesis K_covers_Rn : forall p : Rn, exists k : nat, K k p.
  Hypothesis K_expand : forall k,
      forall x, (K k) x ->  (interior (K (S k))) x.

  Definition C0 : Type := { f : Rn -> R | continuous f }.
  Definition func_of_C0 (c : C0) : Rn -> R := proj1_sig c.
  Coercion func_of_C0 : C0 >-> Funclass.

  Definition test (c : C0) (x : Rn) := c x.
  Definition sub (f g: Rn->R) :=
    fun x => f x - g x.


  Definition semi_norm (k : nat) (f : Rn->R) : R :=
  supremum (fun y => exists x, K k x /\ Rabs (f x) = y).

Axiom semi_non_neg:
  forall x z n , 0 <= semi_norm n (sub x z).

Axiom semi_non_triangle:
  forall x y z n0 , semi_norm n0 (sub x z) <=
                      semi_norm n0 (sub x y) + semi_norm n0 (sub y z).


  (* 假设你的库中已经有 interior_in 或 interior_subset 引理，这里用一个辅助引理： *)
Lemma interior_implies_mem {A : Rn -> Prop} (x : Rn) :
  interior A x -> A x.
Admitted.

Lemma K_nonempty_all : forall n0 , exists x , K n0 x.
Proof.
  induction n0 as [|n IH].
  - (* n0 = 0 *) exact K_nonempty_base.
  - (* n0 = S n *)
    destruct IH as [x Hx].
    exists x.
    apply interior_implies_mem.
    apply K_expand, Hx.
Qed.


  Lemma semi_norm_nonneg : forall n f ,semi_norm n f >=0.
    intros.
    destruct (K_nonempty_all n0) as [x0 HKn0].
    unfold semi_norm.
    apply Rle_ge.               (* 把 >= 转成 <= *)
    set (S := fun y : R => exists x : Rn, K n0 x /\ Rabs (f x) = y).
    assert (Hmem : S (Rabs (f x0))).
     { exists x0; split; [exact HKn0 | reflexivity]. }
     apply Rle_trans with (Rabs (f x0)).
     apply Rabs_pos.
     apply (supremum_ub S (Rabs (f x0)) Hmem).
  Qed.



  Lemma x_noneg :
    forall n0 f, f >=0 -> / 2 ^ n0 * (f / (1 + f)) >= 0.
  Proof.
    intros.
    assert (0 <= (/ 2 ^ n0 * (f / (1 + f)) )).
    apply Rmult_le_pos.
    apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra.
    unfold Rdiv.
    apply Rmult_le_pos. lra.
    assert (1 + f > 0).
    lra.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    lra.
    lra.
  Qed.


  Definition phi (n : nat) (f g : C0) : R :=
  let d := semi_norm n (sub f g) in
  (/(2 ^ n)) * (d / (1 + d)).

Definition phi_common {V} (n : nat) (f g : V)
  (sub: V -> V -> V) (p : nat -> V -> R): R :=
  let d := p n (sub f g) in
  (/(2 ^ n)) * (d / (1 + d)).

Definition dist_frechet (f g : C0) : R :=
  supremum (fun x => exists k : nat, x = phi k f g).

Definition build_frechet_metric (V : Type)
           (sub : V -> V -> V)            (* 减法 *)
           (p : nat -> V -> R)            (* 半范数族 *)
   :=
   fun x y =>
     supremum (fun r => exists n : nat, r = phi_common n x y sub p).



  Lemma phi_sym : forall n f g, phi n f g = phi n  g f.
  Proof.
    intros.
    unfold phi.
    assert (semi_norm n0 (sub f g) =  semi_norm n0 (sub  g f)).
    unfold semi_norm.
    assert (forall x , Rabs (sub f g x) = Rabs (sub  g f x)). {
        intros.
        assert ((sub f g x) = - (sub  g f x)).
        unfold sub.
        lra.
        rewrite H.
        rewrite Rabs_Ropp.
        lra.
        }.
    assert (H_equiv : forall y,
  (exists x : Rn, K n0 x /\ Rabs (sub f g x) = y) <->
  (exists x : Rn, K n0 x /\ Rabs (sub g f x) = y)).
    intros.
    split.
    intros [x [Hk Hr]].
    exists x;split.
    auto.
    rewrite <-Hr.
    symmetry.
    apply H.

    intros [x [Hk Hr]].
    exists x;split;[auto|].
    rewrite <-Hr.

    apply H.

    apply supremum_ext.
    exact H_equiv.
    rewrite H.
    auto.
  Qed.


  Lemma phi_nonneg : forall n f g, phi n f g>=0.
  Proof.
    intros.
    unfold phi.
    assert ((semi_norm n0 (sub f g)) >= 0).
    apply (semi_norm_nonneg n0 (sub f g)).
    apply x_noneg.
    lra.
  Qed.





Lemma dist_frechet_nonneg : forall f g, dist_frechet f g >= 0.
Proof.
  intros f g; unfold dist_frechet.
  apply supremum_sub with (x := phi 0 f g).
  exists 0%nat.
  reflexivity.
  apply phi_nonneg.
Qed.

Lemma dist_frechet_sym : forall f g, dist_frechet f g = dist_frechet g f .
Proof.
  intros f g; unfold dist_frechet.
  set (P := fun x => exists n, x = phi n f g).
  set (Q := fun x => exists n, x = phi n g f).
  assert (forall x, P x <-> Q x). {
    split; intros [n Hx]; exists n; rewrite Hx; apply phi_sym.
  }
  apply supremum_ext.
  auto.
Qed.

Lemma sup_zero_impl_all_zero (S : R -> Prop) :
  supremum S = 0 ->
  (forall y, S y -> 0 <= y) ->
  forall y, S y -> y = 0.
Proof.
  intros Hsup Hnonneg y Hy.
  apply Rle_antisym.
  - rewrite <- Hsup. apply supremum_ub; auto.
  - apply Hnonneg; auto.
Qed.

Lemma sup_zero_impl_all_phi_zero : forall x y,
  supremum (fun x0 : R => exists k : nat, x0 = phi k x y) = 0 ->
  forall k, phi k x y = 0.
Proof.
  intros x y Hsup k.
  set (S := fun x0 : R => exists k : nat, x0 = phi k x y).
  assert (Hnonneg : forall x0, S x0 -> 0 <= x0).
  { intros x0 [k' ->].
    assert (phi k' x y >=0).
    apply phi_nonneg.
    lra.
  }.
  assert (Hmem : S (phi k x y)).
  { exists k; reflexivity. }
  apply Rle_antisym.
  - rewrite <- Hsup; apply supremum_ub; auto.
  - apply Hnonneg; auto.
Qed.
Lemma Rabs_eq_0:
  forall u , Rabs u = 0 -> u = 0 .
  intros.
  unfold Rabs in *.
  case (Req_dec u 0).
  lra.
  intro.
  exfalso.
   destruct (Rcase_abs u) eqn:Hcase.
   lra.
   lra.
Qed.

Lemma pow2_pos (k : nat) : 0 < 2 ^ k.
Proof. apply pow_lt; lra. Qed.

Lemma semi_norm_zero_from_prod (k : nat) (x y : C0) :
  / 2 ^ k * (semi_norm k (sub x y) / (1 + semi_norm k (sub x y))) = 0 ->
  semi_norm k (sub x y) = 0.
Proof.
  intros Hprod.
  assert (Hpos : 0 < / 2 ^ k).
  { apply Rinv_0_lt_compat. apply pow_lt; lra. }
  unfold Rdiv in Hprod.
  apply Rmult_integral in Hprod.
  destruct Hprod as [Hinv | Hfrac].
  exfalso. lra.
  assert ((semi_norm k (sub x y) * / (1 + semi_norm k (sub x y))) = 0).
  auto.
  apply Rmult_integral in Hfrac.
  assert (/ (1 + semi_norm k (sub x y)) <> 0).
   apply Rinv_neq_0_compat.
   apply Rgt_not_eq.
   assert (semi_norm k (sub x y) >=0).
   apply semi_norm_nonneg.
   lra.
   lra.
Qed.


Lemma phi_zero_imp_eq_on_K : forall (k : nat) (x y : C0),
  phi k x y = 0 -> forall t : Rn, K k t -> proj1_sig x t = proj1_sig y t.
Proof.
  intros k x y Hphi t Hk.
  unfold phi in Hphi.
  (* 设 S 为局部绝对值的集合 *)
  set (S := fun d : R => exists t : Rn, K k t /\ Rabs (proj1_sig x t - proj1_sig y t) = d).
  assert (Hnonneg : forall d, S d -> 0 <= d).
  { intros d [t' [Hk' Hd]]. rewrite <- Hd; apply Rabs_pos. }
  (* 证明 Rabs (x t - y t) 属于 S *)
  assert (Hmem : S (Rabs (proj1_sig x t - proj1_sig y t))).
  { exists t; split; [exact Hk | reflexivity]. }
  (* 由 sup = 0 推出该绝对值为 0 *)
  assert (proj1_sig x t - proj1_sig y t = 0).
  apply Rabs_eq_0.
  apply semi_norm_zero_from_prod in Hphi.
  (* 因为 Rabs u = 0 → u = 0 *)
  apply (sup_zero_impl_all_zero S Hphi Hnonneg _ Hmem).
  lra.
Qed.

Lemma C0_eq_ext (x y : C0) : (forall p, proj1_sig x p = proj1_sig y p) -> x = y.
Proof.
  intros.
  destruct x as [f Hf], y as [g Hg].
  simpl in H.
  assert (Heq_fg : f = g) by (apply functional_extensionality; exact H).
  subst g.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma dist_frechet_eq0 : forall x y, dist_frechet x y = 0 -> x = y.
  Proof.
    unfold dist_frechet.
    intros x y Hsup.
    apply C0_eq_ext; intro p.
    assert (Hphi0 : forall k, phi k x y = 0).
    { apply sup_zero_impl_all_phi_zero; assumption. }
    destruct (K_covers_Rn p) as [k Hk].
    apply (phi_zero_imp_eq_on_K k x y (Hphi0 k) p Hk).
  Qed.





Lemma supremum_Rabs0 : forall k,
  supremum (fun y0 : R => exists x : Rn, K k x /\ Rabs 0 = y0) = 0.
Proof.
  intros k.
  apply Rle_antisym.
  - (* ≤ 0 *) apply supremum_lub. intros y0 [x [HK Hy]].
    rewrite <- Hy. rewrite Rabs_R0. apply Rle_refl.
  - (* 0 ≤ *) destruct (K_nonempty_all k) as [x HK].
    apply supremum_ub. exists x; split; [exact HK | apply Rabs_R0].
Qed.
Lemma phi_self: forall k y, phi k y y = 0.
  Proof.
    intros.
    unfold phi.
    assert (sub y y = fun _ => 0).
    unfold sub.
    apply functional_extensionality; intro x.
    lra.
    rewrite H.
    unfold semi_norm.
    assert (supremum (fun y0 : R => exists x : Rn, K k x /\ Rabs 0 = y0) = 0).
    apply supremum_Rabs0.
    rewrite H0.
    lra.
  Qed.


Lemma dist_frechet_eq1 : forall x y,  x = y -> dist_frechet x y = 0.
  Proof.
    intros.
    subst.
    unfold dist_frechet.
    set (S := fun x : R => exists k : nat, x = phi k y y).
    apply Rle_antisym.
    - apply supremum_lub with (Sn := S) (M := 0).
      intros x [k Hx].   (* S x 即存在 k 使得 x = phi k y y *)
      rewrite Hx.        (* x 就是 phi k y y *)
      rewrite phi_self.  (* phi k y y = 0 *)
      apply Rle_refl.
    - apply supremum_ub with (x := 0).
      unfold S.
       exists 0%nat.
       rewrite phi_self.
       reflexivity.
  Qed.

Lemma dist_frechet_eq : forall x y, dist_frechet x y = 0 <-> x = y.
  Proof.
    split.
    apply dist_frechet_eq0.
    apply dist_frechet_eq1.
  Qed.

  Lemma Rle_minus_l a b : a <= b <-> 0 <= b - a.
    Proof.
      split.
      lra.
      lra.
    Qed.

Lemma fraction_ineq a b c :
  0 <= a -> 0 <= b -> 0 <= c ->
  a <= b + c ->
  a / (1 + a) <= b / (1 + b) + c / (1 + c).
Proof.
  intros Ha Hb Hc Hle.
   apply (Rmult_le_reg_r ((1 + a) * (1 + b) * (1 + c))).
  { repeat apply Rmult_lt_0_compat; lra. }
  field_simplify.
  apply Rle_minus_l.
  field_simplify.
  apply Rle_minus_l in Hle.
  assert (a * b * c - a + 2 * b * c + b + c =
            (a * b * c)+ 2 * b * c + (b+c -a)).
  nra.
  rewrite H.
  apply Rle_trans with (0+0+0); [lra | ].
  repeat apply Rplus_le_compat.
  apply Rmult_le_pos; auto.
  apply Rmult_le_pos; auto.
  apply Rmult_le_pos; auto.
  apply Rmult_le_pos; auto.
  lra.
  lra.
  lra.
  lra.
  Qed.

Lemma phi_triangle : forall x y z n, phi n x z <=
                                       phi n x y + phi n y z.
    intros.
    unfold phi.
    assert ((semi_norm n0 (sub x z) / (1 + semi_norm n0 (sub x z))) <=
             (semi_norm n0 (sub x y) / (1 + semi_norm n0 (sub x y)))
             + (semi_norm n0 (sub y z) / (1 + semi_norm n0 (sub y z)))).

    apply fraction_ineq.
    apply semi_non_neg.
    apply semi_non_neg.
    apply semi_non_neg.
    apply semi_non_triangle.
    apply Rmult_le_compat_l with (r := / 2 ^ n0) in H.
    lra.
    assert ( 0 <   2 ^ n0).
    apply pow_lt. lra.
    assert ( 0 < /  2 ^ n0).
    apply Rinv_0_lt_compat.
    lra.
    lra.
Qed.


Lemma dist_frechet_triangle :
  forall x y z , dist_frechet x z <=
                   dist_frechet x y + dist_frechet y z.
  Proof.
    intros.
    unfold dist_frechet.
    apply supremum_lub.
    intros x0 [k ->].
    apply Rle_trans with (phi k x y + phi k y z).
  - apply phi_triangle. (* 引理 *)
  - apply Rplus_le_compat.
    * apply supremum_ub. exists k; reflexivity.
    * apply supremum_ub. exists k; reflexivity.
  Qed.





Class Metric(V:Type) :={
    dist : V -> V -> R;
    dist_nonneg : forall x y, dist x y >= 0;
    dist_sym : forall x y, dist x y = dist y x;
    dist_triangle : forall x y z , dist x z <=  dist x y + dist y z;
    dist_eq : forall x y, dist x y = 0 <-> x = y
}.
Instance C0_metric : Metric C0 :=
  {| dist := fun x y => supremum (fun d => exists k, d = phi k x y);
     dist_nonneg := dist_frechet_nonneg;
     dist_sym := dist_frechet_sym;
     dist_triangle := dist_frechet_triangle;
     dist_eq := dist_frechet_eq |}.

Definition cauchy_seq {V} (seq : nat -> V) `{Metric V}: Prop :=
  forall eps : R, eps > 0 ->
  exists N : nat, forall m n : nat,
    (m >= N)%nat -> (n >= N)%nat ->
    dist (seq m) (seq n) < eps.

Definition limit_of {V} `{Metric V} (seq : nat -> V) (lim : V) : Prop :=
  forall eps : R, eps > 0 ->
  exists N : nat, forall n : nat,
    (n >= N)%nat ->
    dist (seq n) lim < eps.

Class CompleteMetric (V : Type) `{Metric V} :=
  complete : forall seq : nat -> V,
      cauchy_seq seq -> exists lim, limit_of seq lim.

Lemma C0_complete_proof:
  forall seq : nat -> C0,cauchy_seq seq -> exists lim, limit_of seq lim.
  Admitted.



Parameter smooth : (Rn -> R) -> Prop.
(* C∞：所有光滑函数 *)
Definition C_inf : Type := { f : Rn -> R | smooth f }.
Definition Dk (k : nat) : Type :=
  { f : Rn -> R | smooth f /\ forall x : Rn, ~ K k x -> f x = 0 }.

Definition multi_index : Type := list nat.
Fixpoint mi_length (a : multi_index) : nat :=
  match a with
  | nil => 0
  | n :: a' => n + mi_length a'
  end.

Parameter D : multi_index -> (Rn -> R) -> (Rn -> R).

(* 导数在光滑函数上的作用：只需提取底层函数 *)
Definition D_on_C (a : multi_index) (f : C_inf) : Rn -> R :=
  D a (proj1_sig f).

Definition semi_norm_d (n : nat) (f : C_inf) : R :=
  supremum
    (fun r => exists (x : Rn) (a : multi_index),
      K n x /\ (mi_length a <= n)%nat /\ r = Rabs (D_on_C a f x)).

Definition C_inf_plus (f g : C_inf) : C_inf.
  (* 若已定义，直接用；否则假设存在并满足逐点性质 *)
Admitted.

Definition C_inf_scalar_mul (c : R) (f : C_inf) : C_inf.
Admitted.
Definition C_inf_sub (f g : C_inf) :=
  C_inf_plus f (C_inf_scalar_mul (-1) g).

(* 记法 *)
Parameter D_on_C_linear : forall (a : multi_index) (c : R) (f g : C_inf) (x : Rn),
  D_on_C a (C_inf_scalar_mul c f) x = c * D_on_C a f x /\
  D_on_C a (C_inf_plus f g) x = D_on_C a f x + D_on_C a g x.
Record Seminorm (V : Type) : Type := {
  seminorm_fn : V -> R;
  seminorm_scalar: R -> V -> V;
  seminorm_add: V -> V -> V;

  seminorm_nonneg : forall x, 0 <= seminorm_fn x;
  seminorm_scal : forall (c : R) (x : V),
    seminorm_fn (seminorm_scalar c  x) = Rabs c * seminorm_fn x;
  seminorm_triangle : forall x y : V,
    seminorm_fn (seminorm_add x  y) <= seminorm_fn x + seminorm_fn y
}.


Lemma semi_norm_d_nonneg : forall (n : nat) (f : C_inf),
  0 <= semi_norm_d n f.
Proof.
  intros n f.
  unfold semi_norm_d.
  destruct (K_nonempty_all n) as [x Hx].
  set (e := Rabs (D_on_C nil f x)).
  assert (Hmem : (fun r => exists (x0 : Rn) (a : multi_index),
                K n x0 /\ (mi_length a <= n)%nat /\ r = Rabs (D_on_C a f x0)) e).
  { exists x, nil; split; [exact Hx | split; [apply le_0_n | reflexivity]]. }
  apply Rle_trans with e.
  - apply Rabs_pos.
  - apply supremum_ub; exact Hmem.
Qed.

Lemma semi_norm_d_scal : forall (n : nat) (c : R) (f : C_inf),
  semi_norm_d n (C_inf_scalar_mul c f) = Rabs c * semi_norm_d n f.
Proof.
Admitted.

Lemma semi_norm_d_triangle : forall (n : nat) (f g : C_inf),
  semi_norm_d n (C_inf_plus f g) <= semi_norm_d n f + semi_norm_d n g.
Proof.
  intros n f g.
  unfold semi_norm_d.
  set (Ssum := fun r => exists x a, K n x /\ (mi_length a <= n)%nat /\ r = Rabs (D_on_C a (C_inf_plus f g) x)).
  set (Sf := fun r => exists x a, K n x /\ (mi_length a <= n)%nat /\ r = Rabs (D_on_C a f x)).
  set (Sg := fun r => exists x a, K n x /\ (mi_length a <= n)%nat /\ r = Rabs (D_on_C a g x)).
  apply supremum_lub.
  intros r [x [a [Hk [Hlen ->]]]].
  destruct (D_on_C_linear a 1 f g x) as [_ Hlin_add].
  rewrite Hlin_add.
  apply Rle_trans with (Rabs (D_on_C a f x) + Rabs (D_on_C a g x)).
  - apply Rabs_triang.
  - apply Rplus_le_compat.
    + apply supremum_ub; exists x, a; auto.
    + apply supremum_ub; exists x, a; auto.
Qed.

Lemma seminorm_d_n (n : nat) : Seminorm C_inf.
Proof.
  refine ({| seminorm_fn := fun f => semi_norm_d n f;
             seminorm_nonneg := semi_norm_d_nonneg n;
             seminorm_scal := semi_norm_d_scal n;
             seminorm_triangle := semi_norm_d_triangle n |}).
Defined.
Check phi_common.
Instance C_inf_metric : Metric C_inf.
Admitted.


Lemma frechet_cauchy_implies_phi_cauchy (seq : nat -> C_inf) :
  cauchy_seq seq ->
  forall (n : nat) (eps : R), eps > 0 ->
  exists N : nat, forall m l : nat, (m >= N)%nat -> (l >= N)%nat ->
    phi_common n (seq m) (seq l) C_inf_sub semi_norm_d < eps.
Proof.
Admitted.


Require Import ClassicalEpsilon.
Section Completeness.
  Variable seq : nat -> C_inf.
  Hypothesis Hc : cauchy_seq seq.
  Definition cover_index (x : Rn) : nat :=
  let H := K_covers_Rn x in
  proj1_sig (constructive_indefinite_description _ H).
  Lemma cover_index_correct : forall x : Rn, K (cover_index x) x.
Proof.
  intro x.
  unfold cover_index.
  destruct (constructive_indefinite_description _ (K_covers_Rn x)) as [k Hk].
  exact Hk.
Qed.
Lemma pointwise_cauchy
  (n : nat) (a : multi_index) (Ha : (mi_length a <= n)%nat) (x : Rn) (Hx : K n x) :
  forall eps : R, eps > 0 ->
    exists N : nat, forall m l : nat, (m >= N)%nat -> (l >= N)%nat ->
      Rabs (D_on_C a (seq m) x - D_on_C a (seq l) x) < eps.
  Admitted.

Axiom R_cauchy_complete :
  forall (a : nat -> R),
    (forall eps:R, eps > 0 ->
      exists N, forall m l, (m >= N)%nat -> (l >= N)%nat -> Rabs (a m - a l) < eps) ->
    { l : R |
      forall eps:R, eps > 0 -> exists N, forall m, (m >= N)%nat -> Rabs (a m - l) < eps }.

Lemma le_0_n : forall n:nat, (0 <= n)%nat.
Proof. apply Nat.le_0_l. Qed.

Definition lim_fun (x : Rn) : R :=
    let k := cover_index x in
    proj1_sig (R_cauchy_complete
      (fun m => D_on_C nil (seq m) x)
      (pointwise_cauchy k nil (le_0_n k) x (cover_index_correct x))).


Lemma lim_smooth : smooth lim_fun. Admitted.
Definition lim : C_inf := exist _ lim_fun lim_smooth.
Lemma limit_of_seq : limit_of seq lim. Admitted.

End Completeness.

Theorem C_inf_complete :
  forall seq : nat -> C_inf, cauchy_seq seq -> exists lim, limit_of seq lim.
Proof.
  intros seq Hc.
  exists (lim seq Hc).
  apply (limit_of_seq seq Hc).
Qed.


Section frechet.

Section Top.
  Parameter X : Type.
  Parameter norm : X ->R.
  Parameter dist : X->X ->R.

  Definition support (f : X -> R) := { x : X | f x <> 0 }.

  Definition is_compact {X}(S : X -> Prop) : Prop :=
  (* 海涅-博雷尔：有界闭集，这里简化为有界且闭 *)
  (exists M, forall x, S x -> norm x <= M) /\
  (forall x, ~S x -> exists eps, forall y, dist x y < eps -> ~S y).


End Top.
Section distribution.
  Parameter TestFunction : Type.
  Parameter TF_add : TestFunction->TestFunction->TestFunction.
  Parameter TF_scal : R->TestFunction->TestFunction.

  Class VectorSpace (T :Type) := {
      add : T -> T -> T;
      scal : R->T->T;
      zero : T;
      add_assoc : forall x y z, add (add x y) z = add x (add y z);
      add_comm : forall x y, add x y = add y x;
      add_zero : forall x, add x zero = x;
      add_inv : forall x, exists y, add x y = zero;
      scal_dist_l : forall a x y, scal a (add x y) = add (scal a x) (scal a y);
    }.
  Definition convex{X:Type} (S :  X->Prop) `{VectorSpace X} :=
  forall x y : X,
    S x -> S y -> forall t : R, 0 <= t <= 1
                                -> S (add (scal (1 - t) x) (scal t y)).


  Class Distribution : Type := {
    dist_action : TestFunction -> R;        (* 泛函作用：⟨T, φ⟩ *)
    dist_linear : forall a b (f g : TestFunction),
      dist_action (TF_add (TF_scal a f) (TF_scal b g)) = a * dist_action f + b * dist_action g
  }.


End distribution.




Section Space.

End Space.

Section Des.

End Des.
