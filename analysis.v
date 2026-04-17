Require Import Reals.
Require Import List.
Import ListNotations.
Require Import Classical.
Require Import Reals.
Open Scope R_scope.
About le_refl.
About TotalOrder.le_refl.


Class TotalOrder(carrier : Type) : Type := {
  le : carrier -> carrier -> Prop;
  lt (x y : carrier) : Prop := ~ le y x;
  le_refl  : forall x, le x x;
  le_antis : forall x y, le x y -> le y x -> x = y;
  le_trans : forall x y z, le x y -> le y z -> le x z;
  le_total : forall x y, le x y \/ lt y x
}.
Check le.

Definition is_upper_bound {A : Type} `{TotalOrder A}
  (S : A -> Prop) (u : A) : Prop :=
  forall x, S x -> le x u.
Definition has_upper_bound {A : Type} `{TotalOrder A}
  (E : A -> Prop) : Prop :=
  exists u, is_upper_bound E u.

Definition is_supremum {A : Type} `{TotalOrder A}
  (S : A -> Prop) (m : A) : Prop :=
  is_upper_bound S m /\
    forall u, is_upper_bound S u -> le m u.

Definition is_lower_bound {A : Type} `{TotalOrder A} (S : A -> Prop) (l : A) : Prop :=
  forall x, S x -> le l x.

(* 下确界：m 是 S 的最大下界 *)
Definition is_infimum {A : Type} `{TotalOrder A} (S : A -> Prop) (m : A) : Prop :=
  is_lower_bound S m /\ forall l, is_lower_bound S l -> le l m.

Definition supremum_property (A : Type) `{TotalOrder A} : Prop :=
  forall E : A -> Prop,
    (exists x, E x) -> has_upper_bound E -> exists m, is_supremum E m.


Class Field (F : Type) : Type := {
  (* 加法群结构 *)
  zero : F;
  add : F -> F -> F;
  neg : F -> F;
  add_assoc : forall x y z, add x (add y z) = add (add x y) z;
  add_comm  : forall x y, add x y = add y x;
  add_0_l   : forall x, add zero x = x;
  add_neg_l : forall x, add (neg x) x = zero;

  (* 乘法群结构（非零元） *)
  one : F;
  mul : F -> F -> F;
  inv : F -> F;  (* 对非零元定义，可用 option 或加条件 *)
  mul_assoc : forall x y z, mul x (mul y z) = mul (mul x y) z;
  mul_comm  : forall x y, mul x y = mul y x;
  mul_1_l   : forall x, mul one x = x;
  mul_inv_l : forall x, x <> zero -> mul (inv x) x = one;

  (* 分配律 *)
  distrib_l : forall x y z, mul x (add y z) = add (mul x y) (mul x z)
}.

(* 有序域：继承域与全序，并满足相容性公理 *)
Class OrderedField (F : Type) `{Field F} `{TotalOrder F} : Prop := {
  (* 加法保序 *)
  add_le_compat : forall x y z, le x y -> le (add x z) (add y z);
  (* 乘法对正数保序 *)
  mul_pos_le_compat : forall x y, le zero x -> le zero y -> le zero (mul x y);
}.

Definition is_positive {F : Type} `{Field F} `{TotalOrder F} (x : F) : Prop :=
  lt zero x.

Definition is_negative {F : Type} `{Field F} `{TotalOrder F} (x : F) : Prop :=
  lt x zero.



#[export] Instance R_Field : Field R.
Proof. (* 用 Rplus, Rmult 等填充 *) Admitted.

(* 实数全序实例 *)
Lemma Rle_total : forall x y : R, Rle x y \/ ~ Rle x y.
Proof.
  intros x y.
  destruct (Rle_or_lt x y) as [H|Hlt].
  left. exact H.
  right.
  apply Rlt_not_le in Hlt.
  exact Hlt.
Qed.


#[export] Instance R_TotalOrder : TotalOrder R :=
  Build_TotalOrder R Rle Rle_refl Rle_antisym Rle_trans Rle_total.

Lemma R_supremum_property : supremum_property R.
Proof.
  intros E Hne Hbound.
  destruct Hbound as [u Hu].
   destruct (completeness E) as [m Hlub].
  - exists u; intros x Hx; apply Hu; assumption.
  - exact Hne.
  - exists m. unfold is_supremum, is_upper_bound in *.
    destruct Hlub as [Hub Hleast].
    split.
    + intros x Hx. apply Hub. assumption.
    + intros u' Hu'. apply Hleast. intros x Hx. apply Hu'. assumption.
Qed.
Definition C : Type := R * R.
#[export] Instance C_Field : Field C.
Proof. Admitted.

Definition countable {A : Type} (S : A -> Prop) : Prop :=
  exists f : nat -> A, forall x, S x -> exists n, f n = x.
Axiom countable_choice : forall (A : Type) (P : nat -> A -> Prop),
  (forall i, exists f : nat -> A, forall x, P i x -> exists n, f n = x) ->
  exists F : nat -> nat -> A, forall i x, P i x -> exists n, F i n = x.

Fixpoint triangle n :=
  (match n%nat with
    0 => 0
  | S n' => (n%nat + triangle n'%nat)%nat
  end)%nat.



Definition pair (a b : nat) : nat :=
  triangle (a + b) + a.

(* 逆函数 inv_pair : nat -> nat * nat *)
Definition inv_pair (p : nat) : nat * nat.
  (* 寻找满足 triangle k <= p < triangle (S k) 的 k *)
  (* 实际代码略，我们假设其存在并满足 inv_pair (pair a b) = (a,b) *)
Admitted.

Axiom inv_pair_correct : forall a b, inv_pair (pair a b) = (a, b).

Theorem countable_union {A : Type} (A_fam : nat -> A -> Prop) :
  (forall i, countable (A_fam i)) ->
  countable (fun x => exists i, A_fam i x).
Proof.
  intros H.
  (* 通过选择公理获取一族枚举函数 F : nat -> nat -> A *)
  apply countable_choice in H. destruct H as [F HF].
  (* 构造并集的枚举 g *)
  exists (fun k : nat =>
    let '(i, j) := inv_pair k in
    F i j).
  intros x [i Hx].
  (* 由 F 的性质得到 j 使 F i j = x *)
  destruct (HF i x Hx) as [j Hj].
  exists (pair i j).
  rewrite inv_pair_correct.
  exact Hj.
Qed.




Definition open_interval (a b : R) : R -> Prop :=
  fun x => a < x < b.

Definition close_interval (a b : R) : R -> Prop :=
  fun x => a <= x <= b.


Class MetricSpace (X : Type) : Type := {
  dist : X -> X -> R;
  dist_nonneg : forall x y, 0 <= dist x y;
  dist_eq_0   : forall x y, dist x y = 0 <-> x = y;
  dist_sym    : forall x y, dist x y = dist y x;
  dist_triangle : forall x y z, dist x z <= dist x y + dist y z
}.


Definition ball {X : Type} `{MetricSpace X} (c : X) (r : R) : X -> Prop :=
  fun p => dist p c < r.

Definition interior_point {X : Type} `{MetricSpace X} (E : X -> Prop) (p : X) : Prop :=
  exists eps, eps > 0 /\ forall q, dist q p < eps -> E q.

Definition open {X : Type} `{MetricSpace X} (D : X -> Prop) : Prop :=
  forall p, D p -> interior_point D p.
Definition is_open {X : Type} `{MetricSpace X} (U : X -> Prop) : Prop :=
  forall p, U p -> exists r : R, r > 0 /\ forall x, ball p r x -> U x.

Definition continuous_on {X Y : Type} `{MetricSpace X} `{MetricSpace Y}
  (f : X -> Y) (dom : X -> Prop) : Prop :=
  forall x, dom x -> forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall y, dom y -> dist x y < delta -> dist (f x) (f y) < eps.

Definition complement {X : Type} (E : X -> Prop) : X -> Prop :=
  fun x => ~ E x.

Definition neighbourhood {X : Type} `{MetricSpace X} (p : X) (N : X -> Prop) : Prop :=
  exists r : R, r > 0 /\ forall x, ball p r x -> N x.


Definition limit_point {X : Type} `{MetricSpace X} (E : X -> Prop) (p : X) : Prop :=
  forall eps, eps > 0 -> exists q, E q /\ q <> p /\ dist q p < eps.

Definition is_close {X : Type} `{MetricSpace X} (E : X -> Prop) : Prop :=
  forall p , limit_point E p -> E p.

Definition closed {X : Type} `{MetricSpace X} (E : X -> Prop) : Prop :=
  is_open (complement E).   (* E 是闭集当且仅当它的补集是开集 *)



Theorem closed_iff_is_close {X} `{MetricSpace X} (E : X -> Prop) :
  closed E <-> is_close E.
Proof.
  unfold closed.
  unfold is_close.
  unfold is_open.
  unfold complement.
  unfold limit_point.
  split.
  - (* closed -> is_close *)
    intros.
    apply NNPP.
    intro HnotE.
    destruct (H0 p HnotE) as [r [r_pos Hball]].
    destruct (H1 r r_pos) as [q [Eq [Hneq Hdist]]].
    apply Hball in Hdist.
    contradiction.
  - intros His_close p HnotE.
    apply NNPP; intro Hno_ball.
    unfold ball in *.

    assert (forall r, r > 0 -> exists x, ball p r x /\ E x) as HballE.
    { intros r r_pos.
      apply NNPP; intro Hnone.
      assert (forall x, ball p r x -> ~ E x) as Hall.
      { intros x Hx HEx. apply Hnone; exists x; auto. }
      apply Hno_ball; exists r; split; [exact r_pos | exact Hall].
    }
    (* 证明 p 是 E 的极限点 *)
    assert (Hlim : forall eps, eps > 0 -> exists q, E q /\ q <> p /\ dist q p < eps).
    { intros eps eps_pos.
      destruct (HballE eps eps_pos) as [x [Hbx HEx]].
      destruct (classic (x = p)) as [->|Hneq].
      - contradiction.
      - exists x; repeat split; auto. }
    apply His_close in Hlim; contradiction.
Qed.


Definition isolated_point {X : Type} `{MetricSpace X} (E : X -> Prop) (p : X) : Prop :=
  E p /\ exists eps, eps > 0 /\ forall q, E q -> dist q p < eps -> q = p.






Definition perfect {X : Type} `{MetricSpace X} (E : X -> Prop) : Prop :=
  closed E /\ forall p, E p -> limit_point E p.

Definition bounded {X : Type} `{MetricSpace X} (E : X -> Prop) : Prop :=
  exists c : X, exists M : R,
    M > 0 /\ forall x, E x -> dist x c <= M.
Require Import Lra.


(* 2.19 定理 邻域是开集*)
Theorem ball_is_open {X : Type} `{MetricSpace X} :
  forall (c : X) (r : R), r > 0 -> is_open (ball c r).
Proof.
  intros c r Hr p Hp.
  set (h := r - dist p c).
  exists h.
  split.
  - apply Rgt_minus.
    exact Hp.
  - intros q Hq.
    unfold ball in *.
    assert ( H1 : dist q c <= dist q p + dist p c).
    apply dist_triangle.
    unfold h in *.
    assert ( H2 : dist q p + dist p c < r).
    replace r with ((r - dist p c) + dist p c).
    apply Rplus_lt_compat_r.
    exact Hq.
    lra.
    lra.
Qed.

(* p 是E的极限点，那么p 的任意邻域 有 E的无限多个点 *)

Fixpoint list_min (l : list R) : R :=
  match l with
  | nil => 0
  | x :: nil => x
  | x :: xs => Rmin x (list_min xs)
  end.

Lemma list_min_pos : forall l, l <> [] ->
                               (forall x, In x l -> x > 0) -> list_min l > 0.
Proof.
  induction l.
  intros  Hnon Hpos.
  contradiction.

  intros Hnon Hpos.
  assert (Ha : a > 0 ).
  apply Hpos.
  simpl.
  auto.
  destruct l as [|b l'].
  simpl. auto.
  simpl. apply Rmin_pos.
  auto.
  apply IHl.
  discriminate.
  intros.
  apply Hpos.
  simpl.
  right.
  simpl in H.
  auto.
Qed.


Definition infinite_set (S : R -> Prop) :=
  ~ (exists l : list R, forall x, S x <-> In x l).

Definition infinite_intersection (N E : R -> Prop) p :=
  infinite_set (fun x => N x /\ E x/\ x <> p ).

Lemma neighbourhood_contains_other_point `{MetricSpace R}:
  forall (E : R -> Prop) (p : R),
  limit_point E p ->
  forall N : R->Prop,
  neighbourhood p N ->
  exists q : R, N q /\ E q /\ q <> p.
Proof.
Admitted.
Lemma list_min_le : forall (l : list R) (x : R),
  In x l -> list_min l <= x.
Proof.

Admitted.

Lemma map_nonempty : forall (A B : Type) (f : A -> B) (l : list A),
  l <> [] -> map f l <> [].
Proof.
  intros A B f l H.
  destruct l as [|h t]; [contradiction | simpl; discriminate].
Qed.

(* 定理 2.20 *)
Theorem theorem_2_20 `{MetricSpace R}: forall (E : R -> Prop) (p : R),
    limit_point E p ->
    forall N : R -> Prop,
      neighbourhood p N-> infinite_intersection N E p .
Proof.
  intros E p Hlim N Hneigh.
  unfold infinite_intersection, infinite_set.
  intros [l Hl].
  pose (dists := map (fun x => dist x p) l).
  pose (r := list_min dists).
  assert (r > 0).
  subst r.
  subst dists.
  apply list_min_pos.
  apply map_nonempty.
  assert (exists q : R, N q /\ E q /\ q <> p).
  apply neighbourhood_contains_other_point.
  auto.
  auto.
  destruct H0 as [q [H_N [H_E H_neq]]].
  assert (In q l).
  apply Hl; repeat auto.
  destruct l.
  inversion H0.
  discriminate.
  intros x HH.
  apply in_map_iff in HH as [y [H_eq H_in]].
  apply Hl in H_in as [H_N [H_E H_neq]].
  subst.
  assert (0 <= dist y p).
  apply dist_nonneg.
  assert ( 0 <> dist y p).
  intros H00.
  symmetry in H00.
  rewrite  dist_eq_0 in H00.
  auto.
  lra.
  unfold limit_point in *.
  destruct Hneigh as [delta [delta_pos Hdelta]].
  pose (eps := Rmin delta (r / 2)).
  assert (eps_pos : eps > 0) by (apply Rmin_pos; [exact delta_pos | lra]).
  destruct (Hlim eps eps_pos) as [q' [Eq' [q'_neq_p Hdist]]].
  assert (N q') as N_q'.
  { apply Hdelta.
  apply Rlt_le_trans with eps; [exact Hdist | apply Rmin_l]. }
  assert (In q' l) as In_q'.
{ apply Hl; repeat split; auto. }
assert (r <= dist q' p) as r_le_dist.
{ unfold r, dists.
  apply list_min_le.
  pose (fun1 := fun x => dist x p).
  Check in_map.
  apply in_map with (f := fun1) (x := q') (l := l).
  assumption.
  }.
assert (dist q' p < r / 2) as dist_lt_half.
{ apply Rlt_le_trans with eps; [exact Hdist | apply Rmin_r]. }
lra.
Qed.
