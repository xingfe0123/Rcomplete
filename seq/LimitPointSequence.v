From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Compare_dec.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ClassicalEpsilon.

Open Scope R_scope.
Open Scope list_scope.

Import ListNotations.

(******************************************************************************)
(* 度量空间定义                                                                *)
(******************************************************************************)

Record MetricSpace : Type := {
  Carrier :> Type;
  dist : Carrier -> Carrier -> R;
  dist_self : forall x, dist x x = 0;
  dist_sym : forall x y, dist x y = dist y x;
  dist_triangle : forall x y z, dist x z <= dist x y + dist y z;
  dist_eq_ident : forall x y, dist x y = 0 -> x = y
}.

(******************************************************************************)
(* 距离非负性                                                                  *)
(******************************************************************************)

Lemma Rmult_le_compat_r_pos : forall r r1 r2 : R, r > 0 -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros r r1 r2 Hpos Hle.
  apply Rmult_le_compat_l.
  lra.
  exact Hle.
Qed.

Lemma dist_nonneg :
  forall (ms : MetricSpace) (x y : ms),
    0 <= @dist ms x y.

Proof.
  intros ms x y.
  assert (H1 : @dist ms x x <= @dist ms x y + @dist ms y x).
  { apply (@dist_triangle ms). }
  rewrite (@dist_self ms) in H1.
  assert (H2 : @dist ms x y + @dist ms y x = @dist ms x y + @dist ms x y).
  { f_equal. apply (@dist_sym ms). }
  rewrite H2 in H1.
  assert (H3 : @dist ms x y + @dist ms x y = 2 * @dist ms x y).
  { lra. }
  rewrite H3 in H1.
  assert (H4 : / 2 > 0).
  { apply Rinv_0_lt_compat. lra. }
  assert (H5 := Rmult_le_compat_r_pos (/ 2) 0 (2 * @dist ms x y) H4 H1).
  assert (H6a : / 2 * 2 = 1).
  { rewrite Rmult_comm. apply Rinv_r. lra. }
  assert (H6 : / 2 * (2 * @dist ms x y) = @dist ms x y).
  { rewrite <- Rmult_assoc. rewrite H6a. rewrite Rmult_1_l. lra. }
  assert (H7 : / 2 * 0 = 0).
  { apply Rmult_0_r. }
  rewrite H6 in H5. rewrite H7 in H5.
  exact H5.
Qed.

(******************************************************************************)
(* 序列收敛定义                                                                *)
(******************************************************************************)

Definition convergent (ms : MetricSpace) (p : nat -> ms) (p0 : ms) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, (N <= n)%nat -> @dist ms (p n) p0 < eps.

(******************************************************************************)
(* 极限点定义                                                                  *)
(******************************************************************************)

Definition limit_point (ms : MetricSpace) (E : ms -> Prop) (p : ms) : Prop :=
  forall eps : R, eps > 0 ->
    exists q : ms, E q /\ q <> p /\ @dist ms q p < eps.

(******************************************************************************)
(* 引理：1 / (n + 1) > 0 当 n : nat                                          *)
(******************************************************************************)

Lemma inv_nat_pos (n : nat) :
  / (INR (n + 1)) > 0.
Proof.
  apply Rinv_0_lt_compat.
  rewrite plus_INR.
  assert (H : INR n >= 0).
  { induction n.
    - simpl. lra.
    - rewrite S_INR. lra. }
  assert (H1 : 1 > 0).
  { lra. }
  assert (H2 : INR n + 1 >= 1).
  { lra. }
  assert (H3 : INR n + 1 > 0).
  { lra. }
  exact H3.
Qed.

(******************************************************************************)
(* 引理：对任意 eps > 0，存在 N 使得 1/(N+1) < eps                          *)
(******************************************************************************)

Lemma exists_nat_inv_lt (eps : R) :
  eps > 0 -> exists N : nat, / (INR (N + 1)) < eps.
Proof.
  intro Heps.
  (* 由 Archimedean 性质，存在 N 使得 INR(N+1) > 1/eps *)
  (* 即 1/INR(N+1) < eps *)
  assert (H : / eps > 0).
  { apply Rinv_0_lt_compat. lra. }
  assert (Hexists : exists n : nat, INR n > / eps).
  { specialize (archimed (/ eps)) as [n Hn].
    (* n 是 Z 类型，需要转换为 nat *)
    (* 由于 n > / eps > 0，所以 n > 0 *)
    destruct n as [p| |p].
    - (* p : positive *)
      exists (Pos.to_nat p).
      assert (Hconvert : INR (Pos.to_nat p) = IZR (Zpos p)).
      { rewrite INR_IZR_INZ.
        assert (Hpos : 0 <= Zpos p) by apply Pos2Z.pos_is_pos.
        rewrite (Z2Nat.id (Zpos p) Hpos). reflexivity. }
      rewrite Hconvert.
      lra.
    - (* 0 的情况：不可能 *)
      simpl in Hn.
      exfalso.
      lra.
    - (* negative 的情况：不可能 *)
      simpl in Hn.
      exfalso.
      lra. }
  destruct Hexists as [N HN].
  exists N.
  assert (H : / (INR (N + 1)) < eps).
  { (* 由 INR(N) > / eps 推出 / INR(N) < eps *)
    (* 但我们需要的是 / INR(N+1) < eps *)
    (* 由于 INR(N+1) > INR(N) > / eps，所以 / INR(N+1) < eps *)
    assert (H1 : INR (N + 1) > INR N).
    { rewrite plus_INR. assert (H1 : INR N >= 0). { apply pos_INR. }
      lra. }
    assert (H2 : INR (N + 1) > / eps).
    { lra. }
    assert (H3 : INR (N + 1) > 0).
    { lra. }
    apply Rinv_lt_contravar.
    - apply Rmult_gt_0_compat.
      + lra.
      + lra.
    - lra. }
  exact H.
Qed.

(******************************************************************************)
(* 定理：极限点存在收敛序列                                                    *)
(******************************************************************************)

Theorem limit_point_sequence :
  forall (ms : MetricSpace) (E : ms -> Prop) (p : ms),
    limit_point E p ->
    exists p_n : nat -> ms, (forall n, E (p_n n)) /\ convergent ms p_n p.

Proof.
  intros ms E p Hlp.
  assert (Hchoice : {p_n : nat -> ms | forall n, E (p_n n) /\ p_n n <> p /\ @dist ms (p_n n) p < / (INR (n + 1))}).
  { apply constructive_indefinite_description.
    intro n.
    specialize (Hlp (/ (INR (n + 1)))) as [q [HE [Hnp Hdist]]].
    apply inv_nat_pos.
    exists q. split. exact HE. split. exact Hnp. exact Hdist. }
  destruct Hchoice as [p_n Hp_n].
  exists p_n.
  split.
  - intro n. specialize (Hp_n n) as [HE _]. exact HE.
  - intros eps Heps.
    destruct (exists_nat_inv_lt eps Heps) as [N HN].
    exists (N + 1).
    intros n Hn.
    specialize (Hp_n n) as [_ [_ Hdist]].
    assert (H : / (INR (n + 1)) <= / (INR (N + 1))).
    { apply Rinv_le_contravar.
      - rewrite plus_INR. assert (H1 : INR N >= 0). { apply pos_INR. }
        assert (H2 : INR n >= 0). { apply pos_INR. }
        assert (H3 : 1 > 0). { lra. }
        assert (H4 : INR N + 1 > 0). { lra. }
        lra.
      - apply le_INR. lia. }
    assert (H2 : / (INR (n + 1)) < eps).
    { lra. }
    lra.
Qed.
