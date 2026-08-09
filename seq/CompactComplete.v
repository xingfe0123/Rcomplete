From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Compare_dec.
From Stdlib Require Import ClassicalEpsilon.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Import FunctionalExtensionality.

Open Scope R_scope.

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
  apply Rmult_le_compat_l. lra. exact Hle.
Qed.

Lemma dist_nonneg :
  forall (ms : MetricSpace) (x y : ms), 0 <= @dist ms x y.
Proof.
  intros ms x y.
  assert (H1 : @dist ms x x <= @dist ms x y + @dist ms y x).
  { apply (@dist_triangle ms). }
  rewrite (@dist_self ms) in H1.
  assert (H2 : @dist ms x y + @dist ms y x = @dist ms x y + @dist ms x y).
  { f_equal. apply (@dist_sym ms). }
  rewrite H2 in H1.
  assert (H3 : @dist ms x y + @dist ms x y = 2 * @dist ms x y). { lra. }
  rewrite H3 in H1.
  assert (H4 : / 2 > 0). { apply Rinv_0_lt_compat. lra. }
  assert (H5 := Rmult_le_compat_r_pos (/ 2) 0 (2 * @dist ms x y) H4 H1).
  assert (H6a : / 2 * 2 = 1). { rewrite Rmult_comm. apply Rinv_r. lra. }
  assert (H6 : / 2 * (2 * @dist ms x y) = @dist ms x y).
  { rewrite <- Rmult_assoc. rewrite H6a. rewrite Rmult_1_l. lra. }
  assert (H7 : / 2 * 0 = 0). { apply Rmult_0_r. }
  rewrite H6 in H5. rewrite H7 in H5. exact H5.
Qed.

(******************************************************************************)
(* Cauchy 序列定义                                                             *)
(******************************************************************************)

Definition cauchy_seq (ms : MetricSpace) (p : nat -> ms) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall m n : nat, (N <= m)%nat -> (N <= n)%nat -> @dist ms (p m) (p n) < eps.

(******************************************************************************)
(* 收敛定义                                                                    *)
(******************************************************************************)

Definition convergent (ms : MetricSpace) (p : nat -> ms) (p0 : ms) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, (N <= n)%nat -> @dist ms (p n) p0 < eps.

(******************************************************************************)
(* 完备度量空间定义                                                             *)
(******************************************************************************)

Definition complete (ms : MetricSpace) : Prop :=
  forall p : nat -> ms, cauchy_seq ms p -> exists p0 : ms, convergent ms p p0.

(******************************************************************************)
(* 开球定义                                                                    *)
(******************************************************************************)

Definition open_ball (ms : MetricSpace) (c : ms) (r : R) : ms -> Prop :=
  fun x => @dist ms x c < r.

(******************************************************************************)
(* 开覆盖定义                                                                  *)
(******************************************************************************)

Definition open_cover (ms : MetricSpace) (U : ms -> Prop) (I : Type) (f : I -> ms -> Prop) : Prop :=
  (forall i : I, exists (c : ms) (r : R), r > 0 /\ forall x : ms, @dist ms x c < r -> U x) /\
  forall x : ms, U x -> exists i : I, f i x.

(******************************************************************************)
(* 紧致性定义：序列紧 (每个序列有收敛子列)                                      *)
(******************************************************************************)

Definition seq_compact (ms : MetricSpace) : Prop :=
  forall p : nat -> ms,
    exists (phi : nat -> nat) (p0 : ms),
      (forall m n : nat, (m < n)%nat -> (phi m < phi n)%nat) /\
      convergent ms (fun n => p (phi n)) p0.

(******************************************************************************)
(* 引理：eps / 2 > 0                                                           *)
(******************************************************************************)

Lemma half_gt_zero (eps : R) : eps > 0 -> eps / 2 > 0.
Proof.
  intro Heps. unfold Rdiv.
  assert (Hinv : / 2 > 0). { apply Rinv_0_lt_compat. lra. }
  assert (Hres := Rmult_lt_compat_l (/ 2) 0 eps Hinv Heps).
  rewrite Rmult_0_r in Hres. lra.
Qed.

(******************************************************************************)
(* 引理：若 x < eps 对所有 eps > 0 成立，则 x <= 0                              *)
(******************************************************************************)

Lemma lt_all_eps_le_0 (x : R) :
  (forall eps : R, eps > 0 -> x < eps) -> x <= 0.
Proof.
  intros H. apply Rnot_lt_le. intro Hpos. specialize (H x Hpos). lra.
Qed.

(******************************************************************************)
(* 引理：有限最大值                                                             *)
(******************************************************************************)

Fixpoint maxn (f : nat -> R) (n : nat) : R :=
  match n with
  | 0 => 0
  | S k => max (f k) (maxn f k)
  end.

Lemma maxn_ge :
  forall (f : nat -> R) (n m : nat),
    (m < n)%nat -> f m <= maxn f n.
Proof.
  intros f. induction n as [|n IH].
  - intro m Hm. lia.
  - intro m Hm. simpl.
    destruct (Nat.eq_dec m n) as [Hmne | Hmne].
    + subst. apply max_le.
      * lra.
      * exact (IH Hm).
    + apply max_le_r.
      * exact (IH Hm).
Qed.

(******************************************************************************)
(* 引理：Cauchy 列有界                                                         *)
(******************************************************************************)

Lemma cauchy_bounded :
  forall (ms : MetricSpace) (p : nat -> ms),
    cauchy_seq ms p ->
    exists (q : ms) (M : R), M > 0 /\ forall n : nat, @dist ms (p n) q < M.
Proof.
  intros ms p Hcauchy.
  assert (H1 : 1 > 0). { lra. }
  specialize (Hcauchy 1 H1) as [N HN].
  exists (p N).
  exists (2 + maxn (fun k => @dist ms (p k) (p N)) N).
  split.
  - assert (Hnonneg : 0 <= maxn (fun k => @dist ms (p k) (p N)) N).
    { induction N as [|N IH].
      - reflexivity.
      - simpl. apply max_nonneg. exact IH. rewrite dist_nonneg. }
    lra.
  - intro n.
    destruct (Nat.le_dec n N) as [HnN | HnN].
    + (* n <= N *)
      assert (Hn_lt : (n < S N)%nat). { lia. }
      assert (Hdist_le : @dist ms (p n) (p N) <= maxn (fun k => @dist ms (p k) (p N)) (S N)).
      { apply maxn_ge. exact Hn_lt. }
      lra.
    + (* n > N *)
      specialize (HN n n HnN HnN). lra.
Qed.

Lemma strict_increasing_ge :
  forall (phi : nat -> nat),
    (forall m n : nat, (m < n)%nat -> (phi m < phi n)%nat) ->
    forall k, (phi k >= k)%nat.
Proof.
  intros phi Hphi k. induction k as [|k IH].
  - lia.
  - assert (Hlt : (k < S k)%nat). lia.
    specialize (Hphi k (S k) Hlt). lia.
Qed.

(******************************************************************************)
(* 引理：Cauchy 列的子列收敛到 L，则 Cauchy 列本身收敛到 L                     *)
(******************************************************************************)

Lemma cauchy_subseq_conv :
  forall (ms : MetricSpace) (p : nat -> ms) (phi : nat -> nat) (L : ms),
    cauchy_seq ms p ->
    (forall m n : nat, (m < n)%nat -> (phi m < phi n)%nat) ->
    convergent ms (fun n => p (phi n)) L ->
    convergent ms p L.
Proof.
  intros ms p phi L Hcauchy Hphi Hsub.
  intros eps Heps.
  pose proof (half_gt_zero eps Heps) as Hhalf.
  specialize (Hcauchy (eps / 2) Hhalf) as [N1 HN1].
  specialize (Hsub (eps / 2) Hhalf) as [N2 HN2].
  exists (N1 + N2)%nat.
  intros n Hn.
  assert (Hn1 : (N1 <= n)%nat). { lia. }
  assert (HphiN1 : (N1 <= phi (N1 + N2 + n))%nat).
  { assert (Hk : (phi (N1 + N2 + n) >= N1 + N2 + n)%nat).
    { apply strict_increasing_ge. exact Hphi. }
    lia. }
  assert (HphiN2 : (N2 <= phi (N1 + N2 + n))%nat).
  { assert (Hk : (phi (N1 + N2 + n) >= N1 + N2 + n)%nat).
    { apply strict_increasing_ge. exact Hphi. }
    lia. }
  specialize (HN2 (N1 + N2 + n)%nat) as HsubN.
  assert (HsubNbound : (N2 <= N1 + N2 + n)%nat). { lia. }
  specialize (HsubN HsubNbound).
  specialize (HN1 n (phi (N1 + N2 + n)%nat) Hn1 HphiN1).
  assert (Htri : @dist ms (p n) L <= @dist ms (p n) (p (phi ((N1 + N2 + n)%nat))) + @dist ms (p (phi ((N1 + N2 + n)%nat))) L).
  { apply (@dist_triangle ms). }
  eapply Rle_lt_trans. exact Htri. lra.
Qed.

(******************************************************************************)
(* 主定理：序列紧度量空间是完备的                                               *)
(******************************************************************************)

Theorem seq_compact_complete :
  forall (ms : MetricSpace), seq_compact ms -> complete ms.
Proof.
  intros ms Hcompact p Hcauchy.
  destruct (Hcompact p) as [phi [L [Hphi Hconv]]].
  exists L.
  exact (cauchy_subseq_conv ms p phi L Hcauchy Hphi Hconv).
Qed.
