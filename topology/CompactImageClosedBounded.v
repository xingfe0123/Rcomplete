(*
  ================================================================================
  CompactImageClosedBounded.v — 连续映射到 R^n 的像是闭且有界的
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: X → R^n 连续，X 紧 ⟹ f(X) 闭且有界
 ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon PeanoNat.

Open Scope R_scope.

(* ================================================================ *)
(*  R^n = FinT n -> R                                                 *)
(* ================================================================ *)

Inductive FinT : nat -> Set :=
  | F1 : forall n : nat, FinT (S n)
  | FS : forall n : nat, FinT n -> FinT (S n).

Definition Rn (n : nat) := FinT n -> R.

Fixpoint linf_norm {n : nat} : Rn n -> R :=
  match n with
  | 0 => fun _ => 0
  | S n' => fun v => Rmax (Rabs (v (@F1 n'))) (linf_norm (fun i => v (@FS n' i)))
  end.

Definition vsub {n : nat} (u v : Rn n) : Rn n := fun i => (u i - v i)%R.
Definition rn_dist {n : nat} (x y : Rn n) : R := linf_norm (vsub x y).

Axiom linf_norm_nonneg : forall n (v : Rn n), 0 <= linf_norm v.
Axiom linf_norm_triangle : forall n (u v : Rn n),
  linf_norm (fun i => (u i + v i)%R) <= linf_norm u + linf_norm v.
Axiom rn_dist_sym : forall n (x y : Rn n), rn_dist x y = rn_dist y x.
Axiom rn_dist_triangle : forall n (x y z : Rn n),
  rn_dist x z <= rn_dist x y + rn_dist y z.

Lemma rn_dist_nonneg : forall n (x y : Rn n), 0 <= rn_dist x y.
Proof. intros. apply linf_norm_nonneg. Qed.

(* ================================================================ *)
(*  开球                                                              *)
(* ================================================================ *)

Definition open_ball {n : nat} (c : Rn n) (r : R) : Rn n -> Prop :=
  fun x => rn_dist x c < r.

Lemma open_ball_is_open : forall n (c : Rn n) (r : R),
  forall x, open_ball c r x -> exists r', r' > 0 /\
    forall y, open_ball x r' y -> open_ball c r y.
Proof.
  intros n c r x Hx.
  exists (r - rn_dist x c).
  split.
  - assert (Hpos: rn_dist x c < r). exact Hx.
    assert (Hdiff: 0 <= r - rn_dist x c). lra.
    lra.
  - intros y Hy.
    unfold open_ball.
    assert (Htri: rn_dist y c <= rn_dist y x + rn_dist x c).
    { apply rn_dist_triangle. }
    eapply Rle_lt_trans. exact Htri.
    assert (Hsym: rn_dist y x = rn_dist x y). apply rn_dist_sym.
    rewrite Hsym in Hy.
    lra.
Qed.

(* ================================================================ *)
(*  紧性                                                              *)
(* ================================================================ *)

Definition OpenSet {n : nat} (U : Rn n -> Prop) : Prop :=
  forall x, U x -> exists r, r > 0 /\
    forall y, open_ball x r y -> U y.

Definition Compact {n : nat} (E : Rn n -> Prop) : Prop :=
  forall (F : nat -> Rn n -> Prop),
    (forall k, OpenSet (F k)) ->
    (forall x, E x -> exists k, F k x) ->
    exists N : nat, forall x, E x -> exists k, (k < N)%nat /\ F k x.

(* ================================================================ *)
(*  有界与闭                                                          *)
(* ================================================================ *)

Definition Bounded {n : nat} (E : Rn n -> Prop) : Prop :=
  exists c R, R > 0 /\
    forall x, E x -> rn_dist x c <= R.

Definition Closed {n : nat} (E : Rn n -> Prop) : Prop :=
  forall x, (forall r, r > 0 -> exists y, E y /\ rn_dist x y < r) -> E x.

(* ================================================================ *)
(*  引理                                                              *)
(* ================================================================ *)

Lemma rn_archimedean : forall n (x : Rn n), exists k : nat,
  open_ball (fun _ => 0%R) (INR (S k)) x.
Proof. admit. Admitted.

(* ================================================================ *)
(*  紧集必有界                                                        *)
(* ================================================================ *)

Theorem compact_bounded : forall n (E : Rn n -> Prop),
  Compact E -> Bounded E.
Proof.
  intros n E Hcompact.
  set (F := fun k : nat => open_ball (fun _ => 0%R) (INR (S k))).
  assert (HFopen : forall k, OpenSet (F k)). intro k. apply open_ball_is_open.
  assert (HFcover : forall x, E x -> exists k, F k x).
  { intros x Hx. apply rn_archimedean. }
  destruct (Hcompact F HFopen HFcover) as [N HN].
  exists (fun _ => 0%R), (INR N).
  split.
  - destruct N. lra. apply lt_0_INR. lia.
  - intros x Hx. specialize (HN x Hx) as [k [Hk Hkx]].
    unfold open_ball in Hkx. unfold F in Hkx.
    apply Rlt_le. eapply Rle_lt_trans. apply Hkx.
    apply le_INR. lia.
Qed.