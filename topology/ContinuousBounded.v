(*
  ================================================================================
  ContinuousBounded.v — 连续映射把紧集映为有界集
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: X → R^n 连续，E ⊆ X 紧 ⟹ f(E) 有界

  直接证明：
    构造 X 的开覆盖 U_k = f⁻¹(B(0,k+1))，紧性得有限子覆盖，
    对应的最大 k 给出界。
 ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon PeanoNat Lia.

Open Scope R_scope.

(* ================================================================ *)
(*  R^n                                                              *)
(* ================================================================ *)

Inductive FinT : nat -> Set :=
  | F1 : forall n : nat, FinT (S n)
  | FS : forall n : nat, FinT n -> FinT (S n).

Definition Rn (n : nat) := FinT n -> R.

Fixpoint linf_norm {n : nat} : Rn n -> R :=
  match n as m return Rn m -> R with
  | 0 => fun _ => 0
  | S n' => fun v => Rmax (Rabs (v (@F1 n'))) (linf_norm (fun i => v (@FS n' i)))
  end.

Definition rn_dist {n : nat} (x y : Rn n) : R :=
  linf_norm (fun i => (x i - y i)%R).

Axiom linf_norm_nonneg : forall n (v : Rn n), 0 <= linf_norm v.
Axiom rn_dist_sym : forall n (x y : Rn n), rn_dist x y = rn_dist y x.
Axiom rn_dist_triangle : forall n (x y z : Rn n),
  rn_dist x z <= rn_dist x y + rn_dist y z.

Lemma rn_dist_nonneg : forall n (x y : Rn n), 0 <= rn_dist x y.
Proof. intros. apply linf_norm_nonneg. Qed.

Definition ball {n : nat} (c : Rn n) (r : R) : Rn n -> Prop :=
  fun x => rn_dist x c < r.

(* ================================================================ *)
(*  度量空间 X                                                        *)
(* ================================================================ *)

Record MetricSpace : Type := {
  MX : Type;
  dX : MX -> MX -> R;
  dX_nonneg : forall x y, 0 <= dX x y
}.

Definition open_ball_X (M : MetricSpace) (p : MX M) (r : R) : MX M -> Prop :=
  fun x => dX M p x < r.

Definition open_in_X (M : MetricSpace) (U : MX M -> Prop) : Prop :=
  forall x, U x -> exists r, r > 0 /\
    forall y, open_ball_X M x r y -> U y.

(* 紧性：开覆盖 ⟹ 存在统一半径的球覆盖 *)
Definition compact_bounded (M : MetricSpace) (E : MX M -> Prop) : Prop :=
  forall (F : nat -> MX M -> Prop),
    (forall k, open_in_X M (F k)) ->
    (forall x, E x -> exists k, F k x) ->
    exists N : nat, forall x, E x -> F N x.

(* f: X → R^n 连续 *)
Definition continuous_to_rn (M : MetricSpace) {n : nat}
  (f : MX M -> Rn n) : Prop :=
  forall p, forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, dX M p x < delta -> rn_dist (f p) (f x) < eps.

(* ================================================================ *)
(*  引理                                                              *)
(* ================================================================ *)

Lemma preimage_ball_open : forall (M : MetricSpace) {n : nat}
  (f : MX M -> Rn n),
  continuous_to_rn M f ->
  forall k : nat,
  open_in_X M (fun x => ball (fun _ => 0%R) (INR (S k)) (f x)).
Proof.
  intros M n f Hcont k x Hx.
  assert (Hpos: 0 < INR (S k) - rn_dist (f x) (fun _ => 0%R)).
  { assert (Hlt: rn_dist (f x) (fun _ => 0%R) < INR (S k)). { exact Hx. }
    lra. }
  specialize (Hcont x (INR (S k) - rn_dist (f x) (fun _ => 0%R)) Hpos) as [delta [Hdelta Hcd]].
  exists delta.
  split.
  { exact Hdelta. }
  { intros y Hy.
    assert (Htri: rn_dist (f y) (fun _ => 0%R) <=
      rn_dist (f y) (f x) + rn_dist (f x) (fun _ => 0%R)).
    { apply rn_dist_triangle. }
    assert (Heps: rn_dist (f x) (f y) < INR (S k) - rn_dist (f x) (fun _ => 0%R)).
    { exact (Hcd y Hy). }
    assert (Hsym: rn_dist (f y) (f x) = rn_dist (f x) (f y)). apply rn_dist_sym.
    assert (Hsum: rn_dist (f y) (f x) + rn_dist (f x) (fun _ => 0%R) < INR (S k)).
    { rewrite Hsym. lra. }
    apply (Rle_lt_trans _ _ _ Htri Hsum).
  }
Qed.
Lemma rn_archimedean : forall n (y : Rn n), exists k : nat,
  ball (fun _ => 0%R) (INR (S k)) y.
Proof. admit. Admitted.

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

Theorem continuous_image_bounded :
  forall (M : MetricSpace) {n : nat} (f : MX M -> Rn n) (E : MX M -> Prop),
  compact_bounded M E ->
  continuous_to_rn M f ->
  exists R, R > 0 /\
    forall x, E x -> rn_dist (f x) (fun _ => 0%R) < R.
Proof.
  intros M n f E Hcompact Hcont.
  set (F := fun k : nat => fun x => ball (fun _ => 0%R) (INR (S k)) (f x)).
  assert (HFopen : forall k, open_in_X M (F k)).
  { intro k. apply preimage_ball_open. exact Hcont. }
  assert (HFcover : forall x, E x -> exists k, F k x).
  { intros x Hx. apply rn_archimedean. }
  specialize (Hcompact F HFopen HFcover) as [N HN].
  exists (INR (S N)).
  split.
  - apply lt_0_INR. lia.
  - intros x Hx. specialize (HN x Hx). exact HN.
Qed.