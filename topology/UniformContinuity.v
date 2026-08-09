(*
  ================================================================================
  UniformContinuity.v — 紧度量空间上连续函数一致连续
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: X → Y 连续，X 紧 ⟹ f 在 X 上一致连续

  与 ContinuousCompact.v 共享 Compact 定义（nat-索引 σ 有限子覆盖）。
  ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon PeanoNat Compare_dec Psatz.

Open Scope R_scope.

(* ================================================================ *)
(*  度量空间                                                          *)
(* ================================================================ *)

Record MetricSpace : Type := mkMetricSpace {
  MS : Type;
  d : MS -> MS -> R;
  d_nonneg : forall x y, 0 <= d x y;
  d_eq : forall x y, d x y = 0 <-> x = y;
  d_sym : forall x y, d x y = d y x;
  d_triangle : forall x y z, d x z <= d x y + d y z
}.

Definition ball (M : MetricSpace) (c : MS M) (r : R) : MS M -> Prop :=
  fun x => d M c x < r.

Definition OpenSet (M : MetricSpace) (U : MS M -> Prop) : Prop :=
  forall x, U x -> exists r, r > 0 /\
    forall y, ball M x r y -> U y.

(* ================================================================ *)
(*  连续 / 一致连续                                                    *)
(* ================================================================ *)

Definition Continuous (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) : Prop :=
  forall p, forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, d M1 p x < delta -> d M2 (f p) (f x) < eps.

Definition UniformlyContinuous (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x y, d M1 x y < delta -> d M2 (f x) (f y) < eps.

(* ================================================================ *)
(*  紧性（与 ContinuousCompact.v 一致）                              *)
(* ================================================================ *)

Definition CompactSpace (M : MetricSpace) (E : MS M -> Prop) : Prop :=
  forall F : (MS M -> Prop) -> Prop,
    (forall U, F U -> OpenSet M U) ->
    (forall x, E x -> exists U, F U /\ U x) ->
    exists (n : nat) (sigma : nat -> MS M -> Prop),
      (forall i, (i < n)%nat -> F (sigma i)) /\
      (forall x, E x -> exists i, (i < n)%nat /\ sigma i x).

(* ================================================================ *)
(*  引理                                                              *)
(* ================================================================ *)

Lemma ball_is_open : forall (M : MetricSpace) p r,
  r > 0 -> OpenSet M (ball M p r).
Proof.
  intros M p r Hr. unfold OpenSet. intros z Hz.
  unfold ball in Hz.
  exists (r - d M p z). split.
  - lra.
  - intros w Hw. unfold ball.
    assert (Htri : d M p w <= d M p z + d M z w). { apply d_triangle. }
    apply (Rle_lt_trans _ _ _ Htri).
    assert (Htmp := Rplus_lt_compat_l (d M p z) (d M z w) (r - d M p z) Hw).
    assert (Heq: d M p z + (r - d M p z) = r). { lra. }
    rewrite Heq in Htmp.
    exact Htmp.
Qed.

(* 递归定义 [0, n) 上函数值的最小值 *)
Fixpoint finite_min (n : nat) (r : nat -> R) : R :=
  match n with
  | 0%nat => r 0%nat
  | S m => Rmin (r m) (finite_min m r)
  end.

Lemma finite_min_pos : forall (n : nat) (r : nat -> R),
  (forall i, (i < S n)%nat -> r i > 0) ->
  finite_min (S n) r > 0.
Proof.
  induction n as [|n IH]; intros r Hpos.
  - simpl. replace (Rmin (r 0%nat) (r 0%nat)) with (r 0%nat). apply Hpos. lia.
    symmetry. apply Rmin_left. apply Rle_refl.
  - simpl. apply Rmin_case.
    + apply Hpos. lia.
    + apply IH. intros i Hi. apply Hpos. lia.
Qed.

Lemma finite_min_le : forall (n : nat) (r : nat -> R) (i : nat),
  (i < S n)%nat -> finite_min (S n) r <= r i.
Proof.
  induction n as [|n IH]; intros r i Hi.
  - destruct i as [|i']. simpl. apply Rmin_l.
    lia.
  - simpl. destruct (Nat.eq_dec i (S n)) as [Heq | Hneq].
    + subst i. apply Rmin_l.
    + transitivity (finite_min (S n) r). apply (Rmin_r (r (S n)) (finite_min (S n) r)).
      apply IH. lia.
Qed.

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

Theorem compact_continuous_implies_uniform :
  forall (M1 M2 : MetricSpace) (f : MS M1 -> MS M2),
  CompactSpace M1 (fun _ => True) -> Continuous M1 M2 f -> UniformlyContinuous M1 M2 f.
Proof.
  intros M1 M2 f Hcompact Hcont.
  unfold UniformlyContinuous. intros eps Heps.
  set (half_eps := eps / 2).
  assert (Hhalf: half_eps > 0). unfold half_eps. lra.
  (* 1. 连续性给出每点 p 的 δ_p — 用 constructive_indefinite_description 从 Prop 提取 R *)
  set (dp_sig := fun p => constructive_indefinite_description _
    (Hcont p half_eps Hhalf)).
  set (dp := fun p => proj1_sig (dp_sig p)).
  assert (Hdp_pos : forall p, dp p > 0). {
    intro p. exact (proj1 (proj2_sig (dp_sig p))). }
  assert (Hdp_cont : forall p x, d M1 p x < dp p -> d M2 (f p) (f x) < half_eps). {
    intros p x Hx. exact (proj2 (proj2_sig (dp_sig p)) x Hx). }
  (* 2. 构造开覆盖 *)
  set (F := fun U => exists p, U = ball M1 p (dp p / 2)).
  assert (HFopen : forall U, F U -> OpenSet M1 U).
  { intros U [p HU]. rewrite HU. apply ball_is_open.
    assert (Hpos := Hdp_pos p). nra. }
  assert (HFcover : forall x, exists U, F U /\ U x).
  { intros x. exists (ball M1 x (dp x / 2)).
    split; [exists x; reflexivity | unfold ball. apply Hdp_pos]. }
  (* 3. 紧性得有限子覆盖 *)
  specialize (Hcompact F HFopen HFcover) as [n [sigma [HFsub HFcover']]].
  (* 4. 提取半径 r_i = dp(p_i)/2 其中 σ(i) = ball(p_i, dp(p_i)/2) *)
  assert (Hsig : forall i, (i < n)%nat ->
    exists p : MS M1, sigma i = ball M1 p (dp p / 2)). {
    intros i Hi. exact (HFsub i Hi).
  }
  set (r_i := fun i =>
    match Compare_dec.lt_dec i n with
    | left Hi => let (p, _) := constructive_indefinite_description _ (Hsig i Hi) in dp p / 2
    | right _ => 1  (* dummy, i≥n 时不会被使用 *)
    end).
  (* 5. 定义 δ = min_{i < n} r_i *)
  destruct n as [|n'].
  - exists 1. split. lra.
    intros x y Hxy. specialize (HFcover' x (eq_refl _)) as [i [Hi _]]. lia.
  - set (delta := finite_min (S n') r_i).
    assert (Hdelta_pos: delta > 0). {
      apply finite_min_pos. intros i Hi.
      unfold r_i. destruct (Compare_dec.lt_dec i (S n')).
      - destruct (constructive_indefinite_description _ (Hsig i l)). simpl. apply Hdp_pos.
      - lia.
    }
    exists delta. split. exact Hdelta_pos.
    (* 6. 验证一致连续条件 *)
    intros x y Hxy.
    specialize (HFcover' x (eq_refl _)) as [i [Hi Hxsigma]].
    assert (Hsig_i := Hsig i Hi).
    set (p_i_val := proj1_sig (constructive_indefinite_description _ (Hsig_i))).
    assert (Hsigma_eq : sigma i = ball M1 p_i_val (dp p_i_val / 2)). {
      destruct (constructive_indefinite_description _ (Hsig_i)). simpl. exact e.
    }
    rewrite Hsigma_eq in Hxsigma.
    assert (Hxball: d M1 p_i_val x < dp p_i_val / 2). { unfold ball in Hxsigma. exact Hxsigma. }
    (* d(p_i, y) ≤ d(p_i, x) + d(x,y) < dp(p_i)/2 + delta ≤ dp(p_i) *)
    assert (Hmin_le: delta <= r_i i). { apply finite_min_le. lia. }
    assert (Hyball: d M1 p_i_val y < dp p_i_val). {
      pose proof (d_triangle M1 p_i_val x y) as Htri.
      assert (Hd: d M1 p_i_val x + d M1 x y < dp p_i_val / 2 + delta). lra.
      assert (Him: dp p_i_val / 2 + delta <= dp p_i_val). {
        unfold r_i in Hmin_le. destruct (Compare_dec.lt_dec i (S n')).
        - destruct (constructive_indefinite_description _ (Hsig i l)). simpl in Hmin_le.
          rewrite <- Hmin_le. lra.
        - lia.
      }
      lra.
    }
    assert (Hxball': d M1 p_i_val x < dp p_i_val). {
      assert (Hd: d M1 p_i_val x < dp p_i_val / 2). lra.
      assert (Him: dp p_i_val / 2 < dp p_i_val). { apply (Hdp_pos p_i_val). }
      lra.
    }
    specialize (Hdp_cont p_i_val x Hxball') as Hfx.
    specialize (Hdp_cont p_i_val y Hyball) as Hfy.
    pose proof (d_triangle M2 (f p_i_val) (f x) (f y)) as Htri.
    assert (Hd: d M2 (f p_i_val) (f x) + d M2 (f p_i_val) (f y) < half_eps + half_eps). lra.
    assert (He: half_eps + half_eps = eps). unfold half_eps. lra.
    rewrite He in Hd. lra.
Qed.
