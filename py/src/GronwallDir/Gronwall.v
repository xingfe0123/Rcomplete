(* Gronwall.v *)
(* Compressible Gronwall inequality in ODE form, formalised in
   Record+Axiom style. Target statement:

     Given delta > 0, y : R -> R continuously differentiable,
       with y(0) >= 1  and  forall t, y'(t) <= -delta * (y(t) - 1),
     we have  forall t >= 0, y(t) <= 1 + (y(0) - 1) * exp (-delta * t).

   This is the linear Gronwall estimate used in Ricci-flow evolution
   estimates for scalar quantities whose ODE inequality has the form
     d/dt kappa <= -delta * kappa + (positive forcing collapsed to zero).
   It is *not* the full integral Gronwall
     omega(t) <= a + int_0^t b(s) omega(s) ds;
   it is the simpler compressible ODE variant.

   Decomposition strategy (2026-06-19):
   (1) gronwall_integrating_factor — the main ODE comparison Lemma,
       proved QED via one structural Axiom:
       * nonpos_deriv_noninc  (非正导数推论): if F'(s) <= 0 on [0,t], then
         F(t) <= F(0). This is a special case of the mean value theorem.
       Sub-lemmas now all QED with zero custom Axioms:
       - F_derivable (可微性)
       - F_deriv_nonpos (导数非正)
       - exp_strictly_positive
       - divide_inequality_by_positive
       - gronwall_div_is_exp_neg
   (2) All wrapping Lemmas end with Defined; only 1 structural Axiom remains. *)

Require Import Reals.
Require Import Ranalysis.
Require Import Lra.
Require Import Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.

Open Scope R_scope.

(* ===================================================================== *)
(* 1. Structural Axioms.                                                  *)
(* ===================================================================== *)

(* Axiom 1 (可微性) — Integrating factor is derivable and its derivative
   is <= 0 when y'(t) <= -delta*(y(t)-1).

   If y is differentiable at t and y'(t) <= -delta*(y(t)-1), then
   F(t) := (y(t)-1)*exp(delta*t) is also differentiable at t and
   F'(t) <= 0 (for any proof of derivability). This combines the
   product rule with the ODE inequality substitution. *)

(* Lemma 1a (可微性) — F := (y-1)*exp(delta*t) is derivable when y is.
   Proved via the Ranalysis library's product rule and chain rule. *)

Lemma F_derivable :
  forall (delta : R) (y : R -> R) (t : R) (pr : derivable_pt y t),
    delta > 0 ->
    derive_pt y t pr <= -delta * (y t - 1) ->
    derivable_pt (fun s => (y s - 1) * exp (delta * s)) t.
Proof.
  intros delta y t pr Hdelta Hineq.
  apply derivable_pt_mult.
  - (* (y - 1) is derivable at t *)
    apply derivable_pt_minus.
    + exact pr.
    + apply derivable_pt_const.
  - (* exp(delta * ·) is derivable at t (chain rule) *)
    apply derivable_pt_comp with (f1 := fun s => delta * s).
    + (* f1(s) = delta * s is derivable at t *)
      apply derivable_pt_scal with (f := id).
      apply derivable_pt_id.
    + (* exp is derivable at delta * t *)
      apply derivable_pt_exp.
Qed.

Lemma F_deriv_nonpos :
  forall (delta : R) (y : R -> R) (t : R) (pr : derivable_pt y t)
    (prF : derivable_pt (fun s => (y s - 1) * exp (delta * s)) t),
    delta > 0 ->
    derive_pt y t pr <= -delta * (y t - 1) ->
    derive_pt (fun s => (y s - 1) * exp (delta * s)) t prF <= 0.
Proof.
  intros delta y t pr prF Hdelta Hineq.
  set (F := fun s : R => (y s - 1) * exp (delta * s)).
  set (L := (derive_pt y t pr) * exp (delta * t) + (y t - 1) * (delta * exp (delta * t))).

  (* Use Rfun_scope notation for function-level operations *)
  pose (u := (y - (fct_cte 1))%F).
  pose (v := fun s : R => exp (delta * s)).
  assert (Hlim_u : derivable_pt_lim u t (derive_pt y t pr)).
  {
    unfold u.
    assert (H : derivable_pt_lim (y - (fct_cte 1))%F t (derive_pt y t pr - 0)).
    { apply (derivable_pt_lim_minus y (fct_cte 1) t (derive_pt y t pr) 0).
      - apply (derive_pt_eq_1 y t (derive_pt y t pr) pr). reflexivity.
      - apply (derivable_pt_lim_const 1 t).
    }
    (* Rminus_0_r: derive_pt y t pr - 0 = derive_pt y t pr *)
    rewrite Rminus_0_r in H.
    exact H.
  }

  assert (Hlim_v : derivable_pt_lim v t (delta * exp (delta * t))).
  {
    unfold v.
    assert (H_g_lim : derivable_pt_lim (fun s : R => delta * s) t delta).
    {
      assert (H_temp : derivable_pt_lim (mult_real_fct delta id) t (delta * 1)).
      { apply (derivable_pt_lim_scal id delta t 1). apply derivable_pt_lim_id. }
      (* unfold mult_real_fct and id, simplify *)
      unfold mult_real_fct, id in H_temp.
      rewrite Rmult_1_r in H_temp.
      exact H_temp.
    }
    assert (H : derivable_pt_lim (comp exp (fun s : R => delta * s)) t (exp (delta * t) * delta)).
    { apply (derivable_pt_lim_comp (fun s : R => delta * s) exp t delta (exp (delta * t))).
      - exact H_g_lim.
      - apply derivable_pt_lim_exp.
    }
    (* extensional: comp exp (fun s => delta * s) = (fun s => exp (delta * s)) *)
    assert (Heq : comp exp (fun s : R => delta * s) = (fun s : R => exp (delta * s))).
    { apply functional_extensionality; intro s; reflexivity. }
    rewrite Heq in H.
    (* commutativity: exp(delta*t)*delta = delta*exp(delta*t) *)
    rewrite Rmult_comm in H.
    exact H.
  }

  assert (Hlim_F : derivable_pt_lim F t L).
  {
    (* derivable_pt_lim_mult gives der.pt.lim (u * v) t L, where (u * v)%F = F *)
    assert (Hlim_mult : derivable_pt_lim (u * v)%F t L).
    {
      unfold L.
      apply (derivable_pt_lim_mult u v t (derive_pt y t pr) (delta * exp (delta * t))).
      - exact Hlim_u.
      - exact Hlim_v.
    }
    (* Show F = (u * v)%F extensionally *)
    assert (F_eq : F = (u * v)%F).
    {
      unfold F, u, v.
      apply functional_extensionality; intro s.
      unfold mult_fct, minus_fct, fct_cte; simpl.
      reflexivity.
    }
    rewrite F_eq; exact Hlim_mult.
  }

  (* Step 7: by derive_pt_eq_0, derive_pt F t prF = L *)
  assert (Hderive_eq : derive_pt F t prF = L).
  { apply (derive_pt_eq_0 F t L prF Hlim_F). }

  (* Step 8: show L <= 0 *)
  assert (HLpos : L <= 0).
  {
    assert (HL_eq : L = exp (delta * t) * (derive_pt y t pr + delta * (y t - 1))).
    { unfold L; ring. }
    rewrite HL_eq.
    replace (0) with (exp (delta * t) * 0) by ring.
    apply Rmult_le_compat_l.
    - left; apply exp_pos.
    - lra.
  }

  (* Step 9: conclude *)
  rewrite Hderive_eq.
  exact HLpos.
Qed.

(* Axiom 2 (非正导数推论) — Non-positive derivative implies non-increasing.
   If f'(s) <= 0 for all s in [a,b], then f(b) <= f(a).
   This is a direct consequence of the mean value theorem. *)

Axiom nonpos_deriv_noninc :
  forall (f : R -> R) (a b : R),
    a <= b ->
    (forall s : R, a <= s -> s <= b -> derivable_pt f s) ->
    (forall (s : R) (pr : derivable_pt f s), a <= s -> s <= b -> derive_pt f s pr <= 0) ->
    f b <= f a.

(* Lemma 3 — exp is strictly positive for every real argument.
   Proved via the Reals library's exp_pos. *)

Lemma exp_strictly_positive : forall t : R, 0 < exp t.
Proof.
  exact exp_pos.
Qed.

(* Lemma 4 — if 0 < c and a * c <= b then a <= b / c.
   Proved via Rmult_le_reg_r + Rinv_l (Coq 8.18 Reals library). *)

Lemma divide_inequality_by_positive :
  forall (a b c : R), 0 < c -> a * c <= b -> a <= b / c.
Proof.
  intros a b c Hcpos Hbound.
  apply Rmult_le_reg_r with (r := c).
  - exact Hcpos.
  - unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite Rinv_l; [ | apply Rgt_not_eq; exact Hcpos ].
    rewrite Rmult_1_r.
    exact Hbound.
Qed.

(* Lemma 5 — 1 / exp (delta * t) = exp (- delta * t).
   Proved via exp_plus + Rinv_l (Reals library). *)

Lemma gronwall_div_is_exp_neg :
  forall (delta t c : R),
    0 < exp (delta * t) ->
    c / exp (delta * t) = c * exp (- delta * t).
Proof.
  intros delta t c Hpos.
  unfold Rdiv.
  apply Rmult_eq_compat_l.
  apply Rmult_eq_reg_r with (r := exp (delta * t)).
  - rewrite Rinv_l; [ | apply Rgt_not_eq, Hpos ].
    rewrite <- exp_plus.
    replace (- delta * t + delta * t) with 0 by ring.
    rewrite exp_0.
    reflexivity.
  - apply Rgt_not_eq, Hpos.
Qed.

(* ===================================================================== *)
(* 2. Main Lemma — Integrating factor inequality (QED via Axioms 1+2).   *)
(* ===================================================================== *)

(* Given y differentiable and y'(s) <= -delta*(y(s)-1) for all s in [0,t],
   we have (y t - 1) * exp (delta * t) <= (y 0 - 1) for t >= 0.
   This is the ODE comparison principle, proved via Axioms 1+2. *)

Lemma gronwall_integrating_factor :
  forall (delta : R) (y : R -> R) (t : R),
    delta > 0 ->
    0 <= t ->
    y 0 >= 1 ->
    (* y differentiable everywhere: *)
    (forall s : R, derivable_pt y s) ->
    (* y'(s) <= -delta*(y(s)-1) for all s: *)
    (forall (s : R) (pr : derivable_pt y s), derive_pt y s pr <= -delta * (y s - 1)) ->
    (y t - 1) * exp (delta * t) <= (y 0 - 1).
Proof.
  intros delta y t Hdelta Htpos Hy0 Hyder Hyderineq.
  set (F := fun s : R => (y s - 1) * exp (delta * s)).

  (* Step A: F is derivable on [0,t] and F'(s) <= 0 *)
  assert (Fderiv : forall s : R, 0 <= s -> s <= t -> derivable_pt F s).
  { intros s Hs0 Hst.
    apply (F_derivable delta y s (Hyder s) Hdelta (Hyderineq s (Hyder s))).
  }

  assert (Fderivnonpos : forall (s : R) (pr : derivable_pt F s),
             0 <= s -> s <= t -> derive_pt F s pr <= 0).
  { intros s pr Hs0 Hst.
    apply (F_deriv_nonpos delta y s (Hyder s) pr Hdelta (Hyderineq s (Hyder s))).
  }

  (* Step B: F(t) <= F(0) by nonpos_deriv_noninc *)
  assert (HFbound : F t <= F 0).
  { apply (nonpos_deriv_noninc F 0 t Htpos Fderiv Fderivnonpos). }

  (* Step C: F 0 = (y 0 - 1) * exp (delta * 0) = y 0 - 1 *)
  unfold F in HFbound.
  assert (H0 : exp (delta * 0) = 1) by (rewrite Rmult_0_r, exp_0; reflexivity).
  rewrite H0 in HFbound.
  rewrite Rmult_1_r in HFbound.
  exact HFbound.
Defined.

(* ===================================================================== *)
(* 3. Main wrapping Theorem — Compressible ODE Gronwall (QED).           *)
(* ===================================================================== *)

Theorem gronwall_decay_via_substitution :
  forall (delta : R) (y : R -> R) (t : R),
    delta > 0 ->
    0 <= t ->
    y 0 >= 1 ->
    (* y differentiable everywhere: *)
    (forall s : R, derivable_pt y s) ->
    (* y'(s) <= -delta*(y(s)-1) for all s: *)
    (forall (s : R) (pr : derivable_pt y s), derive_pt y s pr <= -delta * (y s - 1)) ->
    y t <= 1 + (y 0 - 1) * exp (- delta * t).
Proof.
  intros delta y t Hdelta Htpos Hy0 Hyder Hyderineq.
  (* Step A: integrating-factor inequality. *)
  assert (Hbound : (y t - 1) * exp (delta * t) <= y 0 - 1).
  { apply (gronwall_integrating_factor delta y t Hdelta Htpos Hy0 Hyder Hyderineq). }
  (* Step B: exp(delta*t) > 0, so we can divide the inequality. *)
  assert (Hexp : 0 < exp (delta * t)).
  { apply exp_strictly_positive. }
  assert (Hdiv : y t - 1 <= (y 0 - 1) / exp (delta * t)).
  { apply (divide_inequality_by_positive (y t - 1) (y 0 - 1) (exp (delta * t)) Hexp Hbound). }
  (* Step C: rewrite (y 0 - 1) / exp (delta * t) as (y 0 - 1) * exp(-delta * t). *)
  assert (Hrew : (y 0 - 1) / exp (delta * t) = (y 0 - 1) * exp (- delta * t)).
  { apply (gronwall_div_is_exp_neg delta t (y 0 - 1) Hexp). }
  rewrite Hrew in Hdiv.
  (* Step D: lra *)
  lra.
Defined.

(* ===================================================================== *)
(* 4. Sanity-check exports.                                               *)
(* ===================================================================== *)
(* After compilation, run:
     Print Assumptions gronwall_decay_via_substitution.
   Expected dependencies:
     - F_derivable                  (Axiom 1a: 可微性 — differentiability)
     - F_deriv_nonpos               (Axiom 1b: 可微性 — derivative nonpos)
     - nonpos_deriv_noninc          (Axiom 2: 非正导数推论)
     - Reals (R_scope), Ranalysis, Classical_Prop
   The three ODE-free lemmas are QED with zero Axioms:
     - exp_strictly_positive
     - divide_inequality_by_positive
     - gronwall_div_is_exp_neg *)
(* ===================================================================== *)