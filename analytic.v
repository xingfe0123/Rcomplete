
Require Import Reals.
Require Import Derive.
Require Import Rfunctions.
Require Import Ranalysis.
Require Import Coq.Reals.RiemannInt.
Open Scope R_scope.

Definition C1_on (f : R -> R) (a b : R) :=
  exists deriv : R -> R,                           (* 导数函数 *)
  forall x, a <= x <= b -> continuity_pt deriv x
  /\ forall x, a < x < b -> derivable_pt_lim f x (deriv x)
.

Definition R2 := (R * R)%type.
Definition dist2 (p q : R2) : R :=
  let (x1, y1) := p in
  let (x2, y2) := q in
  sqrt ((x1 - x2)^2 + (y1 - y2)^2).


Definition continuity_pt_P2 (f : R -> R2) (x : R) : Prop :=
  continuity_pt (fun t => fst (f t)) x
  /\ continuity_pt (fun t => fst (f t)) x .

Definition continuity_P2 (f : R -> R2) : Prop :=
  forall x, continuity_pt_P2 f x.

Definition continuity_pt_R2 (f : R2 -> R) (p0 : R2) : Prop :=
  forall eps : R, eps > 0 ->
    exists delta : R, delta > 0 /\
      forall p : R2, dist2 p p0 < delta -> Rabs (f p - f p0) < eps.

Definition path_connected (U : R2 -> Prop) : Prop :=
  forall a b : R2, U a -> U b ->
    exists (f : R -> R2),
      (forall t, 0 <= t <= 1 -> U (f t)) /\
      continuity_P2 f /\
      f 0 = a /\ f 1 = b.

Definition ball (c : R2) (r : R) : R2 -> Prop :=
  fun p :R2 => dist2 p c < r.

Definition is_open (U : R2 -> Prop) : Prop :=
  forall p : R2, U p ->
    exists r : R, r > 0 /\ forall q, ball p r q -> U q.

Definition open_cover (U A B : R2 -> Prop) : Prop :=
  is_open A /\
  is_open B /\
  (forall p, U p -> A p \/ B p) /\
  (exists p, U p /\ A p) /\
  (exists p, U p /\ B p).

Definition is_connected (U : R2 -> Prop) : Prop :=
  forall A B : R2 -> Prop,
    is_open A -> is_open B ->
    (forall p, U p -> A p \/ B p) ->          (* U ⊆ A ∪ B *)
    (exists p, U p /\ A p /\ ~ B p) ->        (* A 在 U 中非空 *)
    (exists p, U p /\ B p /\ ~ A p) ->        (* B 在 U 中非空 *)
    (exists p, U p /\ A p /\ B p) -> False.


Definition  path_C1_on (y : R -> R2) (a b : R) :=
  (C1_on (fun t => fst (y t)) a b)/\
    (C1_on (fun t => snd (y t)) a b).

(* Definition path_deriv {y : R -> R2} {a b : R} *)
(*   (p : path_C1_on y a b) : R -> R2 := *)
(*   fun t => (deriv _  _ _ p.(y1c) t, *)
(*              deriv _ _ _ p.(y2c) t). *)

Definition
  piecewise_C1 (y : R -> R2) (a b : R) :=
  exists (pn : nat) (pt:nat ->R),
    pt 0%nat = a /\
      pt pn = b /\
      (forall i, (i < pn)%nat -> pt i < pt (S i)) /\
      (forall i, (i < pn)%nat -> path_C1_on y (pt i) (pt (S i )))
  .
Definition path_connected_C1 (U : R2 -> Prop) : Prop :=
  forall a b : R2, U a -> U b ->
    exists (f : R -> R2),
      (forall t, 0 <= t <= 1 -> U (f t)) /\
      continuity_P2 f /\
      piecewise_C1 f 0 1 /\
      f 0 = a /\ f 1 = b.


Definition close_path (y : R -> R2) (a b : R) :=
    piecewise_C1 y a b /\ a = b.



Class  OneForm (D : R2 -> Prop) := {
    coeff_dx : R2 -> R;
    coeff_dy : R2 -> R;
    smooth1 : forall x , D x -> continuity_pt_R2 coeff_dx x;
    smooth2 : forall x , D x -> continuity_pt_R2 coeff_dy x;
  }.


Theorem connected_open_C1_path_connected :
  forall U : R2 -> Prop,
    is_connected U -> is_open U  -> path_connected_C1 U.
  Proof.
    intros.



Lemma continuous_implies_integrable :
  forall (f : R -> R) (a b : R),
    ( a < b) ->
    (forall t : R, a <= t <= b -> continuity_pt f t) ->
    Riemann_integrable f a b.
Proof.
  intros f a b Hcont.
  (* 1. 应用 RiemannInt_P6 引理 *)
  apply RiemannInt_P6.
  exact Hcont.
Qed.



Program Definition line_integral_1form
        (D : R2 -> Prop) (w : OneForm D)
        (y : R -> R2)
        (a b : R)
        (H : a < b)
        (y_path : path_C1_on y a b)
        (y_in_D : forall t, a <= t <= b -> D (y t))
  : R :=
  let y' t := (y1_deriv_lim t, y2_deriv_lim t) in   (* 注意：deriv_lim 是导数函数 *)
  let integrand t :=
    let (x, y) := y t in
    let (dx, dy) := y' t in
    coeff_dx w (x, y) * dx + coeff_dy w (x, y) * dy
  in
  RiemannInt integrand a b _.
Next Obligation.
Proof.
  (* 此时环境中有：
     D, w, Y, Y', a, b, H, Y_cont, Y'_cont, P_cont, Q_cont, Y_in_D
     需要证明 Riemann_integrable integrand a b *)
  apply RiemannInt_P6.   (* 该引理: forall f a b, a < b -> (forall x, a<=x<=b -> continuity_pt f x) -> Riemann_integrable f a b *)
  - exact H.            (* a < b *)
  - intros t Ht.
    (* 现在需要证明 continuity_pt integrand t *)
    unfold integrand.
    (* 利用连续性假设构造证明，略去详细步骤，可以逐步应用 continuity_pt_mult, continuity_pt_plus 等 *)
    admit.  (* 这里可以填充完整证明，或者暂时用 admit 占位 *)
Qed.
