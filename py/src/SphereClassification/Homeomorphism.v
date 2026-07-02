(* Homeomorphism.v *)
(* Bridge module: basic lemmas about IsHomeomorphic (reflexivity, symmetry, transitivity) *)

From SphereClassification Require Import Topology.

Open Scope R_scope.

(* ===================================================================== *)
(* 1. IsHomeomorphic reflexivity                                        *)
(* ===================================================================== *)

Lemma isHomeomorphic_refl :
  forall (X : Type) (T : Toplogy X),
    @IsHomeomorphic X X T T.
Proof.
  intros X T.
  refine (mkIsHomeomorphic _ _ _ _ (fun x => x) (fun x => x) _ _).
  - (* homeo_cont: identity is continuous *)
    unfold Continuous.
    intros V Hopen.
    exact Hopen.
  - (* homeo_inv_cont: identity is continuous *)
    unfold Continuous.
    intros V Hopen.
    exact Hopen.
Qed.

(* ===================================================================== *)
(* 2. IsHomeomorphic symmetry                                          *)
(* ===================================================================== *)

Lemma isHomeomorphic_sym :
  forall (X Y : Type) (T : Toplogy X) (S : Toplogy Y),
    @IsHomeomorphic X Y T S ->
    @IsHomeomorphic Y X S T.
Proof.
  intros X Y T S H.
  destruct H as [f g Hcont Hinvcont].
  refine (mkIsHomeomorphic _ _ _ _ g f _ _).
  - exact Hinvcont.
  - exact Hcont.
Qed.

(* ===================================================================== *)
(* 3. IsHomeomorphic transitivity                                      *)
(* ===================================================================== *)

Lemma isHomeomorphic_trans :
  forall (X Y Z : Type) (T : Toplogy X) (S : Toplogy Y) (U : Toplogy Z),
    @IsHomeomorphic X Y T S ->
    @IsHomeomorphic Y Z S U ->
    @IsHomeomorphic X Z T U.
Proof.
  intros X Y Z T S U H1 H2.
  destruct H1 as [f fg Hcont1 Hinvcont1].
  destruct H2 as [g gh Hcont2 Hinvcont2].
  refine (mkIsHomeomorphic _ _ _ _ (fun x => g (f x)) (fun z => fg (gh z)) _ _).
  - (* (g o f) is continuous X -> Z *)
    unfold Continuous.
    intros V Hopen.
    (* g is continuous Y -> Z, so isOpen (fun y => V (g y)) *)
    assert (Hmid : @isOpen Y S (fun y => V (g y))).
    { apply Hcont2. exact Hopen. }
    (* f is continuous X -> Y: Hcont1 : forall (V' : Y -> Prop), isOpen Y S V' -> isOpen X T (fun x => V' (f x)) *)
    (* Apply Hcont1 to the predicate (fun y => V (g y)) and the proof Hmid *)
    exact (Hcont1 (fun y => V (g y)) Hmid).
  - (* (fg o gh) is continuous Z -> X *)
    unfold Continuous.
    intros V Hopen.
    (* fg is continuous Y -> X, so isOpen (fun y => V (fg y)) *)
    assert (Hmid : @isOpen Y S (fun y => V (fg y))).
    { apply Hinvcont1. exact Hopen. }
    (* gh is continuous Z -> Y: Hinvcont2 : forall (V' : Y -> Prop), isOpen Y S V' -> isOpen Z U (fun z => V' (gh z)) *)
    exact (Hinvcont2 (fun y => V (fg y)) Hmid).
Qed.

(* ===================================================================== *)
(* 4. IsHomeomorphic equivalence relation                              *)
(* ===================================================================== *)

(* IsHomeomorphic is an equivalence relation on (Type, Toplogy) pairs.
   Reflexivity: isHomeomorphic_refl
   Symmetry: isHomeomorphic_sym
   Transitivity: isHomeomorphic_trans *)

(* ===================================================================== *)
(* 5. Homeomorphism composition                                        *)
(* ===================================================================== *)

Definition compose_homeo {X Y Z : Type} {T : Toplogy X} {S : Toplogy Y} {U : Toplogy Z}
  (H1 : @IsHomeomorphic X Y T S) (H2 : @IsHomeomorphic Y Z S U) :
  @IsHomeomorphic X Z T U.
Proof.
  apply (isHomeomorphic_trans X Y Z T S U). exact H1. exact H2.
Defined.

(* ===================================================================== *)
(* 6. Homeomorphism from identity                                      *)
(* ===================================================================== *)

Definition id_homeo {X : Type} {T : Toplogy X} :
  @IsHomeomorphic X X T T.
Proof.
  exact (isHomeomorphic_refl X T).
Defined.

(* ===================================================================== *)
(* 7. Homeomorphism from inverse                                       *)
(* ===================================================================== *)

Definition inv_homeo {X Y : Type} {T : Toplogy X} {S : Toplogy Y}
  (H : @IsHomeomorphic X Y T S) :
  @IsHomeomorphic Y X S T.
Proof.
  apply (isHomeomorphic_sym X Y T S). exact H.
Defined.