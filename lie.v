
Require Import Reals.
Class VectorSpace (V : Type) := {
  vadd : V -> V -> V;
  vzero : V;
  vneg : V -> V;
  smul : R -> V -> V;
    vzero_add : forall x , vadd vzero x = x;
    vzero_smul : forall x , smul x vzero  = vzero;
}.


Class Bilinear (V : Type)
  (add : V -> V -> V) (mul : R -> V -> V) (op : V -> V -> V) : Prop := {
  bilinear_add_l : forall x y z, op (add x y) z = add (op x z) (op y z);
  bilinear_add_r : forall x y z, op z (add x y) = add (op z x) (op z y);
  bilinear_scal_l : forall (c : R) (x y : V), op (mul c x) y = mul c (op x y);
  bilinear_scal_r : forall (c : R) (x y : V), op x (mul c y) = mul c (op x y)
}.

Class LieAlgebra ( V : Type) := {
    bracket : V -> V -> V;
    add : V -> V ->V;
    mul : R -> V ->V;
    zero : V;
    l1 : Bilinear V add mul bracket;
    l2 : forall x , bracket x x = zero;
    l3 : forall x y z, add (bracket x (bracket y z) )
                         (add (bracket y (bracket  z x))
                            (bracket z (bracket x y))) = zero;
  }.

Definition isomorphic{X}{Y}`{LieAlgebra X}`{LieAlgebra Y} (f : X ->Y):=
  forall x y, f (bracket x y ) = bracket (f x ) (f y).

Definition IsSubLieAlgebra {L} `{LieAlgebra L} (H : L -> Prop) : Prop :=
  (* 包含零元 *)
  H zero /\
  (* 对加法和标量乘法封闭，即是一个子空间 *)
  (forall x y, H x -> H y -> H (add x  y)) /\
  (forall a x, H x -> H (mul a  x)) /\
  (* 对李括号封闭 *)
  (forall x y, H x -> H y -> H (bracket x y)).
Section EndV_LieAlgebra.
  Variable (V : Type).
  Context `(VectorSpace V).   (* V 是 R 上的向量空间 *)

  (** 定义线性映射 End(V) *)
  Record LinearMap : Type := {
    fmap : V -> V;
    is_linear :
      forall (a b : R) (x y : V),
        fmap (vadd (smul a x) (smul b  y)) =
          vadd (smul a  (fmap x))
            (smul b (fmap y))
  }.
  Definition lm_zero : LinearMap.
    Proof.
  refine
    {| fmap := fun _ => vzero;
      is_linear := _;
    |}.
  intros.
  simpl.
  assert ((smul a vzero)= vzero).
  apply vzero_smul.
  assert ((smul b vzero)= vzero).
  apply vzero_smul.
  rewrite H0.
  rewrite H1.
  assert (vadd vzero vzero = vzero).
  apply vzero_add.
  rewrite H2.
  reflexivity.
Qed.




(* End(V) 上的加法和标量乘法（逐点定义） *)
Definition lm_add (f g : LinearMap) : LinearMap.
  Proof.
    refine
      {| fmap := fun v => vadd (fmap f v)  (fmap g v);
        is_linear := _;
      |}.
    intros.
    rewrite (is_linear f a b x y).
    rewrite (is_linear g a b x y).





Definition lm_neg (f : LinearMap) : LinearMap :=
  {| fmap := fun v => - (fmap f v);
    is_linear := (* 利用 f 的线性 *)
      fun a b x y =>
        rewrite (is_linear f a b x y);
    rewrite !vneg_add_distr, !scalar_mul_neg; reflexivity
  |}.

Definition lm_scalar_mul (c : R) (f : LinearMap) : LinearMap :=
  {| fmap := fun v => c *: fmap f v;
    is_linear := fun a b x y =>
                   rewrite (is_linear f a b x y);
    (* 标量乘法的线性 *)
    rewrite !scalar_mul_add_distr, !scalar_mul_assoc; reflexivity
  |}.
 #[local] Instance EndV_LieAlgebra : LieAlgebra R LinearMap :=
  {| bracket := lbracket;
     bracket_linear_l := lbracket_linear_l;
     bracket_linear_r := lbracket_linear_r;
     bracket_anti := lbracket_anti;
     bracket_jacobi := lbracket_jacobi
  |}.

End EndV_LieAlgebra.
