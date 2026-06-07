
(* 在文件开头导入 MathComp *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import Reals.
Open Scope R_scope.

(* 导入实数和分析 *)
From Coq Require Import Reals.Reals.
From Coq Require Import Classical.

Class VectorSpace := {
    v_base : Type;
    v_add : v_base -> v_base -> v_base;
    v_smul : R -> v_base -> v_base
  }.

Class NormalVectorSpace :={
    base : Type;
    zero : base;
    ms : R -> base -> base;
    p : base -> R;
    add : base -> base -> base;
    p1 : forall x , p x >=0;
    p2 : forall x, p x = 0 -> x = zero;
    p3 : forall a x , p (ms a x) = a * (p x);
    p4 : forall x y , p (add x  y) <=   p x  + p y ;
  }.

Class MetricSpace :={
    V :Type;
    d : V -> V -> R;
    d1 : forall x y, d x y >= 0;
    d2 : forall x y, d x y = d y x;
    d3 : forall x y z , d x z <=  d x y + d y z;
}.

Class LimitSeq (l_space : MetricSpace):={
    cd1 := l_space.(d);
    seq1 : nat -> l_space.(V);
    x0 : l_space.(V);
    c2 :
    forall e , e>0 ->
     exists N, forall n :nat , (n >= N)%nat  ->
       d (seq1 n) x0 < e;
  }.

Class CauchSeq (m_space : MetricSpace):={
    cd := m_space.(d);
    seq : nat -> m_space.(V);
    c1 :
    forall e , e>0 ->
     exists N, forall n m :nat , (n >= N)%nat /\ (m >= N)%nat ->
       d (seq n) (seq m) < e;
  }.

Definition Complete (M : MetricSpace) : Prop :=
  forall (cauchy : CauchSeq M ),
    exists (L : LimitSeq M ),
      forall n, L.(seq1) n = cauchy.(seq) n.

Variable norm_induced_metric : NormalVectorSpace -> MetricSpace.
Class BanachSpace := {
    N_space : NormalVectorSpace;
    c : Complete (norm_induced_metric N_space)
  }.
Class LinearOperator := {
    X: VectorSpace;
    Y: VectorSpace;
    T : X.(v_base) -> Y.(v_base);
    l1 : forall x y , T (X.(v_add) x  y) = Y.(v_add) (T x) (T y);
    l2 : forall a x , T (X.(v_smul) a x)  = Y.(v_smul) a (T x);
  }.

Class HibertSpace := {
    h_base : Type;
    h_zero : h_base;
    h_add : h_base -> h_base -> h_base;
    h_smul : R -> h_base -> h_base;
    h_op : h_base -> h_base -> R;
    h_conj : R -> R;
    h1 : forall a b x z y ,
      h_op (h_add (h_smul a x) (h_smul b y)) z =
        (a *(h_op x z))  +  (b * (h_op y z));

    h2 : forall a b x z y ,
      h_op  z (h_add (h_smul a x) (h_smul b y)) =
        (h_conj a) *(h_op  z x)  +  (h_conj b) * (h_op z y);
    h3 : forall x, h_op x x >=0;
    h4 : forall x , h_op x x = 0 -> x = h_zero;
  }.




Class BoundedLinearOperator := {
    b_X : Type;
    b_Y : Type;
    b_op : b_X -> b_Y;
    X_op : b_X -> R;
    Y_op : b_Y -> R;
    op_bound : exists M : R, M > 0 /\ forall x,  Y_op (b_op x) <= M * (X_op x)
}.

Variable H2S : HibertSpace -> VectorSpace.

Class ConjOpertaor :={
    c_X : Type;
    c_Y : Type;
    c_op_Y : c_Y -> c_Y -> R;
    c_op_X : c_X -> c_X -> R;
    c_T : c_X -> c_Y;
    c_S : c_Y -> c_X;

    con2 :
     forall x y ,
       c_op_Y (c_T x) y =
         c_op_X  x (c_S y)

  }.
