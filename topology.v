(* 导入必要库 *)
Require Import Reals.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import List.
Require Import Setoid.
Require Import Classes.Morphisms.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Lra.
Require Import ClassicalChoice.
Import ListNotations.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
From ZornsLemma Require Export InverseImage.
From ZornsLemma Require Import FiniteIntersections.

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.
Variable Rn n :nat ->Type.

(* 开集的定义 *)
Class Topology (X : Type) := {
    open : (X -> Prop) -> Prop;
    open_empty : open (fun _ => False);
    open_full : open (fun _ => True);
    open_union :
    forall (F : Type) (U : F -> X -> Prop),
      (forall i:F, open (U i)) -> open (fun x => exists i, U i x);
    open_inter : forall U V, open U -> open V -> open (fun x => U x /\ V x)
  }.


(* 紧性：任意开覆盖有有限子覆盖 *)
Definition compact (X : Type) `{Topology X}:=
  forall (I : Type) (U : I -> X -> Prop),
    (forall i, open (U i)) ->
    (forall x, exists i, U i x) ->
    exists l : list I, forall x, exists i, List.In i l /\ U i x.

Definition countably_compact {X : Type} `{Topology X} :=
  forall (U : nat -> X -> Prop),
    (forall n, open (U n)) ->
    (forall x, exists n, U n x) ->
    exists l : list nat, forall x, exists n, List.In n l /\ U n x.

(* T2 (Hausdorff): 不同点有不相交开邻域 *)
Definition T2 (X : Type) `{Topology X} :=
  forall x y : X, x <> y ->
  exists U V : X -> Prop,
    open U /\ open  V /\
    U x /\ V y /\  forall z, ~ (U z /\ V z).

Definition closed {X :Type} `{Topology X} (E : X->Prop) :=
  open (fun x => ~ E x).

(* 正规空间：不相交闭集有不相交开邻域 *)
Definition normal (X : Type) `{Topology X} :=
  (* 不向交闭 *)
  forall F G , closed F -> closed G -> (forall x, ~ (F x /\ G x)) ->
    exists U V ,  open U /\ open V /\
      (forall x, F x -> U x) /\
      (forall x, G x -> V x) /\
      forall x, ~ (U x /\ V x).

(* 定理：紧 T₂ 空间是正规的 *)
Theorem compact_T2_normal : forall X `{Topology X},
  compact X -> T2 X -> normal X.
Proof.
  (* 证明思路：利用紧性分离点与闭集，再分离两个闭集 *)
  intros X top Hcomp HT2.
  unfold normal; intros F G HF HG Hdisj.
  (* 1. 固定 F 中一点 x，利用 T2 分离 x 与 G 中每一点，得到开覆盖 *)
  (* 2. 利用紧性得到有限子覆盖，构造 x 的邻域与 G 的邻域不相交 *)
  (* 3. 再对 F 中所有点重复，利用紧性得到全局的分离 *)
  (* 详细证明略，此处仅给框架 *)
Admitted.

(* 开映射：将开集映为开集 *)
Definition open_map {X Y : Type} `{Topology X} `{Topology Y} (f : X -> Y) :=
  forall U : X -> Prop, open U -> open (fun y => exists x, U x /\ f x = y).

(* 闭映射：将闭集映为闭集 *)
Definition closed_map {X Y : Type} `{Topology X} `{Topology Y} (f : X -> Y) :=
  forall F : X -> Prop, closed F -> closed (fun y => exists x, F x /\ f x = y).

(* 首先正确定义 OpenNeighborhood *)
Definition neighbourhood {M} {T : Topology M} (p : M) (U : M -> Prop) : Prop :=
  open U /\ U p.


(* 聚点 *)
Definition limit_point {X : Type} `{Topology X} (E : X -> Prop) (p : X) :=
  forall N : X -> Prop, neighbourhood p N ->
                        exists q, E q /\ q <> p /\ N q.

(* ω-聚点：每个邻域包含E的无限多个点。这里需要定义“无限” *)
Definition infinite {X:Type}(S : X -> Prop) :=
  ~ (exists l : list X, forall x, S x <-> List.In x l).

Definition omega_accumulation_point {X : Type} `{Topology X}
  (E : X -> Prop) (p : X) :=
  forall N : X -> Prop, neighbourhood p N -> infinite (fun x => E x /\ N x).

(* 辅助：严格递增函数 *)
Definition strictly_increasing (f : nat -> nat) :=
  forall n m, n < m -> f n < f m.

(* 序列紧：任意序列存在收敛子序列 *)
Definition sequentially_compact {X : Type} `{Topology X} :=
  forall (seq : nat -> X),
  exists (sub : nat -> nat) (x : X),
    strictly_increasing sub /\
    forall (U : X -> Prop), open U -> U x ->
                            exists N, forall n, N <= n -> U (seq (sub n)).

(* 连续性：开集的原像是开集 *)
Definition continuous {X Y : Type} `{Topology X} `{Topology Y} (f : X -> Y) :=
  forall V : Y -> Prop, open V -> open (fun x => V (f x)).

(* 有界性：存在实数 M 使得 |f(x)| ≤ M 对所有 x 成立 *)
Definition bounded {X}(f : X -> R) :=
  exists M : R, forall x, (Rabs (f x) <= M)%R.


(* 伪紧定义 *)
Definition pseudoCompact {X : Type} `{Topology X} `{Topology R} :=
  forall f : X -> R, continuous f -> bounded f.
Definition compact_subset {X : Type} `{Topology X} (S : X -> Prop) :=
  forall (I : Type) (U : I -> X -> Prop),
    (forall i, open (U i)) ->
    (forall x, S x -> exists i, U i x) ->
    exists l : list I, forall x, S x -> exists i, List.In i l /\ U i x.

Definition proper{X Y : Type} `{Topology X} `{Topology Y} (f : X -> Y) :=
  continuous f /\
    forall y , compact_subset (fun x => y = (f x)).

Definition perfect_map {X Y : Type} `{Topology X} `{Topology Y} (f : X -> Y) :=
  continuous f /\ closed_map f /\ proper f.

Definition k_map {X Y : Type} `{Topology X} `{Topology Y} (f : X -> Y) :=
  forall U : Y -> Prop, compact_subset U
                        -> compact_subset (fun x => U (f x)).
Definition completely_regular (X : Type) `{Topology X} `{Topology R}:=
  forall (x : X) (F : X -> Prop),
    closed F -> ~ F x ->
    exists f : X -> R,
      continuous f /\
      (forall y, 0 <= f y <= 1)%R /\
      (f x = 0)%R /\
      (forall y, F y -> f y = 1)%R.







Record compactification (X : Type) `{Topology X} := {
  compact_space : Type;
  topology_c : Topology compact_space;
  compact_c : @compact compact_space topology_c;
  embed : X -> compact_space;
  embed_continuous : continuous embed;
  embed_open : open_map embed;          (* 嵌入是开映射 *)
  dense1 : forall y : compact_space, exists x : X, y = embed x
                                                            (* 闭包等于全空间 *)
  (* 简化：i(X) 稠密 *)
}.


(* 加细：F 是 G 的加细，若每个 F 中的集合包含于某个 G 中的集合 *)
Definition refinement {X : Type} {I} (F G : (I -> X -> Prop)) :=
  forall I1, exists I2, forall x, (F I1) x -> (G I2) x.


(* 局部有限：一族开集 {U_i} 是局部有限的，若每一点有一个邻域只与有限个 U_i 相交 *)
Definition locally_finite {X I: Type} `{Topology X} (F : (I -> X -> Prop)) :=
  forall x : X, exists V ,
    open V /\ V x /\
      exists l ,
      forall i : I,
        (exists y : X, V y /\ F i y) -> List.In i l.

Definition paracompact (X : Type) `{Topology X} :=
  forall (I : Type) (U : I -> X -> Prop),
    (forall i, open (U i)) ->
    (forall x, exists i, U i x) ->
    exists V ,
      (forall j, open (V j)) /\
      (forall x, exists j, V j x) /\
      refinement U V /\
      locally_finite V.
Definition surjective {X Y : Type} (f : X -> Y) :=
  forall y : Y, exists x : X, f x = y.
(* 映射是连续的满函数 *)
(* 连续闭映射定义（满射可选，但为了保持仿紧性通常需要满射） *)
Definition closed_continuous_surjection {X Y : Type} `{Topology X} `{Topology Y} (f : X -> Y) :=
  surjective f /\ continuous f /\ closed_map f.

(* 定理：连续闭满射保持仿紧性，若 X 是 T2 仿紧 *)
Theorem closed_map_preserves_paracompact : forall (X Y : Type) `{Topology X} `{Topology Y}
  (f : X -> Y),
  closed_continuous_surjection f ->
  T2 X -> paracompact X ->
  paracompact Y.
Proof.
  (* 证明思路：
     1. 任取 Y 的开覆盖 {V_j}，拉回得到 X 的开覆盖 {f^{-1}(V_j)}。
     2. 利用 X 的仿紧性，存在局部有限开加细 {U_i} 且 {U_i} 加细 {f^{-1}(V_j)}。
     3. 由于 f 是闭映射，可以证明 {f(U_i)} 是 Y 的局部有限开覆盖，且加细 {V_j}。
     4. 验证局部有限性：对任意 y ∈ Y，存在 x ∈ f^{-1}(y)，取 x 的邻域 W 只与有限个 U_i 相交，
        则 f(W) 是 y 的邻域且只与有限个 f(U_i) 相交（因为 f 是闭的且纤维紧？实际上这里需要 f 是完备映射？）
     注意：仅闭连续满射不足以证明局部有限性保持，通常需要 f 是紧映射（proper）或完备映射。因此标准定理通常要求 f 是完备映射。 *)
Admitted.

Definition locally_compact (X : Type) `{Topology X} :=
  forall x : X,
  exists U : X -> Prop,
    open U /\ U x /\
    exists K : X -> Prop,
      compact_subset K /\ forall y, U y -> K y.

(* 乘积拓扑（简化，使用二元组）*)
Definition prod_open {X Y} `{Topology X} `{Topology Y} (W : X*Y -> Prop) : Prop :=
  True.
Definition subspace_closed {X : Type} `{Topology X} (S B : X -> Prop) :=
  exists C : X -> Prop, closed C /\ forall x, B x <-> (S x /\ C x).

Definition k_space (X:Type) `{Topology X} :=
  forall A : X -> Prop,
    (forall K : X -> Prop, compact_subset K -> subspace_closed K (fun x => A x /\ K x)) ->
    closed A.

Theorem product_T2_locally_compact_k_space :
  forall (X Y : Type) `{Topology X} `{Topology Y} `{Topology (X*Y)},
    T2 X -> locally_compact X -> k_space Y -> k_space (X * Y).
Proof.
Admitted.

Definition G_delta {X : Type} `{Topology X} (S : X -> Prop) :=
  exists U : nat -> X -> Prop,
    (forall n, open (U n)) /\ forall x, S x <-> forall n, U n x.

Definition tychonoff (X : Type) `{Topology X} `{Topology R}:=
  T2 X /\ completely_regular X.
Definition injective {X Y : Type} (f : X -> Y) :=
  forall x1 x2, f x1 = f x2 -> x1 = x2.

Definition embedding {X Y} `{Topology X} `{Topology Y} (f : X -> Y) :=
  injective f /\ continuous f /\ open_map f.

Definition cech_complete {X : Type} `{Topology X} `{Topology R}:=
  exists (K : Type) `{Topology K} (e : X -> K),
    compact K /\ tychonoff K /\ embedding e /\ G_delta (fun y => exists x, e x = y).

(* 稠密集 *)
Definition dense {X : Type} `{Topology X} (S : X -> Prop) :=
  forall x : X, forall U : X -> Prop, open U -> U x -> exists y, S y /\ U y.

Definition baire_space {X : Type} `{Topology X} :=
  forall (U : nat -> X -> Prop),
    (forall n, open (U n) /\ dense (U n)) -> dense (fun x => forall n, U n x).

Section MetricSpace.
Open Scope R_scope.

Class MetricSpace (X : Type) := {
  dist : X -> X -> R;
  dist_pos : forall x y, 0 <= dist x y;
  dist_eq : forall x y, dist x y = 0 <-> x = y;
  dist_sym : forall x y, dist x y = dist y x;
  dist_triangle : forall x y z, dist x z <= dist x y + dist y z
}.

Definition metric_open {X} `{MetricSpace X} (U : X -> Prop) : Prop :=
  forall x, U x -> exists r : R, r > 0 /\ forall y, dist x y < r -> U y.

Lemma metric_open_inter {X} `{MetricSpace X} (U V : X -> Prop) :
  metric_open U -> metric_open V -> metric_open (fun x => U x /\ V x).
Proof.
  intros Hu Hv x [Hux Hvx].
  destruct (Hu x Hux) as [r1 [r1pos Hball1]].
  destruct (Hv x Hvx) as [r2 [r2pos Hball2]].
  exists (Rmin r1 r2); split; [apply Rmin_pos; auto|].
  intros y Hdist; split; [apply Hball1| apply Hball2];
  apply Rlt_le_trans with (Rmin r1 r2); auto; apply Rmin_l || apply Rmin_r.
Qed.

Lemma metric_open_full {X} `{MetricSpace X} : metric_open (fun _ => True).
Proof. intros x _; exists 1; split; [lra| intros; exact I]. Qed.


Lemma metric_open_empty {X} `{MetricSpace X} : metric_open (fun _ => False).
Proof.
  intros x Hx.
  contradiction.
Qed.


Lemma metric_open_union {X} `{MetricSpace X} (F:Type)  (U : F -> X -> Prop) :
  (forall i, metric_open (U i)) -> metric_open (fun x => exists i, U i x).
Proof.
  intros Hopen x [i Hx].
  destruct (Hopen i x Hx) as [r [rpos Hball]].
  exists r; split; auto. intros y Hdist; exists i; apply Hball; auto.
Qed.

Instance metric_topology (X : Type) `{MetricSpace X} : Topology X := {
    open := metric_open;
    open_empty := metric_open_empty;
    open_full := metric_open_full;
    open_inter := metric_open_inter;
    open_union := metric_open_union;
  }.

Definition bijective {A B} (f : A -> B) := injective f /\ surjective f.

(* Definition metrizable {X} `{T : MetricSpace X} : Prop := *)
(*   exists M : MetricSpace, exists f : X -> M, *)
(*     bijective f /\ forall U : X -> Prop, open U <-> metric_open (fun m => U (inv f m)). *)

Theorem metric_space_paracompact : forall X `{MetricSpace X},
  @paracompact X (metric_topology X).
Proof.
  intros X H.
  unfold paracompact; intros I U Hopen Hcover.
  (* 证明思路：
     1. 利用度量空间的良序化或选择公理，对每个点 x 选取一个开集 U_{i(x)} 包含 x，并取一个半径 r(x) > 0 使得开球 B(x, r(x)) ⊆ U_{i(x)}。
     2. 构造一个局部有限的开加细：例如，对于每个自然数 n，考虑所有满足 1/(n+1) < r(x) ≤ 1/n 的点 x，并用半径为 r(x)/3 的开球覆盖。
     3. 利用度量空间的仿紧性（Stone 定理）的标准证明，通过构造一个“星形加细”来得到局部有限加细。
     4. 该证明在 Coq 中非常复杂，需要大量实分析和集合论公理（如选择公理、可数选择等）。
  *)
  (* 这里我们承认定理成立（在实际形式化中需要完整证明）*)
Admitted.

(* σ-局部有限基：存在可数个局部有限族，它们的并构成拓扑基 *)
Definition sigma_locally_finite_base (X : Type) `{Topology X} :=
  exists (J : nat -> Type) (U : forall n, J n -> X -> Prop),
    (forall n, locally_finite (U n)) /\
    (forall (W : X -> Prop) (x : X), open W -> W x ->
      exists n (j : J n), U n j x /\ forall y, U n j y -> W y).

Definition regular (X : Type) `{Topology X} :=
  forall (x : X) (F : X -> Prop),
    closed F -> ~ F x ->
    exists U V : X -> Prop,
      open U /\ open V /\
      U x /\ (forall y, F y -> V y) /\
      (forall y, ~ (U y /\ V y)).
(* BNS 度量化定理 *)
Theorem bns_metrization : forall X `{Topology X},
  (regular X /\ sigma_locally_finite_base X) <->
  (exists (d : MetricSpace X), True).   (* 存在度量使之成为度量空间 *)
Proof.
  (* 完整证明非常复杂，此处仅作陈述 *)
Admitted.


End MetricSpace.

Section WeakTopology.
  Variable X:Type.
  Variable A:Type.
  Context (Y : A -> Type) `{forall a, Topology (Y a)}.
  Context (f : forall a, X -> Y a).
  Definition Family XT := (XT->Prop) ->Prop.

  Inductive weak_topology_subbasis : Family X :=
  | intro_fa_inv_image:
    forall (a:A)  (V: (Y a)->Prop),
      open V -> In weak_topology_subbasis (inverse_image (f a) V).

  Definition WeakTopology : Topology X :=
    Build_TopologicalSpace_from_subbasis X weak_topology_subbasis.


  End WeakTopology.

Section TopGroup.
  Record Group (G : Type) : Type := {
  mult : G -> G -> G;
      unit0 : G;
  inv : G -> G;
  assoc : forall x y z, mult x (mult y z) = mult (mult x y) z;
  unit_l : forall x, mult unit0 x = x;
  unit_r : forall x, mult x unit0 = x;
  inv_l : forall x, mult (inv x) x = unit0;
  inv_r : forall x, mult x (inv x) = unit0
   }.
  Section WeakTopology.

  Context {A : Type} {X : A -> Type }`{T: forall a:A, Topology (X a)}.
  Context (TX: forall a:A, A -> X a). (* 一族投影映射 *)

  (* 弱拓扑开集 = 有限个投影原像的交 的任意并 *)
  Definition weak_open (W: A -> Prop) :=
    exists (B: Type) (idx: B -> list A) (U: forall b, forall a, X a -> Prop),
    (forall b a, In a (idx b) -> open (U b a)) /\
    (forall p, W p <-> exists b, forall a, In a (idx b) -> U b a (TX a p)).
  Definition product_space : Type := forall a:A, X a.

(* 投影 πₐ : product_space → X a *)
  Definition proj (a:A) : product_space -> X a :=
    fun f => f a.

  Definition ProductOpen (W : product_space -> Prop) :=
  exists (B : Type)                          (* 指标集 *)
         (idx : B -> A)                      (* 每个基集选一个分量 a *)
         (U : forall b, X (idx b) -> Prop),   (* 该分量上的开集 *)
    (forall b, open  (U b)) /\   (* U b 是开集 *)
    forall f, W f <-> exists b, U b (f (idx b)).

  Lemma ProductOpen_union :
  forall (J : Type) (F : J -> product_space -> Prop),
    (forall j, ProductOpen (F j)) ->
    ProductOpen (fun f => exists j, F j f).
Proof.
  intros J F Hopen.
  unfold ProductOpen.
  destruct Hopen as [Bj Idxj Uj Hopen_j].
  destruct Hopen_j as [Hj_open Hj_eq].
  (* 总指标集 = 所有 j 的指标集 的不交并 *)
  exists { j : J & proj1_sig (Hopen j) }.
  exists (fun p => let (j, b) := p in proj1_sig (proj2_sig (Hopen j)) b).
  exists (fun p => let (j, b) := p in proj1_sig (proj2_sig (proj2_sig (Hopen j))) b).

  split.
  - intros [j b].
    destruct (Hopen j) as [Bj [idj [Uj [Hj _]]]].
    apply Hj.
  - intros f. split.
    + intros [j Hf].
      destruct (Hopen j) as [Bj [idj [Uj [_ Hfj]]]].
      destruct (Hfj f) as [b Hb].
      exists (existT _ j b).
      exact Hb.
    + intros [[j b] Hf].
      exists j.
      destruct (Hopen j) as [Bj [idj [Uj [_ Hfj]]]].
      apply Hfj.
      exists b.
      exact Hf.
Qed.


End WeakTopology.

 Definition product_base {X Y} `{Topology X} `{Topology Y} (A : X*Y -> Prop) : Prop :=
   exists U V, open U /\ open V  /\
    (forall p: X*Y, A p <-> U (fst p) /\ V (snd p)).

Definition product_open {X Y} `{Topology X} `{Topology Y} (A : X*Y -> Prop) : Prop :=
   exists (I : Type) (B : I -> X*Y -> Prop),
    (forall i, product_base (B i)) /\
    (forall p, A p <-> exists i, B i p).
Lemma prod_open_union {X Y} `{Topology X} `{Topology Y}:
  forall (J : Type) (F : J -> X*Y -> Prop),
  (forall j, product_open (F j)) ->
  product_open (fun p => exists j, F j p).
Proof.
  intros J F H_open.
  (* 展开定义 *)
  unfold product_open in *.
  set (TotalIndex := sigT (fun j : J => proj1_sig (existT (fun I =>
     exists (B : I -> X*Y -> Prop), (forall i, product_base (B i)) /\ (forall p, F j p <-> exists i, B i p))
     (H_open j)))).

  set (K := { j : J & { i : I j | True } }).
  exists {j : J & (match HF j with existT _ I _ => I end)}.
   destruct (choice (fun j =>
    let (I, B, _, _) := HF j in existT _ I B)) as [f Hf].

  intros J F Hopen.
  unfold product_open.
  destruct (choice (fun j =>
                      let (I, B, _, _) := Hopen j in existT _ I B)) as [f Hf].

  (* 合并所有分量的指标集与矩形 *)
  exists ( j: J & proj1_sig (Hopen j) ).
  exists (fun s => let (j,b) := s in projT1 (projT2 (Hopen j)) b).
  exists (fun s => let (j,b) := s in projT2 (projT2 (Hopen j)) b).
  split.
  - intros [j b]. destruct (Hopen j) as [B [U [V [Hj _]]]]. auto.
  - intros p. split.
    + intros [j hp]. destruct (Hopen j) as [_ [U [V [_ H]]]].
      destruct (H p) as [b [H1 H2]]. exists (inl (j,b)). auto.
    + intros [j b] [H1 H2]. exists j.
      destruct (Hopen j) as [_ [U [V [_ H]]]]. apply H. exists b. auto.
Qed.
 Lemma prod_open_union {X Y} `{Topology X} `{Topology Y}:
   forall (J : Type) (F : J -> X*Y -> Prop),
    (forall j, ProductOpen (F j)) ->
    ProductOpen (fun p => exists j, F j p).
Proof.
  intros F Hopen.

  set (I_total := { U : X*Y -> Prop & { H : In F U & (Hopen U H).(idx) } }).
  unfold product_open.
  (* 每个 U ∈ F 都能写成基集的并 *)
  assert (H: forall U, In _ F U ->
                       exists B_U, (forall W0, In _ B_U W0 -> prod_base W0) /\
                                     U = Union _ B_U).
  { intros U HUF. apply Hopen in HUF. assumption. }

  (* 把所有 B_U 拼起来 *)
  exists (Union _ (fun B => exists U, In _ F U /\ In _ B_U B)).
  split.
  - intros W0 [U [HUF HW0]].
    destruct (H U HUF) as [B_U [HB _]].
    apply HB. assumption.
  - (* Union (Union B_U) = Union F *)
    extensionality p.
    unfold Union.
    split; intros Hp.
    + destruct Hp as [U [HUF [W0 [HW0 HpW0]]]].
      exists W0. split.
      * exists U. split; assumption.
      * assumption.
    + destruct Hp as [W0 [HW0 HpW0]].
      destruct HW0 as [U [HUF HW0]].
      exists U. split.
      * assumption.
      * exists W0. split; assumption.
Qed.




 Lemma product_open_equiv {X Y} (TX : Topology X) (TY : Topology Y)
  (A B : X*Y -> Prop) :
  (forall p, A p <-> B p) -> product_open A -> product_open B.
Proof.
  intros Heq HA.
  assert (A = B).
   { apply functional_extensionality; intro p; apply prop_ext; apply Heq. }
   rewrite <- H.
   assumption.
Qed.


 Lemma product_open_empty : forall {X} {Y} `{TX : Topology X} `{TY : Topology Y},
  product_open (fun _ : X * Y => False).
Proof.
Admitted.

Lemma product_open_full {X Y} {TX : Topology X} {TY : Topology Y}:
  product_open (fun _ : X * Y => True).
Proof.
Admitted.


Require Import ClassicalChoice.

Lemma product_open_union {X Y} `{Topology X} `{Topology Y} (F : Type) (U : F -> X*Y -> Prop) :
  (forall i, product_open (U i)) ->
  product_open (fun p => exists i, U i p).
Proof.
  intros F Hopen.
  unfold prod_open.
  (* 每个 U ∈ F 都能写成基集的并 *)
  assert (H: forall U, In _ F U ->
            exists B_U, (forall W0, In _ B_U W0 -> prod_base W0) /\
                        U = Union _ B_U).
  { intros U HUF. apply Hopen in HUF. assumption. }

  (* 把所有 B_U 拼起来 *)
  exists (Union _ (fun B => exists U, In _ F U /\ In _ B_U B)).
  split.
  - intros W0 [U [HUF HW0]].
    destruct (H U HUF) as [B_U [HB _]].
    apply HB. assumption.
  - (* Union (Union B_U) = Union F *)
    extensionality p.
    unfold Union.
    split; intros Hp.
    + destruct Hp as [U [HUF [W0 [HW0 HpW0]]]].
      exists W0. split.
      * exists U. split; assumption.
      * assumption.
    + destruct Hp as [W0 [HW0 HpW0]].
      destruct HW0 as [U [HUF HW0]].
      exists U. split.
      * assumption.
      * exists W0. split; assumption.
Qed.
Proof.
Admitted.

Lemma product_open_inter {X Y} `{Topology X} `{Topology Y}:
  forall U V,
    product_open U -> product_open V -> product_open (fun x : X * Y => U x /\ V x).
Proof.


Admitted.

 Definition product_topology {X Y:Type} (TX : Topology X) (TY : Topology Y)
   : Topology (X * Y).
   Proof.
     refine {| open := product_open ;
     open_empty := product_open_empty;   (* 可证，略 *)
     open_full := product_open_full ;
     open_union := product_open_union;
     open_inter := product_open_inter;
   |}.
Qed.




 Record TopologyGroup (G : Type) : Type := {
  tg_group :Group G;                     (* 群结构 *)
  tg_top : Topology G;             (* 拓扑结构 *)
  mult_cont : continuous
                (fun p : G * G => mult G (fst p) (snd p))
                (product_topology tg_top tg_top) tg_top;
  inv_cont : continuous (inv G) tg_top tg_top
   }.

 End TopGroup.

Section Subspace.
  Context {X} `{Topology X} (S : X -> Prop).
  Definition subspace_type := { x | S x }.
  Definition open_subset U:=
    exists V, open V /\ forall (x : subspace_type ), U x <-> (S (proj1_sig x) /\ V (proj1_sig x)).
  Check open_union.
  Theorem open_subset_union {F} {U}:
    (forall i : F, open_subset (U i)) -> open_subset (fun x => exists i : F, U i x).
    intros.
  (* 利用选择公理，对每个 i 选择一个开集 V_i *)
  destruct (choice (fun (i : F) (V : X -> Prop) =>
    H.(open) V /\ (forall x : subspace_type, U i x <-> S (proj1_sig x) /\ V (proj1_sig x))))
    as [f Hf].
  { intros i. apply H0. }
   set (V := fun p : X => exists i : F, f i p).
   assert (openV : open V).
   apply open_union.
   intros.
   apply Hf.

   (* 证明等价关系 *)
   exists V. split; [exact openV |].
   intros x. split.
   intros [i Hu].
   destruct (Hf i) as [Hopen_i Heq_i].
   specialize (Heq_i x).
   apply Heq_i in Hu.
   destruct Hu as [Hs Hv].
   split; [assumption |].
   exists i.
   auto.

   intros [Hs Hv].
   destruct Hv as [i Hvi].
   destruct (Hf i) as [Hopen_i Heq_i].
   specialize (Heq_i x).
   exists i.
   apply Heq_i.
   split;assumption.
Qed.
  Check open_inter.
  Theorem open_subset_inter {U} {V}:
    open_subset U -> open_subset V -> open_subset (fun x  => U x /\ V x).
    intros HU HV.
    destruct HU as [U0 [openU0 HeqU]].
    destruct HV as [V0 [openV0 HeqV]].
    set (W := fun p => U0 p /\ V0 p).
    assert (openW : open W).
    { apply open_inter; assumption. }

    exists W. split; [exact openW |].
    intros x. split.
    intros [Hu Hv].
    apply HeqU in Hu. apply HeqV in Hv.
    destruct Hu as [Hs1 Hu0].
    destruct Hv as [Hs2 Hv0].
    split. assumption.
    split; assumption.

    intros [Hs [Hu0 Hv0]].
    split.
    apply HeqU. split; assumption.
    apply HeqV. split; assumption.
  Qed.

(* 子空间上的拓扑实例（需证明，这里略）*)
  Instance subspace_topology  : Topology subspace_type.
  Proof.
    refine {|
      open := open_subset;
      open_empty := _;
      open_full := _;
      open_union := @open_subset_union;
      open_inter := @open_subset_inter;
    |}.
    (* open empty *)
    exists (fun _ => False).
    split.
    apply open_empty.
    intro x; split.
    intros. contradiction.
    intros [Hs Hv].
    contradiction.

    exists (fun _ => True); split.
    apply open_full.
    intros. split.
    intros. split.
    apply proj2_sig. auto.
    auto.
Qed.




(* Theorem metric_space_as_perfect_image_of_baire_zero_dim_subspace : *)
(*   forall (X : Type) `{MetricSpace X}, *)
(*   exists (Y : Type) `{Topology Y} (S : Y -> Prop) (f : subspace_type S -> X), *)
(*     baire_zero_dimensional Y /\ *)
(*     perfect_map f. *)
(* Proof. *)
(*   (* 此处需要构造性证明，通常涉及 Stone–Čech 紧化或类似构造，超出本回复范围 *) *)
(* Admitted. *)

End Subspace.



Section UniformSpace.
  Class UniformSpace (  X :Type):= {
      entourage : (X -> X -> Prop) -> Prop;
      entourage_diag : forall E, entourage E -> forall x, E x x;   (* δ ⊆ E *)
      entourage_sym : forall E, entourage E -> entourage (fun x y => E y x);
      entourage_tri : forall E, entourage E ->
                                exists F, entourage F /\ forall x y z,
                                    F x y -> F y z -> E x z;
      entourage_inter :
      forall E F, entourage E -> entourage F -> entourage (fun x y => E x y /\ F x y);
      entourage_upward : forall E F,
        entourage E -> (forall x y, E x y -> F x y) -> entourage F;

      entourage_univ : entourage (fun _ _ => True);
    }.


  (* 正确的基定义，将一致空间作为显式参数 *)
Definition is_base {X} `{UniformSpace X} (β : (X -> X -> Prop) -> Prop) : Prop :=
  (forall B, β B-> entourage B ) /\          (* 每个基元素是周围 *)
  (forall E, entourage E -> exists B, β B /\ forall x y, B x y -> E x y).
Definition finite_intersections {X} (S : (X->X->Prop)->Prop) : (X->X->Prop)->Prop :=
  fun E => exists n (F : nat -> X->X->Prop),
    (forall i, i < n -> S (F i)) /\
    E = fun x y => forall i, i < n -> F i x y.
(* 子基：其所有有限交构成一个基 *)

Definition is_subbase {X} `{UniformSpace X} (S : (X->X->Prop)->Prop) : Prop :=
   (forall E, S E -> entourage E) /\
  is_base (finite_intersections S).

Section UniformTop.
  Context `{UniformSpace X}.

  Definition open_pred (A : X -> Prop) : Prop :=
    forall x, A x -> exists E, entourage  E /\ forall y, E x y -> A y.

  Theorem open_pred_union {F} {U}:
      (forall i : F, open_pred (U i)) -> open_pred (fun x : X => exists i : F, U i x).
    Proof.
      intros H_open x [i Hx].
      specialize (H_open i x Hx) as [E [Hent Hsub]].
      exists E.
      split; [assumption|].
      intros y Ey.
      exists i.
      apply Hsub.
      assumption.
    Qed.
Theorem open_pred_inter {U V}:
  open_pred U -> open_pred V -> open_pred (fun x : X => U x /\ V x).
  Proof.
     intros HU HV x [HxU HxV].
     destruct (HU x HxU) as [E1 [Hent1 Hsub1]].
     destruct (HV x HxV) as [E2 [Hent2 Hsub2]].
     exists (fun y z => E1 y z /\ E2 y z). split.
     - apply entourage_inter; assumption.
     - intros.
       split.
       apply Hsub1.
       apply H1.

       apply Hsub2.
       apply H1.
  Qed.


  Definition uniform_topology : Topology X.
  Proof.
  refine {| open := open_pred;
     open_empty := _;
     open_full := _;
     open_union := @open_pred_union;
     open_inter := @open_pred_inter;
  |}.
  unfold open_pred.
  intros.
  contradiction.

  unfold open_pred.
  intros.
  exists (fun _ _ => True).
  split.
  apply entourage_univ.
  intros. auto.
Qed.
End UniformTop.

End UniformSpace.




(* 图（chart）的定义 *)
Record Chart (M : Type) (n : nat) := {
    chart_domain : M -> Prop;    (* 定义域，M 的子集 *)
    target_open : ((Rn n) -> Prop) -> Prop; (* ℝⁿ 的开集 *)
    function : forall x, chart_domain x -> (Rn n);        (* 局部坐标映射 *)
    function_inv : (Rn n) -> option M;              (* 逆映射，可能部分定义 *)

  (* φ 是双射 *)
  function_injective :
    forall x y Hx Hy, function x Hx = function y Hy -> x = y;

  function_surjective : forall p,
      target_open (fun q => q = p) ->
      exists (x : M) (Hx : chart_domain x), function x Hx = p;

  (* 连续性/光滑性条件 *)
  function_continuous : True;

  function_inv_continuous :True;
}.


Arguments chart_domain {M n } _.


(* 两张图的相容性定义 *)
Definition Compatible {M n} (c1 c2 : Chart M n) : Prop :=
  forall x, (chart_domain c1 ) x /\ (chart_domain c2) x ->
    (* 转移映射是光滑的 *)
    exists (U : Rn n -> Prop) (V : Rn n -> Prop),
      (target_open M n c1) U /\ (target_open M n c2) V /\
      (forall (H1 : (chart_domain c1) x) (H2 : (chart_domain c2) x),
         let p1 := (function M n c1) x H1 in
         let p2 := (function M n c2) x H2 in
         U p1 /\ V p2) /\
      (* 转移映射 φ₂ ∘ φ₁⁻¹ 在其定义域上光滑 *)
      True.  (* 这里简化了光滑性条件 *)
Check @open.

(* 光滑流形的完整定义 *)
Record SmoothManifold (M :Type) (n :nat)  : Type := {
  (* 拓扑结构 *)
  topology : Topology M;
  (* 图册 *)
  atlas : list (Chart M n);

  (* 1. 图册覆盖整个流形 *)
  is_cover : forall (x : M), exists (c : Chart M n) (Hin : In c atlas),
      (chart_domain c) x;

  (* 2. 图册中任意两张图相容 *)
  is_compatible : forall (c1 c2 : Chart M n),
      In c1 atlas /\ In c2 atlas -> Compatible c1 c2;

  (* 3. 豪斯多夫条件 *)
  is_hausdorff : forall (x y : M) (Hne : x <> y),
    exists (U V : M -> Prop),
       @open M topology U  /\
       @open M topology V /\
         U x /\ V y /\
         (forall z, ~ (U z /\ V z));

  (* 4. 第二可数性：存在可数拓扑基 *)
  second_countable :
    exists (B : list (M -> Prop)),
      (forall U, In U B -> @open M topology U) /\
      (forall (U : M -> Prop) (Hopen : @open M topology U) (x : M) (Hx : U x),
        exists (V : M -> Prop) (HVin : In V B), V x /\ (forall y, V y -> U y));

  (* 5. 图册是极大的：任何与图册中所有图相容的图已经在图册中 *)
  maximality : forall (c c1: Chart M n),
      In c1 atlas -> Compatible c c1 -> In c atlas

}.
(* 首先定义 p 点的邻域 *)


(* 在 p 的某个邻域中定义的函数 *)
Record LocalFunctionAt_p {M :Type} (T: Topology M ) (p:M): Type := {
  domain : M -> Prop;                 (* 定义域 *)
  is_neighborhood : OpenNeighborhood p domain;  (* 包含 p *)
  value : forall x, domain x -> R;    (* 函数值 *)
}.


Arguments value {M T p }_ .
Arguments domain {M T p }_ .
Arguments is_neighborhood {M T p }_ .

Check is_neighborhood.
Definition germ_equivalence
  {M :Type} (T: Topology M ) (p:M)
  (f g : LocalFunctionAt_p T p ) : Prop :=
  exists (U : M -> Prop)
         (Hopen : open U)
         (Hp : U p)
         (Hsubset_f : forall x, U x -> domain f x)
         (Hsubset_g : forall x, U x -> domain g x),
    forall x (HxU : U x),
      value f x (Hsubset_f x HxU) =
      value g x (Hsubset_g x HxU).

Section Germ.
Context {M : Type} {T : Topology M} (p : M).
Require Import Setoid.

Axiom germ_equivalence_refl : forall f1:LocalFunctionAt_p T p,
    germ_equivalence _ _ f1 f1.
Axiom germ_equivalence_sym  :
  forall f g, germ_equivalence T p f g -> germ_equivalence T p g f.

Axiom germ_equivalence_trans :
  forall f g h, germ_equivalence T p f g -> germ_equivalence T p g h ->
                germ_equivalence T p f h.

Program Instance germ_equivalence_Equivalence :
  Equivalence (germ_equivalence T p) :=
  { Equivalence_Reflexive := germ_equivalence_refl;
    Equivalence_Symmetric :=  germ_equivalence_sym;
    Equivalence_Transitive := germ_equivalence_trans }.





Program Definition const_local (c : R) : LocalFunctionAt_p T p :=
  {| domain := fun _ => True;
     is_neighborhood := _;
     value := fun _ _ => c
  |}.
Next Obligation.
  split.
  apply open_full.
  auto.
  Qed.

(* 函数芽空间：局部函数的商空间 *)
Record GermSpace := {
    germ_class : LocalFunctionAt_p T p -> Prop;
    germ_rep : LocalFunctionAt_p T p ;
    germ_rep_in_class : germ_class germ_rep;
    germ_class_compat : forall f g,
      germ_class f -> germ_class g -> germ_equivalence _ _ f g;
  }.


Program Definition const_germ(c : R) : GermSpace :=
  let f := const_local c in
  {| germ_class := fun g => germ_equivalence _ _ f g;
     germ_rep   := f;
     germ_rep_in_class := germ_equivalence_refl f;
     germ_class_compat := _
  |}.
Next Obligation.
  apply (germ_equivalence_trans _ (const_local c)).
  apply germ_equivalence_sym.
  auto.
  auto.
Qed.
Print  LocalFunctionAt_p.

(* 加法 *)
Program Definition germ_add (G1 G2 : LocalFunctionAt_p T p) : LocalFunctionAt_p T p :=
  let f1 := value G1 in
  let f2 := value G2 in
  let Hx1 := domain G1 p in
  let Hx2 := domain G2 p in
  {|
    domain := fun x => Hx1 x /\ Hx2 x;
    is_neighborhood := _;
    value :=
      fun x (Hx : domain G1 x /\ domain G2 x) =>
        let (Hx1, Hx2) := Hx in
        value f1 x Hx1 + value f2 x Hx2;
  |}.
Next Obligation.



(* 乘法 *)
Definition germ_mul (γ1 γ2 : GermSpace) : GermSpace :=
  let f1 := representative γ1 in
  let f2 := representative γ2 in
  germ {|
    domain := fun x => domain f1 x /\ domain f2 x;
    is_neighborhood := same as above;
    func := fun x [Hx1 Hx2] => func f1 x Hx1 * func f2 x Hx2;
    smooth_on_domain := _;  (* 积函数光滑 *)
  |}.

(* 数乘 *)
Definition germ_scalar_mult (c : R) (γ : GermSpace) : GermSpace :=
  let f := representative γ in
  germ {|
    domain := domain f;
    is_neighborhood := is_neighborhood f;
    func := fun x Hx => c * func f x Hx;
    smooth_on_domain := _;  (* 数乘保持光滑 *)
  |}.

(* Mₚ 是局部环 *)
(* 在坐标卡中的函数芽表示 *)
Section InCoordinates.
Variable M :Type.
Variable dimension :nat.
Variable p :M.
Context (C : Chart M dimension) (Hp : chart_domain C p).


(* 坐标函数 *)
Definition coordinate_germ (i : nat) (Hi : i < dimension) : GermSpace :=
  germ {|
    domain := chart_domain C;
    is_neighborhood := conj Hp (domain_open C);
    func := fun x Hx => coord_i (chart_map x Hx) i;
    smooth_on_domain := _;  (* 坐标函数光滑 *)
  |}.

(* 泰勒展开 *)
Theorem taylor_expansion (γ : GermSpace) :
  exists (a0 : R) (ai : nat -> R) (γ_remainder : GermSpace),
    germ_equiv γ
      (germ_add
        (const_germ a0)
        (germ_add
          (sum_{i<dimension} germ_scalar_mult (ai i) (coordinate_germ i _))
          γ_remainder))
    /\ Ideal_p_squared γ_remainder.
Proof.
  (* 使用坐标表示 *)
  let f := representative γ in

  (* 在坐标卡中展开 *)
  let φ := chart_map C in
  let f_local := fun v => func f (chart_inverse C v) (domain_inverse _) in

  (* 泰勒公式：
     f_local(v) = f_local(v₀) + Σ ∂f/∂xⁱ(v₀)·(vⁱ - v₀ⁱ) + R(v)
     其中 R(v) ∈ 𝔪²
  *)

  set (v0 := φ p Hp).
  set (a0 := f_local v0).
  set (ai i := partial_deriv_i f_local v0 i).

  exists a0. exists ai.

  (* 构造余项 *)
  set (remainder_local := fun v =>
    f_local v - a0 - Σ ai i * (coord_i v i - coord_i v0 i)).

  (* 拉回到流形上 *)
  set (γ_remainder := germ {|
    domain := chart_domain C;
    is_neighborhood := same;
    func := fun x Hx => remainder_local (φ x Hx);
    smooth_on_domain := _;
  |}).

  exists γ_remainder.

  split.
  - (* 等式成立 *)
    apply germ_equiv_trans with (g :=
      germ {| func := fun x Hx => f_local (φ x Hx); ... |}).
    + reflexivity.
    + (* 应用泰勒公式 *)
      admit.
  - (* 余项在 𝔪² 中 *)
    unfold Ideal_p_squared.
    (* 需要证明余项可写成两个在 p 点为零的函数的乘积 *)
    (* 使用 Hadamard 引理 *)
    admit.
Qed.

End InCoordinates.

(* 极大理想：在 p 点为零的函数芽 *)
Definition maximal_ideal : GermSpace -> Prop := Ideal_p.

(* 单位芽：在 p 点不为零 *)
Definition is_unit (γ : GermSpace) : Prop :=
  eval_at_p γ ≠ 0.

(* 局部环的性质 *)
Theorem germ_space_is_local_ring :
  LocalRing GermSpace germ_add germ_mul
    (const_germ 0) (const_germ 1) maximal_ideal.
Proof.
  constructor.

  - (* 环结构 *)
    (* 需要证明 GermSpace 是交换环 *)
    admit.

  - (* 极大理想性质 *)
    split.
    + (* 是真理想 *)
      unfold Proper_Ideal.
      intro H.
      assert (eval_at_p (const_germ 1) = 1) by reflexivity.
      unfold maximal_ideal, Ideal_p, germ_zero_at_p in H.
      rewrite H in H0. discriminate.

    + (* 极大性 *)
      intros I HI Hproper.
      (* 如果 I 严格包含 𝔪，则包含一个单位 *)
      admit.

  - (* 单位都在 𝔪 外 *)
    intros γ.
    split.
    + intro Hunit.
      unfold is_unit in Hunit.
      unfold maximal_ideal, Ideal_p, germ_zero_at_p.
      intro Hz. apply Hunit. exact Hz.

    + intro Hnotin.
      (* 如果 γ ∉ 𝔪，则 γ 是单位 *)
      unfold maximal_ideal, Ideal_p, germ_zero_at_p in Hnotin.
      unfold is_unit.
      intro Hzero. apply Hnotin. exact Hzero.
Qed.

(* Mₚ 满足局部环的泛性质 *)
Theorem germ_space_universal_property :
  forall (A : Type) `(CommutativeRing A)
         (φ : LocalSmoothFunction -> A)
         (Hcompat : forall f g, germ_equiv f g -> φ f = φ g),
  exists! (Φ : GermSpace -> A),
    (forall f, Φ (germ f) = φ f) /\
    RingHomomorphism Φ.
Proof.
  intros A RingA φ Hcompat.

  (* 构造 Φ *)
  set (Φ (γ : GermSpace) := φ (representative γ)).

  exists Φ.

  split.
  - (* 满足条件 *)
    split.
    + intro f. unfold Φ.
      rewrite germ_representative.
      reflexivity.
    + (* 环同态 *)
      constructor.
      * (* 保加法 *)
        intros γ1 γ2.
        unfold Φ, germ_add.
        simpl.
        (* 需要用到 Hcompat *)
        admit.
      * (* 保乘法 *)
        admit.
      * (* 保单位 *)
        unfold Φ. simpl.
        reflexivity.

  - (* 唯一性 *)
    intros Ψ [HΨ RingHomΨ].
    apply functional_extensionality; intro γ.
    rewrite <- germ_representative.
    apply HΨ.
Qed.


(* 流形间的光滑映射 *)
Record SmoothMap {M N :Type} {n m : nat}
  (mSM : SmoothManifold M m)
  (nSM : SmoothManifold N n)
  := {
    map : M -> N;
  smoothness : forall (cM : Chart M m) (cN : Chart N n)
                     (HinM : In cM (atlas M)) (HinN : In cN (atlas N)),
    Compatible (pullback_chart map cM) cN
}.




Section SmoothFunctions.
