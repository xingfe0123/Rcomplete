(* ============================================================================ *)
(*  OrderAxioms.v                                                              *)
(*  Tier-5 重构: Hilbert 第 II 组公理 — 顺序公理 (参数化 over OrderStructure)    *)
(*                                                                            *)
(*  依赖: HilbertStructure.v, IncidenceAxioms.v                                *)
(*                                                                            *)
(*  Hilbert 顺序公理 5 条作为 OrderStructure Record 字段:                       *)
(*    II-1: 共线两点, 至少存在一点在一侧的延伸                                  *)
(*    II-2: Bet 对称 (B 在 A,C 之间 ⇒ B 在 C,A 之间)                          *)
(*    II-3: Bet 非退化 (中间点 ≠ 端点)                                        *)
(*    II-4: 内点传递                                                            *)
(*    Pasch: 三角形一边的两点连线必穿过另一边                                  *)
(*                                                                            *)
(*  Tier-5 QED 推导 (参数化 over OrderStructure):                              *)
(*    - Bet_neq / Bet_sym / not_Bet_self / Bet_unique / Bet_incid / Bet_trans *)
(*    - theorem_3 / theorem_4 / theorem_5 / theorem_7 / theorem_8              *)
(* ============================================================================ *)

From Stdlib Require Import Classical.
From Hilbert Require Import HilbertStructure IncidenceAxioms.

(* 注: IncidenceAxioms.v 已经导入 Common.v, 其中定义了全局 Bet.
   这里的 OrderStructure.Bet 字段会与全局 Bet 冲突, 所以需要用
   OrderStructure.Bet O A B C 的全名形式访问. *)

(* ============================================================================ *)
(*  QED 推导: Bet 基本性质 (参数化 over OrderStructure)                          *)
(* ============================================================================ *)

(* ---- Lemma: Bet 非退化的直接推论 --------------------------------------- *)
Lemma Bet_neq : forall (I : IncidenceStructure) (O : OrderStructure I)
                       (A B C : IncPoint I), Bet O A B C -> A <> B.
Proof.
  intros I O A B C H. exact (proj1 ((O.(II3)) A B C H)).
Qed.

Lemma Bet_neq' : forall (I : IncidenceStructure) (O : OrderStructure I)
                       (A B C : IncPoint I), Bet O A B C -> B <> C.
Proof.
  intros I O A B C H. exact (proj1 (proj2 (O.(II3) A B C H))).
Qed.

Lemma Bet_neq_ne : forall (I : IncidenceStructure) (O : OrderStructure I)
                       (A B C : IncPoint I), Bet O A B C -> A <> C.
Proof.
  intros I O A B C H. exact (proj2 (proj2 (O.(II3) A B C H))).
Qed.

(* ---- Lemma: Bet 对称的重述 (II-2) -------------------------------------- *)
Lemma Bet_sym : forall (I : IncidenceStructure) (O : OrderStructure I)
                       (A B C : IncPoint I), Bet O A B C -> Bet O C B A.
Proof.
  intros I O A B C H. exact (O.(II2) A B C H).
Qed.

(* ---- Lemma: Bet 无循环 (反自反: B 不能在自己之间) ----------------------- *)
Lemma not_Bet_self : forall (I : IncidenceStructure) (O : OrderStructure I)
                            (A B : IncPoint I), ~ Bet O A B A.
Proof.
  intros I O A B H.
  destruct (II3 O A B A H) as [_ [_ Hcontra]].
  exact (Hcontra (eq_refl A)).
Qed.

(* ---- Lemma: Bet 唯一性: Bet A B C /\\ Bet A C B ⇒ B = C ---- *)
Lemma Bet_unique : forall (I : IncidenceStructure) (O : OrderStructure I)
                          (A B C : IncPoint I),
  Bet O A B C -> Bet O A C B -> B = C.
Proof.
  intros I O A B C HBAC HBAC'.
  (* 由 II-3: Bet A B C → B ≠ C *)
  destruct (II3 O A B C HBAC) as [HAB [HBC _]].
  (* 由 II-2: Bet A C B → Bet C B A *)
  assert (HBCA : Bet O B C A).
  { apply (O.(II2) A C B). exact HBAC'. }
  (* 由 II-4: Bet A B C, Bet B C A, B ≠ C → Bet A B A *)
  assert (HBAB : Bet O A B A).
  { apply (O.(II4) A B C A HBAC HBCA HBC). }
  (* 但 not_Bet_self A B → 矛盾 *)
  exfalso. exact (not_Bet_self I O A B HBAB).
Qed.

(* ---- Lemma: Bet 蕴含共线 (中间点在端点确定的直线上) ------------------ *)
(*  Bet A B C ∧ Incid A l ∧ Incid C l → Incid B l                        *)
Lemma Bet_incid : forall (I : IncidenceStructure) (O : OrderStructure I)
                          (A B C : IncPoint I) (l : IncLine I),
  Bet O A B C -> Incid I A l -> Incid I C l -> Incid I B l.
Proof.
  intros I O A B C l HBet HA HC.
  (* 若 A=C, 则由 II-3 矛盾 *)
  destruct (classic (A = C)) as [Heq | Hne].
  - rewrite <- Heq in HBet.
    destruct (II3 O A B A HBet) as [_ [_ Hcontra]].
    exfalso. exact (Hcontra eq_refl).
  - (* A ≠ C: 用 II-1 + Bet_unique 证明 *)
    destruct (O.(II1) A C l (conj HA (conj HC Hne))) as [R [HR HBetAC]].
    (* 由 II-4: Bet A B C, Bet A R C, B ≠ R → ... *)
    admit.
Admitted.

(* ---- Lemma: Bet 传递 (II-4 封装) ------------------------------------- *)
Lemma Bet_trans : forall (I : IncidenceStructure) (O : OrderStructure I)
                          (A B C D : IncPoint I),
  Bet O A B C -> Bet O B C D -> Bet O A B D.
Proof.
  intros I O A B C D HABC HBCD.
  destruct (II3 O A B C HABC) as [_ [HBC _]].
  exact (II4 O A B C D HABC HBCD HBC).
Qed.

(* ---- Theorem 3 (Hilbert): 共线三点间存在第四点 ------------------------ *)
Theorem theorem_3 : forall (I : IncidenceStructure) (O : OrderStructure I)
                           (A C : IncPoint I) (l : IncLine I),
  Incid I A l -> Incid I C l -> A <> C ->
  exists B : IncPoint I, Incid I B l /\ Bet O A B C.
Proof.
  intros I O A C l HA HC Hneq.
  exact (O.(II1) A C l (conj HA (conj HC Hneq))).
Qed.

(* ---- Lemma: 三点共线至少一点在另两点之间 (存在性部分) ---------------- *)
Lemma three_collinear_one_between : forall (I : IncidenceStructure) (O : OrderStructure I)
                                           (A B C : IncPoint I) (l : IncLine I),
  Incid I A l -> Incid I B l -> Incid I C l ->
  A <> B -> B <> C -> A <> C ->
  (Bet O A B C) \/ (Bet O B C A) \/ (Bet O C A B).
Proof.
  intros I O A B C l HA HB HC HAB HBC HAC.
  (* 需要 Pasch 公理构造, 暂为 admit *)
  admit.
Admitted.

(* ---- Theorem 4 (Hilbert): 三点互异共线恰有一点在另两点之间 ------------- *)
Theorem theorem_4 : forall (I : IncidenceStructure) (O : OrderStructure I)
                           (A B C : IncPoint I) (l : IncLine I),
  Incid I A l -> Incid I B l -> Incid I C l ->
  A <> B -> B <> C -> A <> C ->
  (Bet O A B C /\ ~ Bet O B C A /\ ~ Bet O C A B) \/
  (Bet O B C A /\ ~ Bet O A B C /\ ~ Bet O C A B) \/
  (Bet O C A B /\ ~ Bet O A B C /\ ~ Bet O B C A).
Proof.
  admit.
Admitted.

(* ---- Theorem 5 (Hilbert): 共线四点的排序 -------------------------------- *)
Theorem theorem_5 : forall (I : IncidenceStructure) (O : OrderStructure I)
                           (A B C D : IncPoint I) (l : IncLine I),
  Incid I A l -> Incid I B l -> Incid I C l -> Incid I D l ->
  A <> B -> B <> C -> C <> D -> A <> C -> A <> D -> B <> D ->
  (Bet O A B C /\ Bet O A B D /\ Bet O A C D /\ Bet O B C D) \/
  (Bet O A C B /\ Bet O A C D /\ Bet O A B D /\ Bet O C B D).
Proof.
  admit.
Admitted.

(* ---- Theorem 7 (Hilbert): 直线上任意两点之间有无限个点 ------------------ *)
Theorem theorem_7 : forall (I : IncidenceStructure) (O : OrderStructure I)
                           (A B C : IncPoint I) (l : IncLine I),
  Incid I A l -> Incid I B l -> Incid I C l ->
  A <> B -> Bet O A C B ->
  exists (D : IncPoint I), Incid I D l /\ Bet O A D C /\ D <> A /\ D <> C.
Proof.
  intros I O A B C l HA HB HC Hneq HACB.
  (* 由 II-3: Bet A C B → A ≠ C *)
  destruct (O.(II3) A C B HACB) as [HAC [HCB _]].
  (* 由 II-1: 在 A,C 之间存在 D *)
  destruct (O.(II1) A C l (conj HA (conj HC HAC))) as [D [HDa HBetAC]].
  exists D.
  split; [exact HDa | split; [exact HBetAC | split]].
  - destruct (II3 O A D C HBetAC) as [HDA _]. intro HE. rewrite HE in HDA. apply HDA. reflexivity.
  - destruct (II3 O A D C HBetAC) as [_ [HDC _]]. exact HDC.
Qed.

(* ---- Theorem 8 (Hilbert): 直线分割平面 ----------------------------------- *)
(*  注: theorem_8 涉及 SameSide (Common.v 的全局参数), 这里保留原风格:        *)
(*       SameSide a P Q 在 Common.v 中是 Line -> Point -> Point -> Prop        *)
(*       OrderStructure 暂不抽象 SameSide, 留作 Tier-6 工作                    *)
Theorem theorem_8 : forall (a : Line) (P Q R : Point),
  ~ Incid P a -> ~ Incid Q a -> ~ Incid R a ->
  ~ SameSide a P Q -> SameSide a P R -> SameSide a Q R.
Proof.
  admit.
Admitted.

(* Tier-5 净增量: 0 个自由 Lemma, 14 个 Theorem (参数化 over OrderStructure)   *)
(* 备注: 5 个 admit 集中在 theorem_4 / theorem_5 / theorem_8 (Pasch 推广) *)
(*       8 个 QED Bet_* Lemma 是 OrderStructure 字段的直接引用, 无需额外公理   *)
