

From Stdlib Require Import Classical.
From Hilbert Require Import Common HilbertStructure.

(* ============================================================================ *)
(*  辅助定义: 直线 l 在平面 alpha 内 (在 Record 实例上下文)                     *)
(* ============================================================================ *)

Definition LineInPlane (I : IncidenceStructure) (l : IncLine I) (alpha : IncPlane I) : Prop :=
  forall X : IncPoint I, Incid I X l -> IncidPlane I X alpha.

(* ---- Theorem 1a: 平面上两直线要么唯一交一点, 要么无交点 -------------------- *)
(* Hilbert 定理 1 (第一部分):                                                   *)
(* 同一平面上的两条不同直线, 要么有唯一公共点, 要么无公共点。                    *)
(* 证明: 若有两不同公共点 ⇒ I-2 说两直线重合, 矛盾.                             *)
Theorem theorem_1a : forall (I : IncidenceStructure) (a b : IncLine I) (alpha : IncPlane I),
  LineInPlane I a alpha -> LineInPlane I b alpha -> a <> b ->
  (exists! P : IncPoint I, Incid I P a /\ Incid I P b) \/
  (~ exists P : IncPoint I, Incid I P a /\ Incid I P b).
Proof.
  intros I a b alpha Ha Hb Hneq.
  destruct (classic (exists P : IncPoint I, Incid I P a /\ Incid I P b)) as [Hinter | Hno].
  - left. destruct Hinter as [P [HPa HPb]].
    exists P. split.
    + exact (conj HPa HPb).
    + intros Q [HQa HQb].
      destruct (classic (P = Q)) as [Heq | Hne].
      * exact Heq.
      * exfalso. apply Hneq.
        apply (I2 I a b P Q (conj HPa (conj HQa (conj HPb HQb)))).

  - right. exact Hno.
Qed.

(* ---- Theorem 1b: 两平面要么有公共直线, 要么无公共点 ------------------------ *)
(* Hilbert 定理 1 (第二部分):                                                   *)
(* 两平面 α, β 若有一公共点, 则必有公共直线。                                 *)
(* 证明: 若 ∃P∈α∩β, I-7 给 Q∈α∩β 且 Q≠P.                                     *)
(*       I-1 给过 P,Q 的直线 l. I-5 推 l⊂α 且 l⊂β.                            *)
Theorem theorem_1b : forall (I : IncidenceStructure) (alpha beta : IncPlane I),
  (exists P : IncPoint I, IncidPlane I P alpha /\ IncidPlane I P beta) ->
  exists l : IncLine I, LineInPlane I l alpha /\ LineInPlane I l beta.
Proof.
  intros I alpha beta [P [HPalpha HPbeta]].
  destruct (I7 I alpha beta P (conj HPalpha HPbeta)) as [Q [HQalpha [HQbeta Hneq]]].
  destruct (I1 I P Q) as [l [HPl HQl]].
  assert (HlInAlpha : LineInPlane I l alpha).
  { unfold LineInPlane. intros X HX.
    apply (I5 I l alpha P Q HPl HQl HPalpha HQalpha X HX). }
  assert (HlInBeta : LineInPlane I l beta).
  { unfold LineInPlane. intros X HX.
    apply (I5 I l beta P Q HPl HQl HPbeta HQbeta X HX). }
  exact (ex_intro _ l (conj HlInAlpha HlInBeta)).
Qed.

(* ---- Theorem 1c: 平面和不在其上的直线, 要么唯一交一点, 要么无公共点 -------- *)
(* Hilbert 定理 1 (第三部分):                                                   *)
(* 若直线 a 不全在平面 α 内, 则要么有唯一公共点, 要么无公共点。                 *)
(* 证明: 若有两不同公共点 ⇒ I-5 推 a 全在 α 内, 矛盾.                         *)
Theorem theorem_1c : forall (I : IncidenceStructure) (a : IncLine I) (alpha : IncPlane I),
  ~ LineInPlane I a alpha ->
  (exists! P : IncPoint I, Incid I P a /\ IncidPlane I P alpha) \/
  (~ exists P : IncPoint I, Incid I P a /\ IncidPlane I P alpha).
Proof.
  intros I a alpha HnotIn.
  destruct (classic (exists P : IncPoint I, Incid I P a /\ IncidPlane I P alpha)) as [Hinter | Hno].
  - left. destruct Hinter as [P [HPa HPalpha]].
    exists P. split.
    + exact (conj HPa HPalpha).
    + intros Q [HQa HQalpha].
      destruct (classic (P = Q)) as [Heq | Hne].
      * exact Heq.
      * exfalso. apply HnotIn. unfold LineInPlane. intros X HX.
          apply (I5 I a alpha P Q HPa HQa HPalpha HQalpha X HX).
  - right. exact Hno.
Qed.

(* ---- Theorem 2a: 过一直线和不在这直线上的一点, 有且只有一个平面 ------------ *)
(* Hilbert 定理 2 (第一部分):                                                  *)
(* 给定直线 l 和不在 l 上的点 P, 存在唯一平面 α 包含 l 和 P.                   *)
(* 证明:                                                                      *)
(*   - 存在: I-3 取 A,B∈l; A,B,P 不共线; I-4 给 α=A,B,P; I-5 推 l⊂α           *)
(*   - 唯一: 任何含 l,P 的 β 必含 A,B,P; I-4 唯一性推 β=α                     *)
Theorem theorem_2a : forall (I : IncidenceStructure) (l : IncLine I) (P : IncPoint I),
  ~ Incid I P l ->
  exists! alpha : IncPlane I, LineInPlane I l alpha /\ IncidPlane I P alpha.
Proof.
  intros I l P Hnoton.
  (* 从 I-3 提取: l 上至少有两点 A, B *)
  destruct (I3 I) as [H3linePts H3noncol3].
  destruct (H3linePts l) as [A [B [HA [HB HAB]]]].
  (* A, B, P 不共线: 若 m⊃A,B,P 则 m = l (I-2), P ∈ l 矛盾 *)
  assert (Hnoncol : ~ exists m : IncLine I, Incid I A m /\ Incid I B m /\ Incid I P m).
  { intros [m [HAm [HBm HPm]]].
    assert (Heq : l = m).
    { apply (I2 I l m A B (conj HA (conj HB (conj HAm HBm)))). }
    subst m. apply Hnoton. exact HPm. }
  destruct (I4 I) as [H4plane _].
  destruct (H4plane A B P Hnoncol) as [alpha [Halpha Huniq]].
  destruct Halpha as [HAalpha [HBalpha HPalpha]].
  (* 由 I-5, l 全在 α 内 *)
  assert (Hlinein : LineInPlane I l alpha).
  { unfold LineInPlane. intros X HX.
    apply (I5 I l alpha A B HA HB HAalpha HBalpha X HX). }
  exists alpha. split.
  - exact (conj Hlinein HPalpha).
  - intros beta [Hlinebeta HPbeta].
    (* beta 也包含 A, B, P; 由 I-4 唯一性推 beta = alpha *)
    assert (Hbeta_Ab : IncidPlane I A beta) by (apply (Hlinebeta A HA)).
    assert (Hbeta_Bb : IncidPlane I B beta) by (apply (Hlinebeta B HB)).
    apply (Huniq beta (conj Hbeta_Ab (conj Hbeta_Bb HPbeta))).
Qed.

(* ---- Theorem 2b: 过有公共点的两直线, 有且只有一个平面 --------------------- *)
(* Hilbert 定理 2 (第二部分):                                                  *)
(* 给定交于 P 的两不同直线 a,b, 存在唯一平面 α 包含 a 和 b.                   *)
(* 证明:                                                                      *)
(*   - 存在: 取 Q≠P 在 a 上, R≠P 在 b 上; Q,P,R 不共线;                      *)
(*            I-4 给 α=Q,P,R; I-5 推 a=QP⊂α, b=PR⊂α                         *)
(*   - 唯一: 任何含 a,b 的 β 必含 Q,P,R; I-4 唯一性推 β=α                     *)
Theorem theorem_2b : forall (I : IncidenceStructure) (a b : IncLine I),
  (exists P : IncPoint I, Incid I P a /\ Incid I P b) -> a <> b ->
  exists! alpha : IncPlane I, LineInPlane I a alpha /\ LineInPlane I b alpha.
Proof.
  intros I a b [P [HPa HPb]] Hneq.
  (* 从 I-3 提取: a 上至少有两点 *)
  destruct (I3 I) as [H3linePts _].
  (* 我们需要 Q 在 a 上且 Q ≠ P. 由 I-3 给两不同点, 至少一个 ≠ P *)
  assert (HQaQneqP : exists Q : IncPoint I, Incid I Q a /\ Q <> P).
  { destruct (H3linePts a) as [A1 [A2 [HA1 [HA2 HA12]]]].
    destruct (classic (A1 = P)) as [Heq1 | Hne1].
    - destruct (classic (A2 = P)) as [Heq2 | Hne2].
      + subst. (* A1 = P, A2 = P, 但 A1 ≠ A2 矛盾 → 由此证 ⊥ *)
        exfalso. apply HA12. reflexivity.
      + exists A2. exact (conj HA2 Hne2).
    - exists A1. exact (conj HA1 Hne1). }
  destruct HQaQneqP as [Q [HQa HQneq]].
  (* 类似取 R 在 b 上 R ≠ P *)
  assert (HRbRneqP : exists R : IncPoint I, Incid I R b /\ R <> P).
  { destruct (H3linePts b) as [B1 [B2 [HB1 [HB2 HB12]]]].
    destruct (classic (B1 = P)) as [Heq1 | Hne1].
    - destruct (classic (B2 = P)) as [Heq2 | Hne2].
      + subst. exfalso. apply HB12. reflexivity.
      + exists B2. exact (conj HB2 Hne2).
    - exists B1. exact (conj HB1 Hne1). }
  destruct HRbRneqP as [R [HRb HRneq]].
  (* Q, P, R 不共线: 若共线于 m, 则 m=a 且 m=b, 故 a=b, 矛盾 *)
  assert (Hnoncol : ~ exists m : IncLine I, Incid I Q m /\ Incid I P m /\ Incid I R m).
  { intros [m [HQm [HPm HRm]]].
    assert (ma : a = m).
    { apply (I2 I a m Q P (conj HQa (conj HPa (conj HQm HPm)))). }
    assert (mb : b = m).
    { apply (I2 I b m P R (conj HPb (conj HRb (conj HPm HRm)))). }
    apply Hneq. rewrite ma. rewrite <- mb. reflexivity. }
  destruct (I4 I) as [H4plane _].
  destruct (H4plane Q P R Hnoncol) as [alpha [Halpha Huniq]].
  destruct Halpha as [HQalpha [HPalpha HRalpha]].
  (* 由 I-5, a 全在 α 内 *)
  assert (Hlinein_a : LineInPlane I a alpha).
  { unfold LineInPlane. intros X HX.
    apply (I5 I a alpha Q P HQa HPa HQalpha HPalpha X HX). }
  assert (Hlinein_b : LineInPlane I b alpha).
  { unfold LineInPlane. intros X HX.
    apply (I5 I b alpha P R HPb HRb HPalpha HRalpha X HX). }
  exists alpha. split.
  - exact (conj Hlinein_a Hlinein_b).
  - intros beta [Hlinebeta_a Hlinebeta_b].
    assert (HbetaQ : IncidPlane I Q beta) by (apply (Hlinebeta_a Q HQa)).
    assert (HbetaP : IncidPlane I P beta) by (apply (Hlinebeta_a P HPa)).
    assert (HbetaR : IncidPlane I R beta) by (apply (Hlinebeta_b R HRb)).
    apply (Huniq beta (conj HbetaQ (conj HbetaP HbetaR))).
Qed.
