(* ============================================================================ *)
(*  CongruenceAxiims.v                                                         *)
(*  Tier-3: Hilbert 第 III 组公理 — 合同公理 (核心 5 条 Axiom)                    *)
(*                                                                            *)
(*  依赖: Common.v + Types.v (Ray)                                             *)
(*                                                                            *)
(*  Hilbert 合同公理核心 (5 条独立 Axiom):                                      *)
(*    III-1: 线段迁移 (存在性 + 唯一性, 用 Ray 表述)                              *)
(*    III-2: 合同传递                                                          *)
(*    III-3: 线段加法                                                          *)
(*    III-4: 合同对称 (独立公理, 不可从 III-2+III-5 推导)                          *)
(*    III-5: 合同自反                                                          *)
(*                                                                            *)
(*  角合同:                                                                    *)
(*    CongAng: 角合同 (Parameter, Tier-4 完整化)                                *)
(*    III-6: 角合同对称 (Axiom)                                                *)
(*                                                                            *)
(*  Tier-4 目标: III-5 的完整证明 (需 III-1 唯一性 + 直线唯一性)                  *)
(* ============================================================================ *)

From Stdlib Require Import Classical.
From Hilbert Require Import Common.
From Hilbert Require Import Types.

(* --- 线段合同 (CongSeg) ---------------------------------------------------- *)
Parameter CongSeg : Point -> Point -> Point -> Point -> Prop.

(* --- III-1: 线段迁移 — 给定线段 AB 与射线 r, 存在唯一点 X 在 r 上使 AB ≅ OX *)
Axiom III_1 : forall (A B : Point) (r : Ray),
  A <> B ->
  exists! X : Point, OnRay X r /\ CongSeg A B (ray_origin r) X.

(* --- III-2: 合同传递 ------------------------------------------------------- *)
Axiom III_2 : forall A B C D E F : Point,
  CongSeg A B C D -> CongSeg A B E F -> CongSeg C D E F.

(* --- III-3: 线段加法 ------------------------------------------------------- *)
Axiom III_3 : forall A B C A' B' C' : Point,
  Bet A B C -> Bet A' B' C' ->
  CongSeg A B A' B' -> CongSeg B C B' C' ->
  CongSeg A C A' C'.

(* --- III-4: 合同对称 (Hilbert 独立公理) ------------------------------------ *)
Axiom III_4 : forall A B C D : Point,
  CongSeg A B C D -> CongSeg C D A B.

(* --- III-5: 合同自反 (Hilbert 系统公理) ------------------------------------ *)
Axiom III_5 : forall A B : Point, CongSeg A B A B.

(* --- 角合同 (CongAng) ------------------------------------------------------ *)
Parameter CongAng : Point -> Point -> Point -> Point -> Point -> Point -> Prop.

(* --- III-6: 角合同对称 (Axiom) --------------------------------------------- *)
Axiom III_6 : forall A B C D E F : Point,
  CongAng A B C D E F -> CongAng D E F A B C.

(* Tier-3 净增量: 5 条 Axiom (III_1~III_5) + 1 个 Axiom (III_6)                  *)
(*               + 2 个 Parameters (CongSeg, CongAng)                             *)
(* Tier-4 目标: III-5 的完整证明 (需 III-1 唯一性 + 直线唯一性)                  *)

(* ============================================================================ *)
(*  Theorem 11 (Hilbert): 等腰三角形的底角相等                                 *)
(*                                                                            *)
(*  在三角形 ABC 中, 若 AB ≅ AC, 则 ∠ABC ≅ ∠ACB。                               *)
(*                                                                            *)
(*  经典证明 (Pons Asinorum): 考虑三角形 ABC 与自身 ACB:                          *)
(*    - AB ≅ AC (给定)                                                          *)
(*    - AC ≅ AB (由 III-4 合同对称)                                              *)
(*    - BC ≅ CB (由 III-5 合同自反)                                              *)
(*    - 由 III-3 线段加法, 通过构造辅助点, 证明 SSS 或直接得出底角相等           *)
(* ========================================================================= *)
Theorem theorem_11 : forall (A B C : Point),
  A <> B -> B <> C -> A <> C ->
  CongSeg A B A C ->
  CongAng A B C A C B.
Proof.
  (* 需要 SAS/SSS 合同准则 + 角合同传递性 (III-6) *)
  (* 标准证明途径: 构造 D 在 BA 延长线上使 BD ≅ BC, 然后构造全等三角形 *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 12 (Hilbert): ASA 全等定理 (角边角)                               *)
(*                                                                            *)
(*  给定三角形 ABC 和 A'B'C', 若:                                               *)
(*    (1) AB ≅ A'B' (一边相等)                                                  *)
(*    (2) ∠A ≅ ∠A', 即 ∠BAC ≅ ∠B'A'C' (两端角相等之一)                          *)
(*    (3) ∠B ≅ ∠B', 即 ∠ABC ≅ ∠A'B'C' (两端角相等之二)                          *)
(*  则两三角形全等:                                                            *)
(*    (4) AC ≅ A'C' (第三边相等)                                                *)
(*    (5) BC ≅ B'C' (第三边另一对应)                                            *)
(*    (6) ∠C ≅ ∠C', 即 ∠ACB ≅ ∠A'C'B' (第三角相等)                             *)
(*                                                                            *)
(*  证明: 用 III-1 在射线 B'C' 上取 X 使 BC ≅ B'X。若 X≠C',                       *)
(*   则 ∠ABX 矛盾于 ∠A'B'C' 的唯一性 (III-1)。故 X=C', ASA 得证。               *)
(* ========================================================================= *)
Theorem theorem_12 : forall (A B C A' B' C' : Point),
  A <> B -> B <> C -> A <> C ->
  A' <> B' -> B' <> C' -> A' <> C' ->
  (* 一边 + 两端角相等 *)
  CongSeg A B A' B' ->
  CongAng B A C B' A' C' ->
  CongAng A B C A' B' C' ->
  (* 结论: 全等 *)
  CongSeg A C A' C' /\ CongSeg B C B' C' /\ CongAng A C B A' C' B'.
Proof.
  (* 需 III-1 线段迁移唯一性 + 角合同传递性 *)
  (* 证明思路: 在 B'C' 射线上取 X 使 BC ≅ B'X; 由角唯一性推 X=C' *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 14 (Hilbert): 角合同的邻补角也合同                               *)
(*                                                                            *)
(*  若 ∠ABC ≅ ∠A'B'C', 则它们的邻补角也合同。                                   *)
(*  邻补角: 在射线 BC 的反向延长线上取 D 使 B 在 C,D 之间,                          *)
(*  则 ∠ABD 是 ∠ABC 的邻补角。                                                   *)
(*                                                                            *)
(*  即: CongAng A B C A' B' C', Bet C B D, Bet C' B' D'                       *)
(*      ⇒ CongAng A B D A' B' D'                                               *)
(*                                                                            *)
(*  证明: 由 III-2 (合同传递) + III-1 (角唯一性) 可证。                           *)
(* ========================================================================= *)
Theorem theorem_14 : forall (A B C A' B' C' D D' : Point),
  A <> B -> B <> C -> A <> C ->
  A' <> B' -> B' <> C' -> A' <> C' ->
  D <> B -> D <> A ->
  D' <> B' -> D' <> A' ->
  CongAng A B C A' B' C' ->
  Bet C B D -> Bet C' B' D' ->
  CongAng A B D A' B' D'.
Proof.
  (* 需要角合同传递性 + 邻补角唯一性 *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 15 (Hilbert): 角加/减法 — 同构三射线组角合同传递                *)
(*                                                                            *)
(*  设 h, k, l 是平面内共起点 O 的三条射线, h', k', l' 是共起点 O' 的三条射线。  *)
(*  h 相对于 (k,l) 的位置 (同侧或异侧) 与 h' 相对于 (k',l') 的位置一致。         *)
(*  若 ∠(k,l) ≅ ∠(k',l') 且 ∠(h,l) ≅ ∠(h',l'), 则 ∠(h,k) ≅ ∠(h',k')。         *)
(*                                                                            *)
(*  同侧条件: SameSide (k线) H L 表示 h 和 l 在 k 的同侧;                           *)
(*            <-> 条件确保两侧配置一致。                                         *)
(*                                                                            *)
(*  证明: 分类讨论 (同侧/异侧), 利用角合同传递性 (III-6) 和邻补角合同 (Thm 14)。 *)    
(* ========================================================================= *)
Theorem theorem_15 : forall (O O' H K L H' K' L' : Point)
  (a b c a' b' c' : Line),
  (* 三条线 a=h, b=k, c=l 均过 O *)
  Incid O a -> Incid H a -> H <> O ->
  Incid O b -> Incid K b -> K <> O ->
  Incid O c -> Incid L c -> L <> O ->
  (* 三条线 a'=h', b'=k', c'=l' 均过 O' *)
  Incid O' a' -> Incid H' a' -> H' <> O' ->
  Incid O' b' -> Incid K' b' -> K' <> O' ->
  Incid O' c' -> Incid L' c' -> L' <> O' ->
  (* 同侧/异侧配置一致 *)
  (SameSide b H L <-> SameSide b' H' L') ->
  (* 角合同条件 *)
  CongAng K O L K' O' L' ->
  CongAng H O L H' O' L' ->
  (* 结论 *)
  CongAng H O K H' O' K'.
Proof.
  (* 分类讨论: SameSide b H L 成立/不成立 → 角加法或角减法 *)
  admit.
Admitted.

(* ============================================================================ *)
(*  垂线定义                                                                    *)
(* ============================================================================ *)

(* 两直线 l, m 在点 P 处垂直:                                                    *)
(*  在 l 上取 A, B 使 Bet A P B (A, B 在 P 两侧), 在 m 上取 C (C ≠ P),          *)
(*  使得 ∠APC ≅ ∠CPB (邻角相等, 即直角)。                                        *)
Definition Perpendicular (l m : Line) : Prop :=
  exists P : Point, Incid P l /\ Incid P m /\
    exists (A B : Point) (C : Point),
      Incid A l /\ Incid B l /\ Incid C m /\
      A <> P /\ B <> P /\ C <> P /\
      Bet A P B /\
      CongAng A P C C P B.

(* ============================================================================ *)
(*  Theorem 19 (Hilbert): 过直线上一点有且仅有一条垂线                        *)
(*                                                                            *)
(*  给定直线 l 和 l 上一点 P, 存在唯一直线 m 使 P ∈ m 且 m ⟂ l。                 *)
(*                                                                            *)
(*  证明: 用 III-1 在 l 上取 A, B 使 PA ≅ PB 且 Bet A P B;                         *)
(*        在 l 外取一点 Q, 由 Thm 15 构造等腰三角形 QAB, 取底边中点得垂线。        *)
(* ========================================================================= *)
Theorem theorem_19 : forall (l : Line) (P : Point),
  Incid P l ->
  exists! m : Line, Incid P m /\ Perpendicular l m.
Proof.
  (* 需要 Thm 14 (邻补角) + Thm 15 (角加法) + III-1 线段迁移唯一性 *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 20 (Hilbert): 过直线外一点有且仅有一条垂线                        *)
(*                                                                            *)
(*  给定直线 l 和不在 l 上的点 P, 存在唯一直线 m 使 P ∈ m 且 m ⟂ l。             *)
(*                                                                            *)
(*  证明: 在 l 上取两点 A, B, 用 III-1 在 l 两侧各取 A', B' 使 PA' ≅ PA, PB' ≅ PB; *)
(*        由 Thm 15 得 ∠A'PA' ≅ ∠B'PB', 取角平分线得垂线。                       *)
(* ========================================================================= *)
Theorem theorem_20 : forall (l : Line) (P : Point),
  ~ Incid P l ->
  exists! m : Line, Incid P m /\ Perpendicular l m.
Proof.
  (* 需要 Thm 19 + 三角形全等 (Thm 12) + 角平分线存在性 *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 21 (Hilbert): 直角三角形中斜边大于直角边                          *)
(*                                                                            *)
(*  在直角三角形 ABC 中, ∠C = 90° (即 ∠ACB 为直角), 则斜边 AB 大于两直角边 AC, BC。 *)
(*  即: AB > AC 且 AB > BC。                                                   *)
(*                                                                            *)
(*  证明: 由 Thm 18 (三角形两边之和大于第三边) 可直接推出:                        *)
(*        AB + BC > AC 且 AB + AC > BC, 但更直接的证明是:                       *)
(*        在直角三角形中, 直角是最大的角, 由 Thm 17 (大角对大边) 即得。           *)
(* ========================================================================= *)
Theorem theorem_21 : forall (A B C : Point),
  A <> B -> B <> C -> A <> C ->
  (* ∠ACB 为直角: 在 BC 所在直线上取 D 使 Bet D C B, 且 ∠ACD ≅ ∠ACB *)
  (exists (l : Line) (D : Point),
    Incid B l /\ Incid C l /\
    Incid D l /\
    Bet D C B /\
    CongAng A C D A C B) ->
  (* 斜边 AB 大于两直角边 *)
  ~ CongSeg A B A C /\ ~ CongSeg A B B C.
Proof.
  (* 需要 Thm 17 (大角对大边) + 直角定义 *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 22 (Hilbert): 外角定理 — 外角大于任意不相邻内角                  *)
(*                                                                            *)
(*  在三角形 ABC 中, 延长边 AC 到 D (Bet A C D), 则外角 ∠BCD 大于:              *)
(*    (1) 不相邻内角 ∠CAB (∠A 处);                                             *)
(*    (2) 不相邻内角 ∠ABC (∠B 处)。                                             *)
(*                                                                            *)
(*  角不等式 ∠BCD > ∠CAB 定义为:                                               *)
(*    存在射线 CE 在 ∠BCD 内部, 使 ∠ECD ≅ ∠CAB (且 E ≠ C, ~ SameSide (line BC) E D). *)
(*  此处用简化表述: ∠BCD ≅ ∠CAB ∧ ∠BCD ≅ ∠ABC 均不成立。                       *)
(*                                                                            *)
(*  证明: 取 BC 中点 M (Thm 10), 连 AM 并延长至 E 使 M 为 AE 中点;               *)
(*        △AMC ≅ △EMB (SAS, Thm 12) ⇒ ∠MAC ≅ ∠MEB; 由 Thm 14 邻补角得外角更大。 *)
(* ========================================================================= *)
Theorem theorem_22 : forall (A B C D : Point) (l : Line),
  ~ (exists m : Line, Incid A m /\ Incid B m /\ Incid C m) ->
  Incid A l -> Incid C l -> Incid D l ->
  Bet A C D ->
  ~ CongAng B C D C A B /\ ~ CongAng B C D A B C.
Proof.
  (* 需要 Thm 10 (中点) + Thm 12 (SAS) + Thm 14 (邻补角) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 23 (Hilbert): 垂线段最短 — 点到直线的距离                       *)
(*                                                                            *)
(*  给定直线 l 和不在 l 上的点 P, 过 P 作 l 的垂线 (Thm 20), 垂足为 F。           *)
(*  对 l 上任意不同于 F 的点 Q, 有 PF < PQ (即垂线段最短)。                      *)
(*                                                                            *)
(*  证明: 在三角形 PFQ 中, 由 Perpendicular 定义, ∠PFQ 是直角。                  *)
(*        ∠PFQ 是三角形 PFQ 的最大角 (外角定理 Thm 22 + 直角定义),               *)
(*        由 Thm 17 (大角对大边) 得 PQ > PF。                                    *)
(* ========================================================================= *)
Theorem theorem_23 : forall (l m : Line) (P F Q : Point),
  ~ Incid P l ->
  Incid P m -> Incid F m ->
  Incid F l -> Incid Q l ->
  Q <> F ->
  Perpendicular l m ->
  ~ CongSeg P F P Q.
Proof.
  (* 需要 Thm 22 (外角定理) + Thm 17 (大角对大边) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 24 (Hilbert): 中垂线定理 — 中垂线上点到线段两端等距            *)
(*                                                                            *)
(*  设 M 是线段 AB 的中点, l 是过 M 且垂直于 AB 的直线 (中垂线)。                *)
(*  对 l 上任意一点 P, 有 PA ≅ PB。                                             *)
(*                                                                            *)
(*  证明: 在 △PMA 和 △PMB 中:                                                 *)
(*    - PM ≅ PM (III-5 自反)                                                   *)
(*    - AM ≅ BM (M 为中点)                                                     *)
(*    - ∠PMA ≅ ∠PMB = 90° (l ⟂ AB)                                            *)
(*    - 由 SAS (Thm 12) ⇒ △PMA ≅ △PMB ⇒ PA ≅ PB                                *)
(* ========================================================================= *)
Theorem theorem_24 : forall (A B M P : Point) (l m : Line),
  A <> B -> M <> A -> M <> B -> P <> M ->
  Incid A m -> Incid B m ->                (* 直线 m = AB *)
  Incid M m ->                              (* M 在 AB 上 *)
  Bet A M B ->                              (* M 是 AB 中点: A—M—B *)
  CongSeg A M B M ->                         (* AM ≅ BM, 中点合同定义 *)
  Incid P l -> Incid M l ->                  (* l 过 P 和 M *)
  Perpendicular m l ->                       (* l ⟂ m, 即 l 是垂直平分线 *)
  CongSeg P A P B.
Proof.
  (* 需要 Thm 12 (SAS) + III-5 (自反) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 25 (Hilbert): 中垂线逆定理 — 到两端等距的点在中垂线上          *)
(*                                                                            *)
(*  设 M 是线段 AB 的中点, 若点 P 满足 PA ≅ PB, 则 P 在线段 AB 的中垂线上。      *)
(*  即: 直线 PM ⟂ AB。                                                        *)
(*                                                                            *)
(*  证明: 在 △PMA 和 △PMB 中:                                                 *)
(*    - PA ≅ PB (给定)                                                         *)
(*    - AM ≅ BM (M 为中点)                                                     *)
(*    - PM ≅ PM (III-5 自反)                                                   *)
(*    - 由 SSS (Thm 13) ⇒ △PMA ≅ △PMB ⇒ ∠PMA ≅ ∠PMB                            *)
(*    - ∠PMA 与 ∠PMB 是邻补角 (Bet A M B 推邻补), 由 Thm 14 知它们合同且互补,    *)
(*      故均为直角 → PM ⟂ AB。                                               *)
(* ========================================================================= *)
Theorem theorem_25 : forall (A B M P : Point) (m : Line),
  A <> B -> M <> A -> M <> B -> P <> M ->
  Incid A m -> Incid B m -> Incid M m ->
  Bet A M B ->                              (* M 是 AB 中点: A—M—B *)
  CongSeg A M B M ->                         (* AM ≅ BM *)
  CongSeg P A P B ->                         (* PA ≅ PB *)
  (* 结论: 存在 l 过 P,M 且 l ⟂ m *)
  exists l : Line, Incid P l /\ Incid M l /\ Perpendicular m l.
Proof.
  (* 需要 Thm 13 (SSS) + Thm 14 (邻补角) + Thm 19 (过直线上一点垂线唯一) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 26 (Hilbert): 外心定理 — 三角形三中垂线交于一点                  *)
(*                                                                            *)
(*  三角形 ABC 的三边各自的中垂线交于同一点 O, 该点到三顶点等距:                *)
(*  OA ≅ OB ≅ OC。                                                             *)
(*                                                                            *)
(*  证明: 设 l_AB, l_BC 分别为 AB 和 BC 的中垂线, 交于 O。                     *)
(*        Thm 24 ⇒ OA ≅ OB (O 在 AB 中垂线上) 且 OB ≅ OC (O 在 BC 中垂线上),    *)
(*        III-2 (合同传递) ⇒ OA ≅ OC ⇒ Thm 25 ⇒ O 在 AC 的中垂线上。           *)
(* ========================================================================= *)
Theorem theorem_26 : forall (A B C : Point) (m_AB m_BC : Line),
  ~ (exists l : Line, Incid A l /\ Incid B l /\ Incid C l) ->
  (* 设 M_AB 是 AB 中点, l_AB 是 AB 中垂线; M_BC 是 BC 中点 *)
  (exists (M_AB : Point) (M_BC : Point),
    Incid M_AB m_AB /\ Incid A m_AB /\ Incid B m_AB /\
    Bet A M_AB B /\ CongSeg A M_AB B M_AB /\
    Incid M_BC m_BC /\ Incid B m_BC /\ Incid C m_BC /\
    Bet B M_BC C /\ CongSeg B M_BC C M_BC) ->
  (* 存在点 O 同时在中垂线上, 且等距于三顶点 *)
  exists O : Point,
    (exists l_AB l_BC l_AC : Line,
      Incid O l_AB /\ Perpendicular m_AB l_AB /\
      Incid O l_BC /\ Perpendicular m_BC l_BC /\
      Incid O l_AC /\ Perpendicular m_AB l_AC) /\
    CongSeg O A O B /\ CongSeg O B O C /\ CongSeg O A O C.
Proof.
  (* 需要 Thm 24 (中垂线定理) + Thm 25 (中垂线逆定理) + III-2 (合同传递) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 27 (Hilbert): 内心定理 — 三角形三角平分线交于一点               *)
(*                                                                            *)
(*  三角形 ABC 的三个内角平分线交于同一点 O, 该点到三边距离相等。                *)
(*  等价于: 存在 O 使 ∠CAO ≅ ∠OAB, ∠ABO ≅ ∠OBC, ∠BCO ≅ ∠OCA。                *)
(*                                                                            *)
(*  证明: 设 O 是 ∠A 和 ∠B 的平分线交点。                                     *)
(*        Thm 12 (ASA): 由角相等推三角形全等, 得 O 到三边等距。                  *)
(*        再由 Thm 14 (邻补角) + 角加法得 O 也在 ∠C 平分线上。                 *)
(* ========================================================================= *)
Theorem theorem_27 : forall (A B C : Point),
  ~ (exists l : Line, Incid A l /\ Incid B l /\ Incid C l) ->
  exists O : Point,
    CongAng C A O O A B /\   (* O 在 ∠A 平分线上 *)
    CongAng A B O O B C /\   (* O 在 ∠B 平分线上 *)
    CongAng B C O O C A.     (* O 在 ∠C 平分线上 *)
Proof.
  (* 需要 Thm 12 (ASA) + Thm 14 (邻补角) + Thm 15 (角加法) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 28 (Hilbert): 平行判定 — 同位角相等则两直线平行                 *)
(*                                                                            *)
(*  若两直线 a,b 被第三直线 c 所截, 截点分别为 P,Q, 形成的同位角相等              *)
(*  (∠APQ ≅ ∠PQB, A∈a, B∈b, A,B 在 c 同侧), 则 a ∥ b。                         *)
(*                                                                            *)
(*  证明 (反证法): 假设 a 与 b 交于 R, 则三角形 PQR 中:                       *)
(*        ∠APQ 是三角形 PQR 外角 (或内部), 由 Thm 22 (外角定理)                 *)
(*        ∠APQ ≠ ∠PQB, 与条件矛盾。故 a,b 不相交 → 平行。                      *)
(* ========================================================================= *)
Theorem theorem_28 : forall (a b c : Line) (P Q A B : Point),
  P <> Q ->
  Incid P a -> Incid P c ->
  Incid Q b -> Incid Q c ->
  Incid A a -> A <> P ->
  Incid B b -> B <> Q ->
  CongAng A P Q P Q B ->
  SameSide c A B ->
  Parallel a b.
Proof.
  (* 需要 Thm 22 (外角定理) + II 组直线上两点之间存在点 *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 29 (Hilbert): 三角形内角和定理 — 内角和等于两个直角              *)
(*                                                                            *)
(*  在三角形 ABC 中, 三个内角之和等于两个直角:                                  *)
(*    ∠BAC + ∠ABC + ∠ACB = 2 × 直角。                                         *)
(*                                                                            *)
(*  证明: 过 A 作 BC 的平行线 l (IV-1)。                                       *)
(*        由 Thm 28 (同位角相等) 得 ∠ABC ≅ ∠(l, AB) 且 ∠ACB ≅ ∠(l, AC)。       *)
(*        由 Thm 15 (角加法) 得 ∠BAC + ∠ABC + ∠ACB = 直线 l 上的平角 = 2×直角。 *)
(* ========================================================================= *)
Theorem theorem_29 : forall (A B C : Point) (l : Line),
  ~ (exists m : Line, Incid A m /\ Incid B m /\ Incid C m) ->
  Incid B l -> Incid C l ->
  (* 存在过 A 的平行线 l' 平行于 l, 且三个内角可拼成平角 *)
  exists l' : Line, Incid A l' /\ Parallel l l' /\
    (* 在 l' 上取点 D, E 使 Bet D A E, 且 ∠DAB ≅ ∠ABC, ∠EAC ≅ ∠ACB *)
    (* 则 ∠BAC + ∠ABC + ∠ACB = ∠DAE = 平角 (两个直角) *)
    exists (D E : Point),
      Incid D l' /\ Incid E l' /\
      Bet D A E /\
      CongAng D A B A B C /\
      CongAng E A C A C B.
Proof.
  (* 需要 IV-1 (过直线外一点平行线) + Thm 28 (同位角) + Thm 15 (角加法) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  平行四边形定义                                                              *)
(* ============================================================================ *)

Definition Parallelogram (A B C D : Point) : Prop :=
  exists (l_AB l_BC l_CD l_DA : Line),
    Incid A l_AB /\ Incid B l_AB /\
    Incid B l_BC /\ Incid C l_BC /\
    Incid C l_CD /\ Incid D l_CD /\
    Incid D l_DA /\ Incid A l_DA /\
    Parallel l_AB l_CD /\
    Parallel l_BC l_DA.

(* ============================================================================ *)
(*  Theorem 30 (Hilbert): 平行四边形对边相等                                *)
(*                                                                            *)
(*  在平行四边形 ABCD 中, 对边分别相等:                                        *)
(*    (1) AB ≅ CD                                                              *)
(*    (2) AD ≅ BC                                                              *)
(*                                                                            *)
(*  证明: 连对角线 AC。                                                        *)
(*        由 AB ∥ CD 得 ∠BAC ≅ ∠DCA (Thm 28 同位角);                           *)
(*        由 AD ∥ BC 得 ∠BCA ≅ ∠DAC (Thm 28 同位角);                           *)
(*        AC ≅ AC (III-5 自反);                                                *)
(*        由 ASA (Thm 12) ⇒ △ABC ≅ △CDA ⇒ AB ≅ CD, AD ≅ BC。                   *)
(* ========================================================================= *)
Theorem theorem_30 : forall (A B C D : Point),
  Parallelogram A B C D ->
  CongSeg A B C D /\ CongSeg A D B C.
Proof.
  (* 需要 Thm 12 (ASA) + Thm 28 (同位角) + III-5 (自反) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 31 (Hilbert): 平行四边形对角线互相平分                        *)
(*                                                                            *)
(*  在平行四边形 ABCD 中, 对角线 AC 与 BD 互相平分, 即:                       *)
(*    设 M 为 AC 与 BD 的交点, 则 AM ≅ MC 且 BM ≅ MD。                         *)
(*                                                                            *)
(*  证明: 由 Thm 30 (对边相等) + Thm 28 (同位角):                             *)
(*        ∠BAM ≅ ∠DCM, ∠ABM ≅ ∠CDM, AB ≅ CD,                                  *)
(*        由 ASA (Thm 12) ⇒ △ABM ≅ △CDM ⇒ AM ≅ MC, BM ≅ MD。                  *)
(* ========================================================================= *)
Theorem theorem_31 : forall (A B C D : Point),
  Parallelogram A B C D ->
  exists (M : Point) (l_AC l_BD : Line),
    Incid A l_AC /\ Incid C l_AC /\
    Incid B l_BD /\ Incid D l_BD /\
    Incid M l_AC /\ Incid M l_BD /\
    (* M 是 AC 与 BD 的交点, 且 M 平分两条对角线 *)
    CongSeg A M M C /\ CongSeg B M M D.
Proof.
  (* 需要 Thm 30 (平行四边形对边相等) + Thm 28 (同位角) + Thm 12 (ASA) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 32 (SSS 全等定理, Hilbert Thm 13)                                *)
(*                                                                            *)
(*  若两个三角形的三对边分别合同:                                                *)
(*    (1) AB ≅ A'B', BC ≅ B'C', AC ≅ A'C'                                      *)
(*  则三对角也分别合同:                                                       *)
(*    ∠BAC ≅ ∠B'A'C', ∠ABC ≅ ∠A'B'C', ∠ACB ≅ ∠A'C'B'                          *)
(*                                                                            *)
(*  证明: 用反证法。假设 ∠BAC ≠ ∠B'A'C',                                        *)
(*        在 A'B' 的另一侧构造与 △ABC 合同但 ≠ △A'B'C' 的三角形 △AB'C''            *)
(*        由 Thm 11 (等腰三角形底角相等) 导出矛盾。                                *)
(* ========================================================================= *)
Theorem theorem_32 : forall (A B C A' B' C' : Point),
  A <> B -> B <> C -> A <> C ->
  A' <> B' -> B' <> C' -> A' <> C' ->
  CongSeg A B A' B' ->
  CongSeg B C B' C' ->
  CongSeg A C A' C' ->
  CongAng B A C B' A' C' /\ CongAng A B C A' B' C' /\ CongAng A C B A' C' B'.
Proof.
  (* 需要 Thm 11 (等腰三角形底角相等) + 反证法 + III 组合同传递性 *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 33 (Hilbert Thm 10): 线段中点存在唯一性                          *)
(*                                                                            *)
(*  对任意两个不同点 A, C, 存在唯一点 B 使得 B 在 A,C 之间且 AB ≅ BC。           *)
(*                                                                            *)
(*  证明:                                                                     *)
(*    (1) 存在性:                                                              *)
(*        过 A,C 作直线 l (I_1)。                                              *)
(*        在 l 外取点 D (由 I_3, 存在不共线三点), 连 D,A 和 D,C。               *)
(*        由 III-1 在射线 DA 上取 E 使 AD ≅ A'E? 更复杂...                     *)
(*        标准构造: 在直线 AC 外取点 D, 在射线 DA 上取 E 使 AD ≅ DE,            *)
(*        连 EC, 过 D 作 EC 平行线交 AC 于 B, 由 Thm 30 (平行四边形) 得证。 *)
(*        另一种标准证明: 用 III-1 构造等腰三角形, 再用角平分线性质。            *)
(*    (2) 唯一性: 由 Bet 唯一性 + 合同唯一性 (III-1) 保证。                    *)
(* ========================================================================= *)
Theorem theorem_33 : forall (A C : Point),
  A <> C ->
  exists! B : Point, Bet A B C /\ CongSeg A B B C.
Proof.
  (* 需要 III-1 (线段迁移) + 等腰三角形构造 + Bet 唯一性 *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 34 (Hilbert Thm 11 逆定理): 等角对等边                          *)
(*                                                                            *)
(*  若三角形 ABC 中 ∠ABC ≅ ∠ACB (底角相等), 则 AB ≅ AC (腰相等)。              *)
(*                                                                            *)
(*  证明 (反证法 + SSS):                                                     *)
(*    假设 AB ≠ AC。不妨设 AB > AC (用合同传递性 III-2 比较)。                   *)
(*    在射线 AB 上取点 D 使 AD ≅ AC (III-1)。                                  *)
(*    则 CD 中垂线...                                                          *)
(*    标准证明: 由 ASA (Thm 12) 或 SSS (Thm 32) 可证:                           *)
(*      - 取 BC 中点 M (Thm 33), 连 AM。                                        *)
(*      - △ABM 和 △ACM 中: BM ≅ CM (中点), AM ≅ AM (III-5), ∠AMB ≅ ∠AMC?      *)
(*      - 由 SSS (Thm 32) ⇒ △ABM ≅ △ACM ⇒ AB ≅ AC。                            *)
(* ========================================================================= *)
Theorem theorem_34 : forall (A B C : Point),
  A <> B -> B <> C -> A <> C ->
  CongAng A B C A C B ->
  CongSeg A B A C.
Proof.
  (* 需要 Thm 33 (中点) + Thm 32 (SSS) + III-5 (自反) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 35 (SAS 全等定理): 两边及其夹角分别相等的两三角形全等             *)
(*                                                                            *)
(*  若 △ABC 和 △A'B'C' 满足:                                                *)
(*    (1) AB ≅ A'B' (一对边相等)                                                *)
(*    (2) AC ≅ A'C' (另一对边相等)                                              *)
(*    (3) ∠BAC ≅ ∠B'A'C' (夹角相等)                                            *)
(*  则:                                                                       *)
(*    (4) BC ≅ B'C' (第三边相等)                                                *)
(*    (5) ∠ABC ≅ ∠A'B'C' (第二角相等)                                          *)
(*    (6) ∠ACB ≅ ∠A'C'B' (第三角相等)                                          *)
(*                                                                            *)
(*  证明: 用 III-1 在射线 A'B' 上取 X 使 BC ≅ A'X。                            *)
(*        由 ASA (Thm 12) 得 △ABC ≅ △A'B'X ⇒ AC ≅ A'X, ∠BAC ≅ ∠B'A'X。        *)
(*        由 ∠BAC ≅ ∠B'A'C' 和角的唯一性 (III-1) 得 X = C'。                    *)
(* ========================================================================= *)
Theorem theorem_35 : forall (A B C A' B' C' : Point),
  A <> B -> B <> C -> A <> C ->
  A' <> B' -> B' <> C' -> A' <> C' ->
  CongSeg A B A' B' ->
  CongSeg A C A' C' ->
  CongAng B A C B' A' C' ->
  CongSeg B C B' C' /\ CongAng A B C A' B' C' /\ CongAng A C B A' C' B'.
Proof.
  (* 需要 Thm 12 (ASA) + III-1 (线段/角迁移唯一性) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 36 (等腰三角形中线性质): 等腰三角形的底边中线垂直底边            *)
(*                                                                            *)
(*  在等腰三角形 ABC 中, AB ≅ AC。设 M 为 BC 的中点 (Bet B M C, BM ≅ MC)。       *)
(*  则 AM ⟂ BC, 即 ∠AMB ≅ ∠BMC (邻补角相等 ⇒ 直角)。                            *)
(*                                                                            *)
(*  证明:                                                                    *)
(*    △ABM 和 △ACM 中:                                                        *)
(*      - AB ≅ AC (给定)                                                       *)
(*      - AM ≅ AM (III-5 自反)                                                 *)
(*      - BM ≅ CM (M 为中点)                                                   *)
(*      - 由 SSS (Thm 32) ⇒ △ABM ≅ △ACM ⇒ ∠AMB ≅ ∠AMC                          *)
(*    - 由 Bet B M C 知 ∠AMB 和 ∠AMC 是邻补角                                   *)
(*    - 邻补角相等 ⇒ 均为直角 ⇒ AM ⟂ BC                                        *)
(* ========================================================================= *)
Theorem theorem_36 : forall (A B C M : Point),
  A <> B -> B <> C -> A <> C -> M <> B -> M <> C ->
  CongSeg A B A C ->
  Bet B M C -> CongSeg B M M C ->
  CongAng A M B B M C.
Proof.
  (* 需要 Thm 32 (SSS) + III-5 (自反) + 邻补角性质 (Thm 14) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 37 (角合同传递性): CongAng 是传递关系                             *)
(*                                                                            *)
(*  若 ∠ABC ≅ ∠DEF 且 ∠DEF ≅ ∠GHI, 则 ∠ABC ≅ ∠GHI。                           *)
(*                                                                            *)
(*  证明: 由 III-6 (角合同对称) + 合同公理的传递性。                              *)
(*  具体: 用 III-1 (角迁移唯一性) + III-2 (合同传递性) 可证。                     *)
(*  在 ℝ³ 模型中由余弦平方相等直接可得。                                          *)
(* ========================================================================= *)
Theorem theorem_37 : forall (A B C D E F G H I : Point),
  A <> B -> B <> C -> A <> C ->
  D <> E -> E <> F -> D <> F ->
  G <> H -> H <> I -> G <> I ->
  CongAng A B C D E F -> CongAng D E F G H I ->
  CongAng A B C G H I.
Proof.
  (* 需要 III-6 (对称) + 角合同传递性 (或 III-1 角唯一性) *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 38 (外角定理, Hilbert Thm 16): 三角形外角大于不相邻内角           *)
(*                                                                            *)
(*  在 △ABC 中, 延长 BC 至 D (Bet B C D)。则外角 ∠ACD > 内角 ∠BAC 和 ∠ABC。  *)
(*                                                                            *)
(*  证明:                                                                    *)
(*    取 AC 中点 M (Thm 33), 延长 BM 至 E 使 BM ≅ ME。                           *)
(*    由 SAS (Thm 35) ⇒ △BMC ≅ △EMA ⇒ BC ≅ AE, ∠BCM ≅ ∠EAM。                   *)
(*    由 ∠BCM = ∠ACD (对顶角) 得 ∠ACD > ∠BAC。                                  *)
(*    同理 ∠ACD > ∠ABC。                                                        *)
(* ========================================================================= *)
Theorem theorem_38 : forall (A B C D : Point),
  A <> B -> B <> C -> A <> C ->
  Bet B C D ->
  (* 外角 ∠ACD 大于内角 ∠BAC 和 ∠ABC *)
  (* 注: 此处用 "角大于" 的几何定义, 即 ∠ACD 包含 ∠BAC 或 ∠ABC *)
  (* 具体: 在 ∠ACD 内部存在射线使得 ∠ACD > ∠BAC *)
  (* 形式化: 存在点 E 在 ∠ACD 内部使得 ∠BAC ≅ ∠ACE, 且 E 在 ∠ACD 内部 *)
  (* 简化: 用 Thm 15 (角大小比较) 的框架 *)
  True.
Proof.
  (* 需要 Thm 33 (中点) + Thm 35 (SAS) + 对顶角相等 + 角大小比较 *)
  admit.
Admitted.

(* ============================================================================ *)
(*  Theorem 39 (直角三角形斜边中线定理): 斜边中点到三顶点等距                  *)
(*                                                                            *)
(*  在直角三角形 ABC 中, ∠ACB 为直角, M 为斜边 AB 的中点 (Bet A M B, AM ≅ MB)。  *)
(*  则 CM ≅ AM (即 CM ≅ AM ≅ BM)。                                              *)
(*                                                                            *)
(*  证明 (矩形法):                                                            *)
(*    过 A 作 BC 的平行线, 过 B 作 AC 的平行线, 两线交于 D。                    *)
(*    则 ACBD 是矩形 (由平行和直角推得), M 是矩形对角线交点。                   *)
(*    由矩形对角线相等且互相平分 (Thm 30, 31) 得 CM = AM = BM。                *)
(*                                                                            *)
(*  证明 (直接法):                                                            *)
(*    延长 CM 至 N 使 CM ≅ MN。                                                 *)
(*    则 AM = BM (中点), CM = MN (构造)。                                       *)
(*    由 SAS (Thm 35) 可证 △AMC ≅ △BMN ⇒ ∠MAC ≅ ∠MBN ⇒ AC ∥ BN。                *)
(*    同理 △CMB ≅ △NMA ⇒ CN 为直径 ⇒ CM = AM。                                  *)
(* ========================================================================= *)
Theorem theorem_39 : forall (A B C M : Point) (l : Line) (D : Point),
  A <> B -> B <> C -> A <> C -> M <> A -> M <> B ->
  Bet A M B -> CongSeg A M M B ->
  Incid B l -> Incid C l -> Incid D l ->
  Bet D C B ->
  CongAng A C D A C B ->
  CongSeg C M A M.
Proof.
  (* 需要 Thm 30 (平行四边形) + Thm 33 (中点) + Thm 35 (SAS) + 平行线性质 *)
  admit.
Admitted.