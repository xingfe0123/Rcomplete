(* ============================================================================ *)
(*  HilbertStructure.v                                                          *)
(*  Tier-5: Hilbert 公理系统的 5 个独立 Record 抽象                                *)
(*                                                                            *)
(*  把 Hilbert 公理系统拆分为 5 个独立 Record, 每个 Record 自包含载体类型和公理.    *)
(*  这样 Q² 可以作为 Record 的具体实例构造, 验证公理的独立性 (V_2 独立于 V_1).   *)
(*                                                                            *)
(*  6 个 Record:                                                               *)
(*    IncidenceStructure    — I-1~I-8 (关联公理)                                 *)
(*    OrderStructure        — II-1~II-4 + Pasch (顺序公理)                       *)
(*    CongruenceStructure   — III-1~III-6 + CongSeg/CongAng 参数 (合同公理)     *)
(*    ParallelStructure     — IV-1~IV-2 + Parallel (平行公理)                    *)
(*    ArchimedesStructure   — V-1 (Archimedes 公理)                              *)
(*    DedekindStructure     — V-2 (戴德金完备性公理)                              *)
(*                                                                            *)
(*  设计目标:                                                                  *)
(*    1. 每个 Record 包含 载体 (Point/Line) + 关系 + 公理, 自包含              *)
(*    2. Q² 可作为前 4 个 Record 的实例 (满足 I-IV + V_1)                      *)
(*    3. Q² 不能作为 DedekindStructure 的实例 (V_2 在 Q 中不成立, √2 反例)      *)
(*                                                                            *)
(*  依赖: Common.v (作为 "抽象接口", 后续文件可改用具体 Record 实例)              *)
(*  平行关系 Parallel 从 Common.v 的 Parameter 迁移到 ParallelStructure Record    *)
(* ============================================================================ *)

From Stdlib Require Import Classical.

(* ============================================================================ *)
(*  IncidenceStructure: 关联公理 (I-1 ~ I-8)                                     *)
(*                                                                            *)
(*  载体: Point, Line, Plane                                                    *)
(*  关系: Incid (点在直线上), IncidPlane (点在平面上)                            *)
(*  公理: I-1: 两点确定一直线                                                   *)
(*        I-2: 两点至多确定一直线                                               *)
(*        I-3: 直线上至少两点 + 至少三点不共线                                  *)
(*        I-4: 三点不共线唯一确定一平面                                         *)
(*        I-5: 直线两点在平面内 ⇒ 整直线在平面内                                *)
(*        I-6: 平面内至少三点不共线 + 平面外存在一点                            *)
(*        I-7: 两平面交于一点 ⇒ 至少交于两点                                    *)
(*        I-8: 至少四点不共面                                                   *)
(* ============================================================================ *)

Record IncidenceStructure : Type := mkIncidence {
  IncPoint : Type;
  IncLine : Type;
  IncPlane : Type;
  Incid : IncPoint -> IncLine -> Prop;
  IncidPlane : IncPoint -> IncPlane -> Prop;

  I1 : forall A B : IncPoint, exists l : IncLine, Incid A l /\ Incid B l;
  I2 : forall (l m : IncLine) (P Q : IncPoint),
    Incid P l /\ Incid Q l /\ Incid P m /\ Incid Q m -> l = m;
  I3 : (forall l : IncLine, exists P Q : IncPoint, Incid P l /\ Incid Q l /\ P <> Q)
       /\ (exists A B C : IncPoint, ~(exists l : IncLine, Incid A l /\ Incid B l /\ Incid C l));
  I4 : (forall A B C : IncPoint,
    ~(exists l : IncLine, Incid A l /\ Incid B l /\ Incid C l) ->
    exists! alpha : IncPlane,
      IncidPlane A alpha /\ IncidPlane B alpha /\ IncidPlane C alpha)
    /\ (forall alpha : IncPlane, exists P : IncPoint, IncidPlane P alpha);
  I5 : forall (a : IncLine) (alpha : IncPlane) (A B : IncPoint),
    Incid A a -> Incid B a -> IncidPlane A alpha -> IncidPlane B alpha ->
    forall X : IncPoint, Incid X a -> IncidPlane X alpha;
  I6 : forall alpha : IncPlane,
    exists A B C : IncPoint,
      IncidPlane A alpha /\ IncidPlane B alpha /\ IncidPlane C alpha /\
      ~(exists l : IncLine, Incid A l /\ Incid B l /\ Incid C l);
  I7 : forall alpha beta : IncPlane,
    forall A : IncPoint, IncidPlane A alpha /\ IncidPlane A beta ->
    exists B : IncPoint, IncidPlane B alpha /\ IncidPlane B beta /\ A <> B;
  I8 : exists A B C D : IncPoint,
    ~(exists alpha : IncPlane, IncidPlane A alpha /\ IncidPlane B alpha /\
                              IncidPlane C alpha /\ IncidPlane D alpha)
}.

(* ============================================================================ *)
(*  OrderStructure: 顺序公理 (Hilbert 1959 II-1 ~ II-4 + Pasch + Bet 元性质)      *)
(*                                                                            *)
(*  依赖: IncidenceStructure (需要 Point, Line, Incid)                          *)
(*  新增关系: Bet (B 在 A,C 之间)                                               *)
(*                                                                            *)
(*  Hilbert 1959 §4 公理 II:                                                    *)
(*    II-1: 给定线段 AB, B 端延长线上存在点 C (即 Bet A B C)                 *)
(*    II-2: 给定线段 AB, A 端延长线上存在点 D (即 Bet D A B)                 *)
(*    II-3: 给定共线两点 A,B (A ≠ B), 存在第三点 C 使 Bet A C B                 *)
(*          (此即 "betwixt" 公理, 任意两点之间有中间点)                          *)
(*    II-4: Pasch 公理 — 直线穿过三角形一边的两点必穿过另一边                   *)
(*                                                                            *)
(*  Hilbert 1959 §3 定义 Bet 元性质: Bet 对称、非退化、内点传递.                *)
(*                                                                            *)
(*  字段命名映射:                                                              *)
(*    II_1  = Hilbert 1959 II-1 (B 端延长)                                      *)
(*    II_2  = Hilbert 1959 II-2 (A 端延长)                                      *)
(*    II_3  = Hilbert 1959 II-3 (betwixt, 两点间有中间点)                       *)
(*    Bet_sym / Bet_nondeg / Bet_trans: Hilbert 1959 §3 元性质                   *)
(*    Pasch = Hilbert 1959 II-4 (Pasch 公理)                                    *)
(* ============================================================================ *)

Record OrderStructure (I : IncidenceStructure) : Type := mkOrder {
  Bet : IncPoint I -> IncPoint I -> IncPoint I -> Prop;

  (* Hilbert 1959 II-1: 给定线段 AB (A ≠ B 共线), B 端延长线上存在 C (Bet A B C). *)
  II_1 : forall (A B : IncPoint I) (a : IncLine I),
    Incid I A a /\ Incid I B a /\ A <> B ->
    exists C : IncPoint I, Incid I C a /\ Bet A B C;

  (* Hilbert 1959 II-2: 给定线段 AB (A ≠ B 共线), A 端延长线上存在 D (Bet D A B). *)
  II_2 : forall (A B : IncPoint I) (a : IncLine I),
    Incid I A a /\ Incid I B a /\ A <> B ->
    exists D : IncPoint I, Incid I D a /\ Bet D A B;

  (* Hilbert 1959 II-3: 共线两点 A,B (A ≠ B) 之间存在第三点 C (Bet A C B). *)
  II_3 : forall (A B : IncPoint I) (a : IncLine I),
    Incid I A a /\ Incid I B a /\ A <> B ->
    exists C : IncPoint I, Incid I C a /\ Bet A C B;

  (* Hilbert 1959 §3: Bet 元性质 *)
  Bet_sym : forall A B C : IncPoint I, Bet A B C -> Bet C B A;
  Bet_nondeg : forall A B C : IncPoint I, Bet A B C -> A <> B /\ B <> C /\ A <> C;
  Bet_trans : forall A B C D : IncPoint I,
    Bet A B C -> Bet B C D -> B <> C -> Bet A B D;

  Pasch : forall A B C P Q : IncPoint I,
    Bet A P C -> Bet B Q C ->
    P <> C -> Q <> C ->
    exists X : IncPoint I, Bet P X Q /\ (Bet A X B \/ Bet B X A);

  (* 同侧: P,Q 在直线 l 的同侧 ⟺ 不存在 l 上的点 X 在 P,Q 之间 *)
  SameSide : IncPoint I -> IncPoint I -> IncLine I -> Prop;

  (* 射线类型 — 定义在 OrderStructure 中 (只需 I + Bet, 不需合同) *)
  Ray : Type;
  ray_origin : Ray -> IncPoint I;
  ray_line : Ray -> IncLine I;
  ray_valid : forall r : Ray, (Incid I) (ray_origin r) (ray_line r);
  OnRay : IncPoint I -> Ray -> Prop
}.

(* ============================================================================ *)
(*  CongruenceStructure: 合同公理 (III-1 ~ III-6)                                *)
(*                                                                            *)
(*  依赖: IncidenceStructure + OrderStructure                                  *)
(*  新增参数: CongSeg (线段合同), CongAng (角合同)                              *)
(*  公理: III-1: 线段迁移 (存在+唯一, 使用 O.Ray/O.OnRay/O.ray_origin)           *)
(*        III-2: 合同传递                                                        *)
(*        III-3: 线段加法                                                        *)
(*        III-4: 合同对称 (独立)                                                 *)
(*        III-5: 合同自反                                                        *)
(*        III-6: 角合同对称                                                      *)
(* ============================================================================ *)

Record CongruenceStructure (I : IncidenceStructure) (O : OrderStructure I)
  : Type := mkCongruence {
  CongSeg : IncPoint I -> IncPoint I -> IncPoint I -> IncPoint I -> Prop;
  CongAng : IncPoint I -> IncPoint I -> IncPoint I -> IncPoint I -> IncPoint I -> IncPoint I -> Prop;

  (* 边 (Side): 线段 AB — 由两个端点确定的几何对象 *)
  Side : Type;
  side_start : Side -> IncPoint I;
  side_end : Side -> IncPoint I;
  side_valid : forall s : Side, side_start s <> side_end s;

  (* 角 (Angle): 由顶点 B 和两条射线 BA, BC 组成的图形 *)
  Angle : Type;
  angle_vertex : Angle -> IncPoint I;        (* 顶点 *)
  angle_side1 : Angle -> Ray I O;             (* 第一条边（射线） *)
  angle_side2 : Angle -> Ray I O;             (* 第二条边（射线） *)
  angle_valid : forall a : Angle,
    (ray_origin I O) (angle_side1 a) = angle_vertex a /\
    (ray_origin I O) (angle_side2 a) = angle_vertex a;

  III1 : forall (A B : IncPoint I) (r : Ray I O),
    A <> B ->
    exists! X : IncPoint I, OnRay I O X r /\ (CongSeg) A B (ray_origin I O r) X;
  III2 : forall A B C D E F : IncPoint I,
    CongSeg A B C D -> CongSeg A B E F -> CongSeg C D E F;
  III3 : forall A B C A' B' C' : IncPoint I,
    @Bet I O A B C -> @Bet I O A' B' C' ->
    CongSeg A B A' B' -> CongSeg B C B' C' ->
    CongSeg A C A' C';
  III4 : forall A B C D : IncPoint I,
    CongSeg A B C D -> CongSeg C D A B;
  III5 : forall A B : IncPoint I, CongSeg A B A B;
  III6 : forall A B C D E F : IncPoint I,
    CongAng A B C D E F -> CongAng D E F A B C;
  III6_reflex : forall A B C : IncPoint I, CongAng A B C A B C;
  (* 角的无向性: ∠BAC ≅ ∠CAB (同一角, 顶点相同, 两边互换) *)
  III6_undirected : forall A B C : IncPoint I,
    CongAng A B C C B A;

  (* SAS 全等公理 (Hilbert 原书 III.7): 两边及其夹角分别相等的两三角形全等 *)
  III7 : forall A B C A' B' C' : IncPoint I,
    A <> B -> B <> C -> A <> C ->
    A' <> B' -> B' <> C' -> A' <> C' ->
    CongSeg A B A' B' -> CongSeg A C A' C' ->
    CongAng B A C B' A' C' ->
    CongSeg B C B' C' /\ CongAng A B C A' B' C' /\ CongAng A C B A' C' B'
}.

(* ============================================================================ *)
(*  ParallelStructure: 第 IV 组公理 — 平行公理 (Hilbert 1959 §6)                 *)
(*                                                                            *)
(*  依赖: IncidenceStructure (需要 Point, Line, Incid)                          *)
(*  新增关系: Parallel (两直线平行)                                              *)
(*                                                                            *)
(*  公理:                                                                      *)
(*    IV-1 (Playfair): 设 a 为一条直线, A 为 a 外的一点。在由 a 和 A           *)
(*      确定的平面上, 至多只有一条直线经过 A 且不与 a 相交。                   *)
(*    IV-2:            平行可传递                                              *)
(*    Parallel_nointersect: 平行 = 不相交 (Hilbert 原始定义)                    *)
(*                                                                            *)
(*  QED 推导:                                                                  *)
(*    Parallel_sym: 平行对称 (从 Parallel_nointersect 导出, 在 Record 外证明)    *)
(* ============================================================================ *)
Record ParallelStructure (I : IncidenceStructure) : Type := mkParallel {
  Parallel : IncLine I -> IncLine I -> Prop;

  (* IV-1 (Playfair): 至多只有一条直线经过 A 且不与 a 相交 *)
  (*   设 a 为一条直线, A 为 a 外的一点。在由 a 和 A 确定的平面上,           *)
  (*   对任意两条经过 A 的直线 b, c, 如果 b 和 c 都不与 a 相交, 则 b = c.  *)
  IV_1 : forall (P : IncPoint I) (a : IncLine I),
    ~ Incid I P a ->
    forall (b c : IncLine I),
      Incid I P b -> Incid I P c ->
      Parallel a b -> Parallel a c ->
      b = c;

  (* IV-2: 平行可传递 *)
  IV_2 : forall a b c : IncLine I,
    Parallel a b -> Parallel b c -> Parallel a c;

  (* 平行 = 不相交 (Hilbert 原始定义) *)
  Parallel_nointersect : forall a b : IncLine I,
    Parallel a b <-> ~ (exists P : IncPoint I, Incid I P a /\ Incid I P b)
}.

(* ============================================================================ *)
(*  Wrapper 函数: 隐式参数风格，用于 theorem 文件的 Section 内                     *)
(*  Bet_ A B C  ≡ Bet I O A B C                                                  *)
(*  CongSeg_ A B C D  ≡ CongSeg I O Cstr A B C D                                 *)
(*  CongAng_ A B C D E F  ≡ CongAng I O Cstr A B C D E F                         *)
(* ============================================================================ *)
Set Implicit Arguments.
Definition Bet_ {I : IncidenceStructure} {O : OrderStructure I}
  (A B C : IncPoint I) : Prop := Bet I O A B C.
Definition CongSeg_ {I : IncidenceStructure} {O : OrderStructure I}
  {Cstr : CongruenceStructure I O} (A B C' D : IncPoint I) : Prop :=
  CongSeg I O Cstr A B C' D.
Definition CongAng_ {I : IncidenceStructure} {O : OrderStructure I}
  {Cstr : CongruenceStructure I O} (A B C' D E F : IncPoint I) : Prop :=
  CongAng I O Cstr A B C' D E F.
Unset Implicit Arguments.
(* ============================================================================ *)
(*  ArchimedesStructure: V-1 (Archimedes 公理)                                   *)
(*                                                                            *)
(*  依赖: IncidenceStructure + OrderStructure + CongruenceStructure              *)
(*  新增类型: Segment (线段)                                                    *)
(*  新增定义: SegmentTimes (n 段累加), SegmentLe (偏序)                          *)
(*  公理: V-1: 对任意两线段 s, t, 存在 n 使 n·s 累加超过 t                      *)
(* ============================================================================ *)

Record ArchimedesStructure (I : IncidenceStructure) (O : OrderStructure I)
                            (C : CongruenceStructure I O) : Type := mkArchimedes {
  Segment : Type;
  segStart : Segment -> IncPoint I;
  segEnd   : Segment -> IncPoint I;
  segValid : forall s : Segment, segStart s <> segEnd s;
  SegmentTimes : Segment -> nat -> Segment;
  SegmentLe : Segment -> Segment -> Prop;

  V1 : forall (s t : Segment),
    exists n : nat, ~ SegmentLe (SegmentTimes s n) t
}.

(* ============================================================================ *)
(*  DedekindStructure: V-2 (戴德金完备性公理)                                    *)
(*                                                                            *)
(*  依赖: IncidenceStructure + OrderStructure                                   *)
(*  新增类型: DedekindCut (戴德金分割 = Lower/Upper 互斥且穷尽)                 *)
(*  公理: V-2: 戴德金分割有唯一分界点 (完备性)                                   *)
(* ============================================================================ *)

Record DedekindStructure (I : IncidenceStructure) (O : OrderStructure I) : Type := mkDedekind {
  DedekindCut : Type;
  cutLower : DedekindCut -> IncPoint I -> Prop;
  cutUpper : DedekindCut -> IncPoint I -> Prop;
  cutValid : forall (cut : DedekindCut) (P : IncPoint I), cutLower cut P <-> ~ cutUpper cut P;

  V2 : forall (cut : DedekindCut) (a : IncLine I),
    (exists P : IncPoint I, (Incid I) P a /\ cutLower cut P) ->
    (exists Q : IncPoint I, (Incid I) Q a /\ cutUpper cut Q) ->
    exists S : IncPoint I, (Incid I) S a /\
      (forall P : IncPoint I, (Incid I) P a -> cutLower cut P -> exists T : IncPoint I, @Bet I O P S T) /\
      (forall Q : IncPoint I, (Incid I) Q a -> cutUpper cut Q -> exists T : IncPoint I, @Bet I O S Q T)
}.

(* ============================================================================ *)
(*  6 层 Hilbert 系统: I + II + III + IV + V_1 (弱) + V_2 (强)                   *)
(* ============================================================================ *)

(* 弱 Hilbert 系统: I + II + III + IV + V_1 (Archimedes) 但不要求 V_2 (完备性) *)
Record WeakHilbertPlane : Type := mkWeakHilbert {
  whI : IncidenceStructure;
  whO : OrderStructure whI;
  whC : CongruenceStructure whI whO;
  whP : ParallelStructure whI;
  whA : ArchimedesStructure whI whO whC  (* shA 也需要 whC, whO 在前, whC 在后 *)

}.

(* 强 Hilbert 系统: 弱 + V_2 (完备性) *)
Record StrongHilbertPlane : Type := mkStrongHilbert {
  shI : IncidenceStructure;
  shO : OrderStructure shI;
  shC : CongruenceStructure shI shO;
  shP : ParallelStructure shI;
  shA : ArchimedesStructure shI shO shC;
  shD : DedekindStructure shI shO
}.

(* shD 满足 shI+shO (与 shC, shA 无关) — V_2 仅依赖 I + II *)

(* Tier-5 净增量: 6 个 Record + 2 个组合 Record                                 *)
(* Tier-6 目标:                                                                  *)
(*   - QPlane.v: 构造 Q² 作为 WeakHilbertPlane 实例 (满足 I-IV + V_1)          *)
(*   - QPlaneNotDedekind.v: 证明 Q² 不满足 V_2 (√2 反例)                       *)
(*   - RealPlane.v: 构造 R² 作为 StrongHilbertPlane 实例                        *)
