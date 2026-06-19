Require Import Reals Lra Vector.
Open Scope R_scope.
Lemma test2 (n : nat) (x y : t R (S n)) 
  (Hsum : -(Vector.hd x - Vector.hd y) + vr_distance (Vector.tl x) (Vector.tl y) = 0)
  (Hnonneg : 0 <= vr_distance (Vector.tl x) (Vector.tl y))
  (Hneg : Vector.hd x - Vector.hd y < 0) : False.
Proof.
  lra.
Qed.
