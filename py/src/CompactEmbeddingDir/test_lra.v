Require Import Reals Lra.
Open Scope R_scope.
Lemma test (a b : R) (Hsum : -a + b = 0) (Hnonneg : 0 <= b) (Hneg : a < 0) : False.
Proof.
  lra.
Qed.
