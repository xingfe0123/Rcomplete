Require Import Reals.
Open Scope R_scope.
Lemma test : forall a b c : R, a + (b + c) = (a + b) + c.
Proof.
  intros.
  ring.
Qed.
