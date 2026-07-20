From Stdlib Require Import QArith QOrderedType.
Open Scope Q_scope.

Lemma test1 : (0 : Q) < (1 : Q).
Proof. apply Qlt_0_1. Qed.

Lemma test2 : (0 : Q) <= (1 : Q).
Proof. apply Qlt_le_weak. exact Qlt_0_1. Qed.

Lemma test3 : forall x : Q, 0 <= x -> x * x < 2 -> x < 2.
Proof.
  intros x Hx Hxx.
  destruct (Qlt_le_dec x 2) as [Hlt | Hle].
  - exact Hlt.
  - exfalso.
    assert (H2 : 4 <= x * x).
    { assert (H3 : 2 <= x) by (apply Qlt_le_weak; exact (Qle_not_lt 2 x Hle)).
      assert (H4 : 0 <= 2) by (apply Qlt_le_weak; exact Qlt_0_1).
      exact (Qmult_le_compat 2 x H4 Hx H3). }
    exact (Qle_not_lt _ _ H2 Hxx).
Qed.
