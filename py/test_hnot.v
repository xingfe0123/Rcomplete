
Require Import RicciFlow.HopfDir.Hopf.

Goal False.
Proof.
  apply (interior_max_implies_contradiction (fun _ => 0%R) 0 0 0%R).
  intros Hnot.
  unfold not in Hnot.
  Check Hnot.
