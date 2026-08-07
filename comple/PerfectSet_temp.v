  (* Find N_max = max(N_0, ..., N_{n_dim-1}) *)
  assert (Hmax : exists N_max : nat, forall i : nat, forall Hi : Nat.lt i n_dim,
    forall n : nat, Nat.le N_max n ->
      Rabs (s n i - proj1_sig (Hlimits i Hi)) < eps / INR (n_dim + 1)).
  { (* Standard result: finite set of naturals has a maximum *)
    assert (Hall : forall n : nat, forall (f : nat -> Prop), (forall i, Nat.lt i n -> f i) -> forall i, Nat.lt i n -> f i).
    { intros n f H i Hi. apply H. exact Hi. }
    (* Use constructive choice to extract all N_i and compute max *)
    assert (Hex : forall i : nat, Nat.lt i n_dim -> exists n : nat, forall n0 : nat, Nat.le n n0 ->
      Rabs (s n0 i - proj1_sig (Hlimits i H)) < eps / INR (n_dim + 1)).
    { intros i Hi. apply HNs. exact Hi. }
    (* Since we have existence for each i, we can use choice to get a function *)
    assert (Hf : { f : nat -> nat | forall i : nat, Nat.lt i n_dim -> forall n : nat, Nat.le (f i) n ->
      Rabs (s n i - proj1_sig (Hlimits i (Nat.lt_trans _ _ _ i n_dim (Nat.lt_succ_diag_r _) (fun j Hj => Hj)))) < eps / INR (n_dim + 1)) }).
    Admitted.
    (*
    destruct Hf as [f Hf].
    exists (seq_max f n_dim).
    intros i Hi n Hn.
    unfold seq_max in Hn.
    apply Hf.
    *)
    Admitted.
  }
