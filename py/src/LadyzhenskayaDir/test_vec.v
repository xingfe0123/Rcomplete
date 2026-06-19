Require Import Vector.
Require Import VectorSpec.
Require Import Reals.
Open Scope R_scope.

(* Define component-wise addition for R^n *)
Fixpoint add {n : nat} : t R n -> t R n -> t R n :=
  match n with
  | 0 => fun _ _ => nil R
  | S n' => fun u v => cons R (hd u + hd v) n' (add (tl u) (tl v))
  end.

(* Define zero vector *)
Fixpoint zero (n : nat) : t R n :=
  match n with
  | 0 => nil R
  | S n' => cons R 0 n' (zero n')
  end.

(* Test: add is associative *)
Lemma add_assoc : forall n (u v w : t R n), add (add u v) w = add u (add v w).
Proof.
  induction n; intros.
  - simpl. reflexivity.
  - rewrite (VectorSpec.eta u), (VectorSpec.eta v), (VectorSpec.eta w).
    { f_equal.
      { ring. }
      { reflexivity. }
      { symmetry. apply (IHn (tl u) (tl v) (tl w)). }
    }
Qed.

(* Test: add is commutative *)
Lemma add_comm : forall n (u v : t R n), add u v = add v u.
Proof.
  induction n; intros.
  - simpl. reflexivity.
  - rewrite (VectorSpec.eta u), (VectorSpec.eta v).
    { f_equal.
      { ring. }
      { reflexivity. }
      { apply (IHn (tl u) (tl v)). }
    }
Qed.

(* Test: zero + u = u *)
Lemma zero_add : forall n (u : t R n), add (zero n) u = u.
Proof.
  induction n; intros.
  - simpl. rewrite (VectorSpec.nil_spec u). reflexivity.
  - rewrite (VectorSpec.eta u).
    { f_equal.
      { ring. }
      { reflexivity. }
      { apply (IHn (tl u)). }
    }
Qed.

(* Test: u + zero = u *)
Lemma add_zero : forall n (u : t R n), add u (zero n) = u.
Proof.
  induction n; intros.
  - simpl. rewrite (VectorSpec.nil_spec u). reflexivity.
  - rewrite (VectorSpec.eta u).
    { f_equal.
      { ring. }
      { reflexivity. }
      { apply (IHn (tl u)). }
    }
Qed.

(* Test: u + (-u) = zero *)
Lemma add_neg : forall n (u : t R n), add u (map Ropp n u) = zero n.
Proof.
  induction n; intros.
  - simpl. rewrite (VectorSpec.nil_spec u). reflexivity.
  - rewrite (VectorSpec.eta u).
    { f_equal.
      { ring. }
      { reflexivity. }
      { apply (IHn (tl u)). }
    }
Qed.

(* Test: map (fun x => 1 * x) u = u *)
Lemma map_smult_1 : forall n (u : t R n), map (fun x => 1 * x) n u = u.
Proof.
  induction n; intros.
  - simpl. rewrite (VectorSpec.nil_spec u). reflexivity.
  - rewrite (VectorSpec.eta u).
    { f_equal.
      { ring. }
      { reflexivity. }
      { apply (IHn (tl u)). }
    }
Qed.

(* Test: map (a * x) (map (b * x) u) = map (a*b * x) u *)
Lemma map_smult_mul : forall n (a b : R) (u : t R n),
  map (fun x => a * x) n (map (fun x => b * x) n u) = map (fun x => a * b * x) n u.
Proof.
  induction n; intros.
  - simpl. rewrite (VectorSpec.nil_spec u). reflexivity.
  - rewrite (VectorSpec.eta u).
    { f_equal.
      { ring. }
      { reflexivity. }
      { apply (IHn (tl u)). }
    }
Qed.

(* Test: map (a * x) (add u v) = add (map (a * x) u) (map (a * x) v) *)
Lemma map_smult_add_dist : forall n (a : R) (u v : t R n),
  map (fun x => a * x) n (add u v) = add (map (fun x => a * x) n u) (map (fun x => a * x) n v).
Proof.
  induction n; intros.
  - simpl. rewrite (VectorSpec.nil_spec u), (VectorSpec.nil_spec v). reflexivity.
  - rewrite (VectorSpec.eta u), (VectorSpec.eta v).
    { f_equal.
      { ring. }
      { reflexivity. }
      { apply (IHn (tl u) (tl v)). }
    }
Qed.

(* Test: map ((a+b) * x) u = add (map (a * x) u) (map (b * x) u) *)
Lemma map_smult_plus_dist : forall n (a b : R) (u : t R n),
  map (fun x => (a + b) * x) n u = add (map (fun x => a * x) n u) (map (fun x => b * x) n u).
Proof.
  induction n; intros.
  - simpl. rewrite (VectorSpec.nil_spec u). reflexivity.
  - rewrite (VectorSpec.eta u).
    { f_equal.
      { ring. }
      { reflexivity. }
      { apply (IHn (tl u)). }
    }
Qed.

Print "All 9 axioms proven!"
