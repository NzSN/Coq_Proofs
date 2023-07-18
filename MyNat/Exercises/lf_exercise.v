Require Import LF.MyNat.Basics.

(* Proof by induction *)
Theorem mult_0_r: forall n : nat,
    n * O = O.
Proof.
  Admitted.

Theorem plus_n_Sm: forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  Admitted.

Theorem plus_comm: forall n m : nat,
    n + m = m + n.
Proof.
  Admitted.

Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  Admitted.
