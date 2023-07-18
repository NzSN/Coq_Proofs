Require Export LF.MyNat.Basics.

Theorem plus_id_example: forall n m:nat,
    n = m -> n + n = m + m.
Proof.
  intros n m.
  intros P.
  rewrite -> P.
  reflexivity.
  Qed.

Theorem plus_O_n: forall n : nat, O + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
  Qed.

Theorem plus_1_n: forall n : nat, S O + n = S n.
Proof.
  intros n.
  simpl.
  reflexivity.
  Qed.

Theorem plus_id: forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros P1.
  intros P2.
  rewrite -> P1.
  rewrite -> P2.
  reflexivity.
  Qed.

Theorem mult_0_plus: forall n m: nat,
    (O + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
  Qed.

Theorem mult_S_1: forall n m: nat,
    m = S n -> m * ((S O) + n) = m * m.
Proof.
  intros n m.
  intros P1.
  rewrite -> plus_1_n.
  rewrite -> P1.
  reflexivity.
  Qed.

(* Proof by Case Analysis *)
Theorem plus_1_neq_0_firsttry: forall n : nat,
    (n + S O) =? S O = false.
Proof.
  intros n.
  simpl.
  Abort.

Theorem plus_1_neq_0 : forall n : nat,
    (n + S O) =? O = false.
Proof.
  intros [|n].

  (* Case n = O *)
  - simpl.
    reflexivity.

  (* Case n = S n' *)
  - simpl.
    reflexivity.
Qed.

Theorem negb_involutive: forall b : bool,
    negb (negb b) = b.
Proof.
  intros b.
  destruct b eqn:E.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }
Qed.

Theorem andb_commutative'':
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_n_O: forall n:nat,
    n = n + O.
Proof.
  intros.
  induction n as [|n' An'].
  - reflexivity.
  - simpl.
    rewrite <- An'.
    reflexivity.
Qed.

Theorem minus_diag: forall n,
    minus n n = O.
Proof.
  intros n.
  induction n as [|n' An'].

  - simpl.
    reflexivity.

  - simpl.
    rewrite -> An'.
    reflexivity.
Qed.
