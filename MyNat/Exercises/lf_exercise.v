From LF Require Import MyNat.Basics.
From LF Require Import MyNat.Proofs.

(* Proof by induction *)
Theorem mult_0_r: forall n : nat,
    n * O = O.
Proof.
  intros.
  induction n as [|n' An'].

  - reflexivity.
  - simpl.
    rewrite -> An'.
    reflexivity.
Qed.

Theorem plus_n_Sm: forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' An'].
  (* Base Case of Induction on n *)
  {
    simpl.
    reflexivity.
  }

  (* m' Assumation of Induction on n *)
  {
    simpl.
    rewrite -> An'.
    reflexivity.
  }
Qed.

Theorem plus_comm: forall n m : nat,
    n + m = m + n.
Proof.
  intros n m.

  induction n as [|n' An'].

  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - simpl.
    rewrite -> An'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.

  induction n as [|n' An'].

  - simpl.
    reflexivity.

  - simpl.
    rewrite -> An'.
    reflexivity.
Qed.

(* Proof property of this  *)
Fixpoint double (n:nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n.

  induction n as [|n' An'].

  - simpl.
    reflexivity.

  - simpl.
    rewrite -> An'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  intros n.

  induction n as [|n' An'].
  - simpl.
    reflexivity.

  - rewrite -> An'.
    simpl.
    rewrite -> negb_involutive.
    reflexivity.
Qed.

(* Proffs Within Proofs *)
Theorem mult_O_plus' : forall n m : nat,
    (O + n) * m = n * m.
Proof.
  intros n m.
  assert (H: O + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange: forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.
