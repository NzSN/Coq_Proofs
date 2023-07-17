Module Number.

Inductive nat: Type :=
  | O
  | S (n : nat).

Definition pred (n : nat): nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
   end.

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat): nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m: nat): nat :=
  match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
  end.

Fixpoint eqb (n m: nat): bool :=
  match n with
    | O => match m with
            | O => true
            | S m' => false
          end
    | S n' => match m with
              | O => false
              | S m' => eqb n' m'
             end
  end.

Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                      : nat_scope.
Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70): nat_scope.
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

(* Exercise 1 *)
Theorem plus_id_exercise: forall n m o : nat,
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

(* Exercise 1 End*)

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
  intros n.
  destruct n as [| n'] eqn:E.

  (* Case n = O *)
  - simpl.
    reflexivity.

  (* Case n = S n' *)
  - simpl.
    reflexivity.
Qed.





End Number.
