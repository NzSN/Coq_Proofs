Require Export Basics.

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
