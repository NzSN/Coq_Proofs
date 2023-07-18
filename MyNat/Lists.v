Require Import LF.MyNat.Basics.

Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).
Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
    | (x,y) => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
    | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (x,y) => (y,x)
  end.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
Notation "x :: l" := (cons x l)
                      (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | O => nil
    | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
    | nil => default
    | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => match h with
                | O => nonzeros t
                | S n' => S n' :: (nonzeros t)
              end
  end.

Example test_nonzeros:
  nonzeros [O;S O;O;S (S O);S (S (S O)); O; O] = [S O; S (S (O)); S (S (S O))].
Proof.
  simpl.
  reflexivity.
Qed.

Fixpoint alternate (l1 l2: natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => match l2 with
                | nil => h :: t
                | h' :: t' => h :: h' :: (alternate t t')
              end
  end.

Example test_alternate1:
  alternate [S O; S (S O); S (S (S O))]
            [S (S (S (S O))); S (S (S (S (S O)))); S (S (S (S (S (S O)))))] =
    [S O; S (S (S (S O))); S (S O); S (S (S (S (S O)))); S (S (S O));
     S (S (S (S (S (S O)))))].
Proof.
  simpl.
  reflexivity.
Qed.

Example test_alternate2:
  alternate [S O] [S (S (S (S O))); S (S (S (S (S O)))); S (S (S (S (S (S O)))))] =
    [S O; S (S (S (S O))); S (S (S (S (S O)))); S (S (S (S (S (S O)))))].
Proof.
  simpl.
  reflexivity.
Qed.

Example test_alternate3:
  alternate [S O; S (S O); S (S (S O))] [S (S (S (S O)))] =
    [S O; S (S (S (S O))); S (S O); S (S (S O))].
Proof.
  simpl.
  reflexivity.
Qed.

Example test_alternate4:
  alternate [] [S (S O); S O] = [S (S O); S O].
Proof.
  simpl.
  reflexivity.
Qed.

Definition bag := natlist.

End NatList.

Import NatList.

(* NatList Theorems *)
Theorem surjective_pairing': forall p : natprod,
    p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
    (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
    fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.
