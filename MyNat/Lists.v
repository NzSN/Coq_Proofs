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

End NatList.
