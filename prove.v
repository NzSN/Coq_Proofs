Require Import Bool.

Definition eqb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Definition Is_true (b:bool) :=
  match b with
    | true => True
    | false => False
  end.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    simpl.
    exact I.

    simpl.
    exact I.
Qed.


Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
  intros A B.
  intros proof_of_A.
  pose (proof_of_A_or_B := or_introl proof_of_A : A \/ B).
  exact proof_of_A_or_B.
Qed.

Theorem right_or : (forall A B : Prop, B -> A \/ B).
Proof.
  intros A B.
  intros proof_of_B.
  refine (or_intror _).
    exact proof_of_B.
Qed.

Theorem or_commutes : (forall A B, A \/ B -> B \/ A).
Proof.
  intros A B.
  intros A_or_B.
  case A_or_B.
    intros proof_of_A.
    refine(or_intror _).
    exact proof_of_A.
  
    intros proof_of_B.
    refine(or_introl _).
    exact proof_of_B.
Qed.

Theorem both_and : (forall A B : Prop, A -> B -> A /\ B).
Proof.
  intros A B.
  intros proof_of_A proof_of_B.
  refine (conj _ _).
    exact proof_of_A.
    exact proof_of_B.
Qed.

Theorem and_commutes : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  case A_and_B.
    intros proof_of_A.
    intros proof_of_B.
    refine (conj _ _).
      exact proof_of_B.
      exact proof_of_A.
Qed.

Theorem and_commutes__again : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  destruct A_and_B as [ proof_of_A proof_of_B].
  refine (conj _ _).
    exact proof_of_B.

    exact proof_of_A.
Qed.

(*
Definition iff (A B:Prop) := (A -> B) /\ (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.
*)

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine(conj _ _).
    intros H.
    case a, b.
      (* True True *)
      simpl.
      refine (or_introl _).
      exact I.
      (* True False *)
      simpl.
      refine(or_introl _).
      exact I.
      (* False True *)
      simpl.
      refine(or_intror _).
      exact I.
      (* False False *)
      simpl in H.
      case H.

    intros H.
    case a, b.
      (* T, T *)
      simpl.
      exact I.
      (* T, F *)
      simpl.
      exact I.
      (* F, T *)
      simpl.
      exact I.
      (* F, F *)
      simpl.
      case H.
        intros A.
        simpl in A.
        case A.

        intros B.
        simpl in B.
        case B.
Qed.

Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine(conj _ _).
    intros H.
    case a, b.
      (* T, T *)
      simpl.
      exact (conj I I).
      (* T, F *)
      simpl.
      case H.
      (* F, T *)
      simpl.
      case H.
      (* F, F *)
      simpl.
      case H.

    intros H.
    case a, b.
      (* T, T *)
      simpl.
      exact I.
      (* T, F *)
      simpl in H.
      destruct H as [A B].
      case B.
      (* F, T *)
      simpl in H.
      destruct H as [A B].
      case A.
      (* F, F *)
      simpl in H.
      destruct H as [A B].
      case A.
Qed.

Theorem backward_small : (forall A B : Prop, A -> (A->B)->B).
Proof.
 intros A B.
 intros proof_of_A A_implies_B.
 refine (A_implies_B _).
   exact proof_of_A.
Qed.

Theorem thm_true_imp_false : ~(True -> False).
Proof.
  intros T_implies_F.
  refine (T_implies_F _).
    exact I.
Qed.

Theorem negb_is_not : (forall a, Is_true (negb a) <-> (~(Is_true a))).
Proof.
  intros a.
  unfold iff.
  refine(conj _ _).
    case a.
      (* True *)
      simpl.
      intros proof_of_False.
      case proof_of_False.
      (* False *)
      simpl.
      intros proof_of_True.
      unfold not.
      intros proof_of_False.
      case proof_of_False.
    case a.
      (* True *)
      simpl.
      unfold not.
      intros T_implies_F.
      refine(T_implies_F _).
        exact I.
      (* False *)
      simpl.
      unfold not.
      intros F_implies_F.
      exact I.
Qed.


(*
Inductive ex (A:Type) (P:A -> Prop) : Prop :=
  ex_intro : forall x:A, P x -> ex (A:=A) P.

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
*)

Definition basic_predicate :=
  (fun a => Is_true (andb a true)).

Theorem thm_exists_basics : (ex basic_predicate).
Proof.
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
    simpl.
    exact I.
Qed.

