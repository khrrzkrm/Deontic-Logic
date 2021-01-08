Set Implicit Arguments.
Set Contextual Implicit.

Inductive option (A:Type) : Type :=
  | some : A -> option A
  | none : option A.


Definition pred_opt (n: nat): option nat :=
  match n with | O => none
               | S n => some n end.


Definition pred (n: nat): nat :=
  match n with | O => O
               | S n => n end.         


Definition is_none (X: Type) (x: option X): bool :=
  match x with | none => true
               | some x  => false end.

Definition is_some (X: Type) (x: option X): bool := negb (is_none x).

Fixpoint minus (x y: nat): option nat :=
  match (x, y) with | (x, O) => some x
               | (S x, S y) => minus x y
               | _ => none                                  
  end.

Definition head (X: Type) (xs: list X): option X :=
  match xs with | nil => none
           | cons x _ => some x end.



Lemma spec_head (X: Type):
  forall (x: X) (xs: list X), head (cons x xs) = some x.
Proof.
  intros x xs. simpl. reflexivity.
Qed.

Lemma minus_none:
  forall (m n: nat), minus m n = none \/ minus n m = none \/ m = n.
Proof.
  intros m. induction m.
  - intros n.
    destruct n.
    + auto.
    + left. auto.
  - intros n. destruct n.
    + auto.
    + simpl. specialize (IHm n).
      destruct IHm; auto. destruct H; auto.
Qed.

Lemma pred_lem:
  forall (n: nat), S (pred n) = n \/ n = 0.
Proof.
  intros n. destruct n.
  - auto.
  - simpl. left. reflexivity.
Qed.

