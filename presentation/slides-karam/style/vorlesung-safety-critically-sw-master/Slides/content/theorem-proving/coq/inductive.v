Require Import Omega.

Inductive zero : nat -> Prop :=
| zeroI : zero 0.

Lemma zero_iff x:
  zero x <-> x = 0.
Proof.
  split; intro H.
  - destruct H. reflexivity.
  - rewrite H. constructor.
Qed.

(* Linearize non-parametric arguments *)
Goal not (zero 2).
Proof.
  intros A.
  remember 2.
  destruct A. discriminate Heqn.
Qed.

(* Even *)
Inductive even: nat -> Prop :=
| evenO  : even O
| evenSS n : even n -> even (S(S n)).

Inductive even' (x: nat): Prop :=
| even'O : x = O -> even' x
| even'SS y : x = S (S y) -> even' y -> even' x.

Lemma even_iff x:
  even x <-> exists k, x = 2*k.
Proof.
  split; intro H.
  - induction H.
    + exists O. tauto.
    + destruct IHeven. subst. exists (S x). omega.
  - destruct H as (n, H). subst. induction n.
    + constructor.
    + replace (2 * S n) with (S (S (2*n))) by omega.
      now constructor.
Qed.

Lemma even_iff_2 x:
  even x <-> even' x.
Proof.
  split; intro H.
  - induction H.
    + now constructor.
    + apply even'SS with (y := n).
      * auto.
      * auto.
  - revert H. revert x. apply even'_ind.
    + intros x H1. subst. constructor.
    + intros. subst. constructor. auto.
Qed.

(* Eq *)
Inductive myeq (X: Type) (x: X): X -> Prop :=
| myeq_refl: myeq X x x.

Inductive myeqnon (X: Type): X -> X -> Prop :=
| meqnon_refl x: myeqnon X x x.

Lemma myeq_myeqnon X (x: X):
  myeq X x x <-> myeqnon X x x.
Proof.
  split; intros H.
  - constructor.
  - constructor.