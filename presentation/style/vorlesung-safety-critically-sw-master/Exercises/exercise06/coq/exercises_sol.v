Set Implicit Arguments.
Set Contextual Implicit.



(* ex. 5.1 a) *)

(* Example *)
Lemma contradict_imp_any:
  forall (P Q: Prop), P -> (P -> False) -> Q.
Proof.
  intros P Q.
  intros p H1.
  exfalso.
  apply H1.
  exact p.
Qed.

(* Example via proof term *)
Lemma contradict_imp_any':
  forall (P Q: Prop), P -> (P -> False) -> Q.
Proof.
  exact (fun P Q p H1 => match (H1 p) with end).
Qed.  

(* (i) *)
Lemma intro_double_neg:
  forall (P: Prop), P -> ~(~P).
Proof.
  intros P.
  intros p H.
  apply H.
  exact p.
Qed.

(* (i) via proof term *)
Lemma intro_double_neg':
  forall (P: Prop), P -> ~(~P).
Proof.
  exact (fun P p H => H p).
Qed.

(* (ii) *)
Lemma imp_trans:
  forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R.
  intros H1 H2 p.
  apply H2.
  apply H1.
  exact p.
Qed.

(* (ii) via proof term *)
Lemma imp_trans':
  forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  exact (fun P Q R H1 H2 p => H2 (H1 p)).
Qed.

(* ex. 5.1 c) *)

(* (i) *)
Lemma and_comm:
  forall (P Q: Prop), P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  destruct H as [p q].
  split.
  - exact q.
  - exact p.
Qed.

(* (i) via proof term *)
Lemma and_comm':
  forall (P Q: Prop), P /\ Q -> Q /\ P.
Proof.
  exact (fun P Q H => match H with conj p q => conj q p end).
Qed.

(* (ii) *)
Lemma and_distr:
  forall (P Q R: Prop), P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  intros P Q R [p qr].
  destruct qr as [q | r].
  - left. split.
    + exact p.
    + exact q.
  - right. split.
    + exact p.
    + exact r.
Qed.

(* (ii) via proof term *)
Lemma and_distr':
  forall (P Q R: Prop), P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  exact (fun P Q R H => match H with conj p qr =>
                          match qr with | or_introl q => or_introl (conj p q)
                                   | or_intror r => or_intror (conj p r)
                          end
                        end).
Qed.




(* ex. 5.2 *)

Inductive option (A:Type) : Type :=
  | some : A -> option A
  | none : option A.

(* (i) *)
Definition pred_opt (n: nat): option nat :=
  match n with | O => none
               | S n => some n end.

(* (ii) *)
Definition pred (n: nat): nat :=
  match n with | O => O
               | S n => n end.         

(* (iii) *)
Fixpoint minus (x y: nat): option nat :=
  match (x, y) with | (x, O) => some x
               | (S x, S y) => minus x y
               | _ => none                                  
  end.

(* (iv) *)
Definition is_none (X: Type) (x: option X): bool :=
  match x with | none => true
               | some x  => false end.


(* (v) *)
Definition head (X: Type) (xs: list X): option X :=
  match xs with | nil => none
           | cons x _ => some x end.




(* ex. 5.3 *)

(* (i) *)
Lemma spec_head (X: Type):
  forall (x: X) (xs: list X), head (cons x xs) = some x.
Proof.
  intros x xs. simpl. reflexivity.
Qed.

(* (ii) *)
Lemma spec_pred:
  forall (n: nat), S (pred n) = n \/ n = 0.
Proof.
  intros n. destruct n.
  - right. reflexivity.
  - simpl. left. reflexivity.
Qed.

(* (iii) *)
Lemma plus_assoc: forall (a b c: nat), (a + b) + c = a + (b + c).
Proof.
  intros a b c. induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa.
    reflexivity.
Qed.

(* (iv) *)
Lemma minus_none:
  forall (m n: nat), minus m n = none \/ minus n m = none \/ m = n.
Proof.
  intros m. induction m.
  - intros n.
    destruct n.
    + right. right. reflexivity.
    + left. simpl. reflexivity.
  - intros n. destruct n.
    +right. left. auto.
    + simpl. specialize (IHm n).
      destruct IHm.
      * left. exact H.
      * destruct H.
        right. left. exact H.
        right. right. rewrite H. reflexivity.
Qed.
