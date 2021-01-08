Set Implicit Arguments.
Set Contextual Implicit.



(* (i) *)
Lemma intro_double_neg:
  forall (P: Prop), P -> ((P -> False) -> False).
Proof.
  intro P.
  intro p.
  intro.
  apply H.
  exact p.
  (* INSERT HERE *)
Qed.

Print intro_double_neg.

(*
(* (i) via proof term *)
Lemma intro_double_neg':
  forall (P: Prop), P -> ~(~P).
Proof.
  exact ( (* INSERT HERE *) ).
Qed.

(* ex. 5.1 a) *)



(* Example *)
Lemma contradict_imp_any:
  forall (P Q: Prop), P -> (P -> False) -> Q.
Proof.
  
Qed.

(* Example via proof term *)
Lemma contradict_imp_any':
  forall (P Q: Prop), P -> (P -> False) -> Q.
Proof.
  exact ( (* INSERT HERE *) ).
Qed.  



(* (ii) *)
Lemma imp_trans:
  forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  (* INSERT HERE *)
Qed.

(* (ii) via proof term *)
Lemma imp_trans':
  forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  exact ( (* INSERT HERE *) ).
Qed.
*)
(* ex. 5.1 c) *)

(* (i) *)
Lemma and_comm:
  forall (P Q: Prop), P /\ Q -> Q /\ P.
Proof.
  intros P Q.
  intro H.
  split.
  - destruct H.
    exact H0.
  - tauto.
Qed.

Print and_comm.

(* (i) via proof term *)
Lemma and_comm':
  forall (P Q: Prop), P /\ Q -> Q /\ P.
Proof.
  exact ( (* INSERT HERE *) ).
Qed.

(* (ii) *)
Lemma and_distr:
  forall (P Q R: Prop), P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  (* INSERT HERE *)
Qed.

(* (ii) via proof term *)
Lemma and_distr':
  forall (P Q R: Prop), P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  exact ( (* INSERT HERE *) ).
Qed.




(* ex. 5.2 *)

Inductive option (A:Type) : Type :=
  | some : A -> option A
  | none : option A.

(* (i) *)
Definition pred_opt (n: nat): option nat :=
  (* INSERT HERE *)

(* (ii) *)
Definition pred (n: nat): nat :=
  (* INSERT HERE *)      

(* (iii) *)
Fixpoint minus (x y: nat): option nat :=
  (* INSERT HERE *)

(* (iv) *)
Definition is_none (X: Type) (x: option X): bool :=
  (* INSERT HERE *)

(* (v) *)
Definition head (X: Type) (xs: list X): option X :=
  (* INSERT HERE *)




(* ex. 5.3 *)

(* (i) *)
Lemma spec_head (X: Type):
  forall (x: X) (xs: list X), head (cons x xs) = some x.
Proof.
  (* INSERT HERE *)
Qed.

(* (ii) *)
Lemma spec_pred:
  forall (n: nat), S (pred n) = n \/ n = 0.
Proof.

Qed.

(* (iii) *)
Lemma plus_assoc: forall (a b c: nat), (a + b) + c = a + (b + c).
Proof.
  intros a b c. induction a.
  (* INSERT HERE *)
Qed.

(* (iv) *)
Lemma minus_none:
  forall (m n: nat), minus m n = none \/ minus n m = none \/ m = n.
Proof.
  intros m. induction m.
  (* INSERT HERE *)
  (* There is one more tactic you need here:
       specialize (H n)
     This specializes a hypothesis
       H: forall (m: nat), P m
     with
       n: nat
     resulting in
       H: P n
     You can see it as feeding n as an argument to H.
  *) 
Qed.