Lemma dem:
  forall (P Q: Prop), ~(P /\ Q) -> (~P \/ ~Q).
Proof.
  intros P Q H.
Admitted.

Lemma dem2:
  forall (P Q: Prop), ~(P \/ Q) -> (~P /\ ~Q).
Proof.
  intros P Q H.
  split.
  - intros p. apply H. left. exact p.
  - intros q. apply H. right. exact q.
Qed.