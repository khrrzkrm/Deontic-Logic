Lemma p_q_p: forall (P Q: Prop), P -> Q -> P.
Proof.
  intros P Q p q.
  apply p.
Qed.  