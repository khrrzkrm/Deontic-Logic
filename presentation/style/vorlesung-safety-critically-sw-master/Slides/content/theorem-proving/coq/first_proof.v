Theorem t_and_t: True /\ True.
Proof.
  apply conj.
  - apply I.
  - apply I.
Qed.



Definition f_or_t: False \/ True :=
  or_intror I.

Lemma f_or_t2: False \/ True.
  or_intror I.