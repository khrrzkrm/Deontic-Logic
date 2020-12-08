Lemma O_plus_n: forall (n: nat), 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Lemma m_plus_O: forall (m: nat), m + 0 = m.
Proof.
  intros m.
  induction m.
  - simpl. reflexivity.
  - simpl. rewrite IHm. reflexivity.
Qed.

Lemma m_plus_S: forall (m n: nat), m + (S n) = S (m + n).
Proof.
  intros m n.
  induction m.
  - simpl. reflexivity.
  - simpl. rewrite IHm. reflexivity.
Qed.    
  
Lemma plus_comm: forall (m n: nat), m + n = n + m.
Proof.
  intros m.
  induction m.
  - intros. rewrite m_plus_O.
    simpl. reflexivity.
  - intros n. simpl. rewrite IHm.
    rewrite m_plus_S. reflexivity.
Qed.