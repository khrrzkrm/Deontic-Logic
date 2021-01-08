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
