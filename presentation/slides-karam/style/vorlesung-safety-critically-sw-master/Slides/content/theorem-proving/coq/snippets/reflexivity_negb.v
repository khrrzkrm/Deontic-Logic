Definition negb : bool -> bool :=
  fun x => match x with
          | true  => false
          | false => true
           end.

Lemma negb_tf: negb true = false.
Proof.
  simpl.
  reflexivity.
Qed.