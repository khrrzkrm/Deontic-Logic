Set Implicit Arguments.
Set Contextual Implicit.

Inductive list (X: Type) : Type :=
| nil:  list X
| cons: X -> list X -> list X.

Definition myt := cons 3 (nil).


Definition list_param_ind:
  forall (X: Type) (P: list X -> Prop),
    P (nil X) ->
    (forall (x: X) (xr: list X), P xr -> P (cons X x xr)) ->
    forall (xs: list X), P xs :=
  fun X P H1 H2 => fix f xs := match xs with
                               | nil _ => H1
                               | cons _ x xr => H2 x xr (f xr) end.

(* This direction is easy... *)
Lemma list_nonparam_ind: forall P : (forall T : Type, list T -> Prop),
      (forall X : Type, P X (nil X)) ->
      (forall (X : Type) (x : X) (l : list X), P X l -> P X (cons X x l)) ->
      forall (T : Type) (l : list T), P T l .
Proof.
  intros P H1 H2 T l.
  apply list_ind.
  - (* base *)
    auto.
  - (* step *)
    auto.
Qed.

