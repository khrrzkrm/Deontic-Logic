(*  Lists *)

Inductive list : Type -> Type :=
| nil:  forall (X: Type), list X
| cons: forall (X: Type), X -> list X -> list X.

(* Can we prove the induction lemma of param list? *)

Lemma list_param_ind:
  forall (X: Type) (P: list X -> Prop),
    P (nil X) ->
    (forall (x: X) (xr: list X), P xr -> P (cons X x xr)) ->
    forall (xs: list X), P xs.
Proof.
  intros X P H1 H2. intros xs.
  induction xs.
  - apply H1.
  - apply H2. apply IHxs.
    + apply H1.
    + apply H2.
Qed.

Lemma list_param_ind':
  forall (X: Type) (P: list X -> Prop),
    P (nil X) ->
    (forall (x: X) (xr: list X), P xr -> P (cons X x xr)) ->
    forall (xs: list X), P xs.
Proof.
  intros X P H1 H2. intros xs.
  pose (ind := list_ind).
  pose (Q := (fun (X0 : Type) (xs0 : list X0) =>
                forall P0 : list X0 -> Prop, P0 (nil X0) -> (forall (x : X0) (xr : list X0), P0 xr -> P0 (cons X0 x xr)) -> P0 xs0)).
  specialize (ind Q).
  subst Q. simpl in ind.
  apply ind.
  - intros X'. (* now prove base case *)
    intros. auto.
  - intros X' x' l' IH. (* now prove step *)
    intros. apply H0.  apply IH; auto.
  - auto.
  - intros.  apply H2.  auto.
Qed.
