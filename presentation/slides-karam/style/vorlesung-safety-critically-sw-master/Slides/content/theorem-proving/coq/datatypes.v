(*  Vectors *)

Inductive vector (X: Type): nat -> Type :=
| nil:  vector X 0
| cons: forall m, X -> vector X m -> vector X (S m).



Fixpoint app {X: Type} {m n:nat} (v1: vector X m) (v2: vector X n): vector X (m+n) :=
  match v1 with
  | nil _ => v2
  | cons _ m' x v1' => cons X (m' + n) x (app v1' v2)
  end.
                                        

Definition myvec := cons nat 0 3 (nil nat).
