Set Implicit Arguments.
Set Contextual Implicit.

Inductive even : nat -> Prop :=
| evenO:  even O
| evenSS: forall (n: nat), even n ->
                      even (S(S n)).

Definition two_even: even 2 := evenSS (evenO).