Definition plus : nat -> nat -> nat :=
  fix f (m n: nat) :=
    match m with
    | O    => n
    | S m' => S (f m' n)
    end.