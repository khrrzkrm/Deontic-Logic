Fixpoint plus (m n: nat) : nat :=
  match m with
  | O    => n
  | S m' => S (plus m' n)
  end.