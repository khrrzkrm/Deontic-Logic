Definition negb (x: bool) : bool :=
  match x with
  | true  => false
  | false => true
  end.