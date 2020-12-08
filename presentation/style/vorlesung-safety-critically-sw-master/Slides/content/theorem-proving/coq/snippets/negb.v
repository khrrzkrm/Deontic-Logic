Definition negb : bool -> bool :=
  fun x => match x with
          | true  => false
          | false => true
          end.