(* Let's start with defining booleans *)
Fixpoint nonterm (n: nat): nat := nonterm n.

Definition prove_false: False := match (nonterm 42) with end. 


Inductive bool : Type :=
| true  : bool
| false : bool.

(* ... and some functions *)

Definition negb (x : bool) : bool :=
  match x with
  | true  => false
  | false => true
  end.

Definition andb : bool -> bool -> bool :=
  fun x y => match x with
             | true => match y with
                       | true => true
                       | false => false end
             | false => false end.

(* Just notation for the last definition. It is therefore the *same* definition: *)
Definition andb' (x y: bool) : bool :=
  match x with
  | true => match y with
            | true => true
            | _ => false end
  | _ => false end.


(* Again, just notation for the *same* definition: *)
Definition andb'' (x: bool) (y: bool) : bool :=
  match x with
  | true => match y with
            | true => true
            | _ => false end
  | _ => false end.

(* This definition introduces a pair (x, y), so it is not the *same* definition.
   Semantically though it is equivalent: *)
Definition andb''' (x y: bool) : bool :=
  match (x, y) with
  | (true, true) => true
  | _ => false end.

(*
  Exercise: Define the functions
     impb: bool -> bool -> bool
  and
     orb: bool -> bool -> bool
 *)





(* We can ask Coq to infer the type of "negb true" *)

Check (negb true).

(* ... and to reduce it to its normal form *)

Compute (negb true).





(* Let's continue with natural numbers *)

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

(* Teaser: Recursive functions *)

Fixpoint plus (m n: nat) : nat :=
  match m with
  | O    => n
  | S m' => S (plus m' n)
  end.

(* The last definition was just notation for the following *)

Definition plus' : nat -> nat -> nat :=
  fix f (m n: nat): nat :=
    match m with
    | O    => n
    | S m' => S (f m' n)
    end.

(*
  Exercise: Define
    nat_greater_than_2: nat -> bool
*)

(*
  Exercise for the eager: Define
    mult: nat -> nat -> nat
*)




(* One more data type *)

(* Lists over natural numbers *)
Inductive natlist : Type :=
 | nil: natlist
 | cons: nat -> natlist -> natlist.

(*
  Exercise: Define the term that represents the list [1, 2, 3]
    one_two_three: natlist
*)

(*
  Exercise: Define
    is_natlist_empty: natlist -> bool
 *)

(*
  Exercise for the eager: Define
    length: natlist -> nat
*)