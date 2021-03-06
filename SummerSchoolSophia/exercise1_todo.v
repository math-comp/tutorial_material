From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** *** Exercise :
    - Define the option container with constructors None and Some
    - Define the "projection" default
*)
Inductive option
Arguments Some {_}.
Arguments None {_}.

Definition default
Eval lazy in default 3 None. (* 3 *)
Eval lazy in default 3 (Some 4). (* 4 *)

(** *** Exercise :
    Define boolean negation
*)
Definition negb b :=
Notation "~~ x" := (negb x).

Eval lazy in negb true.
Eval lazy in negb false.

(** *** Exercise :
    Use the [iter] function below to define:
    - addition over natural numbers.
    - multiplication over natural unmbers.
*)
Fixpoint iter (T : Type) n op (x : T) :=
  if n is p.+1 then op (iter p op x) else x.
Arguments iter {T}.

Definition addn n m :=

Eval lazy in addn 3 4.

Definition muln n m :=

Eval lazy in muln 3 4.

(** *** Exercise :
    - Define muln by recursion
*)
Fixpoint muln_rec n m :=

(** *** Exercise :
    - Use the the existing map function to define a functions that adds 2 to
      all elements of a list of integers.
    - Use the result of the previous exercise and the iter function to define
      a function that maps the natural number n to the list containing the n first
      odd numbers. (start with the empty list and then at each step, add 1 in front
      and increase all other elements by 2).*)

Definition add2list s :=

Definition odds n :=

