From mathcomp Require Import all_ssreflect. 


(** *** Exercise 1:
    - Let's define the subtype of odd and even natural numbers
    - Intrument Coq to recognize odd/even number built out
      of product and successor
    - Inherit on [odd_nat] the [eqType] structure 
*)

Structure odd_nat := Odd {
  oval :> nat;
  oprop : odd oval
}.

(* Prove the main property of [odd_nat] *)
Lemma oddP (n : odd_nat) : odd n.
Proof.
(*D*)by case: n.
Qed.

Structure even_nat := Even {
  eval :> nat;
  eprop : ~~ (odd eval)
}.

(* Prove the main property of [even_nat] *)
Lemma evenP (n : even_nat) : ~~ (odd n).
Proof.
(*D*) by case: n.
Qed.

(* The objective is to make it work: knowing that [n] is [odd]
   Coq should infer that [n * 3] is also odd, and that [6] is even *)
Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof. Fail by rewrite oddP evenP. Abort.

(* Let's start by telling Coq that 0 is even *)
Canonical even_0 : even_nat := Even 0 isT.

Lemma oddS n : ~~ (odd n) -> odd n.+1.
Proof.
(*D*)by rewrite /=; case: (odd n).
Qed.

Lemma evenS n : (odd n) -> ~~ (odd n.+1).
Proof.
(*D*)by rewrite /=; case: (odd n).
Qed.

(* Here we teach Coq that if [m] is even, then [m.+1] is odd *)
Canonical odd_even (m : even_nat) : odd_nat :=
  Odd m.+1 (oddS m (eprop m)).

(* Implement the dual, teach coq that if [m] is odd then [m.+1] is even *)
Canonical even_odd (m : odd_nat) : even_nat :=
(*D*)Even m.+1 (evenS m (oprop m)).

(* Now let's deal with multiplication *)
Lemma odd_mulP (n m : odd_nat) : odd (n * m).
Proof.
(*D*)by rewrite odd_mul !oddP.
Qed.

(* Teach Coq that [*] preserves being odd *)
Canonical odd_mul (n m : odd_nat) : odd_nat :=
(*D*)Odd (n * m) (odd_mulP n m).

(* Enjoy! *)
Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof. by rewrite oddP evenP. Qed.

(* We can't use [==] on odd natural numbers because 
   [odd_nat] is not an [eqType] *)
Fail Check forall n m : odd_nat, n == m.

(* Use the subtype machinery (that we used for tuples) in order
   to teach Coq that [odd_nat] is an [eqType] *)
Canonical odd_subType :=
(*D*)Eval hnf in [subType for oval].
Definition odd_eqMixin :=
(*D*)Eval hnf in [eqMixin of odd_nat by <:].
Canonical odd_eqType :=
(*D*)Eval hnf in EqType odd_nat odd_eqMixin.

(* Enjoy *)
Check forall n m : odd_nat, n == m.

(* Now do the same for [even_nat] *)
Fail Check forall (n m : even_nat), m == n.

(*D*)Canonical even_subType := Eval hnf in [subType for eval].
(*D*)Definition even_eqMixin := Eval hnf in [eqMixin of even_nat by <:].
(*D*)Canonical even_eqType := Eval hnf in EqType even_nat even_eqMixin.

Check forall (n m : even_nat), m == n.



