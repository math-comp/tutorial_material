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
Lemma oddP (n : odd_nat) : odd n.
Proof. by case: n. Qed.

Structure even_nat := Even {
  eval :> nat;
  eprop : ~~ (odd eval)
}.
Lemma evenP (n : even_nat) : ~~ (odd n).
Proof. by case: n. Qed.

Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof. Fail by rewrite oddP evenP. Abort.

Canonical even_0 := Even 0 isT.

Lemma oddS n : ~~ (odd n) -> odd n.+1.
Proof.
Qed.

Lemma evenS n : (odd n) -> ~~ (odd n.+1).
Proof.
Qed.

Canonical odd_even (m : even_nat) :=
  Odd m.+1 (oddS m (eprop m)).
Canonical even_odd (m : odd_nat) :=

Lemma odd_mulP (n m : odd_nat) : odd (n * m).
Proof.
Qed.
Canonical odd_mul (n m : odd_nat) :=

Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof. by rewrite oddP evenP. Qed.

Fail Check forall n m : odd_nat, n == m.

Canonical odd_subType :=
Definition odd_eqMixin :=
Canonical odd_eqType :=

Check forall n m : odd_nat, n == m.

