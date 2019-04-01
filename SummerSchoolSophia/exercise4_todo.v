From mathcomp Require Import all_ssreflect.

Implicit Type P Q R : Prop.

(** *** Exercise 0:
    - Define not. In type theory negation is defined in terms
      of [False].
*)

Definition not P := 
.

(** *** Exercise 1:
    - Prove the negation of the excluded middle.
*)
Lemma ex0 P : not (P /\ not P).
Proof.
Qed.

(** *** Exercise 2:
    - Declare iff (the constructor being called [iff_intro]).
    - Define iff1 of the given type
*)
Inductive iff P Q :=
.

Definition iff1 P Q : iff P Q -> P -> Q :=

(** *** Exercise 3:
    - Declare xor: two constructors, both have two arguments
    - Prove the following lemmas
*)

Inductive xor P Q : Prop :=
.

Lemma xorC P Q : iff (xor P Q) (xor Q P).
Proof.
Qed.


Lemma xor1 P Q : (xor P Q) -> not Q -> P.
Proof.
Qed.

Lemma xor2 P Q Z : (xor P Q) -> (xor Q Z) -> iff P Z.
Proof.
Qed.

(** *** Exercise 4:
    - Declare exists2
    - Prove a lemma ex1 -> ex2 T
*)

Inductive ex2 T (P Q : pred T) : Prop :=
.

Lemma ex2T T (P : pred T) : (exists x, P x) -> (ex2 T P P).
Proof.
Qed.

(** *** Exercise 5:
    - Write the induction principle for lists
*)
Definition induction_seq A (P : seq A -> Prop) :
  P nil -> (forall a l, P l -> P (a :: l)) -> forall l, P l :=
.


(** *** Exercise 6:
    - remeber [=> /view] to prove the following lemma
    - the two relevant views are [prime_gt1] and [dvdn_leq]
    - Note: [=> /view] combines well with [->] (lesson 3)
    - Hint: the proof can be a one liner [by move=> ....]
    - Recall: the notation "_ < _ <= _" hides a conjunction
*)
About prime_gt1.
About dvdn_leq.

Lemma ex_view p : prime p -> p %| 7 -> 1 < p <= 7.
Proof.
Qed.

(** *** Exercise 7:
    - Define the indexed data type of Cherry tree:
      + the index is a bool and must be truee iff the tree is completely
        flourished
      + leaves can be either Flower or Bud
      + the third constructor is called Node and has two sub trees
*)
Inductive cherryt : bool -> Type :=

Check Node _ Flower Flower : cherryt true.
Check Node _ Bud Bud       : cherryt false.
Fail Check Node _ Flower Bud.


