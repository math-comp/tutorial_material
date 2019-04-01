From mathcomp Require Import all_ssreflect.

Implicit Type P Q R : Prop.

(** *** Exercise 0:
    - Define not. In type theory negation is defined in terms
      of [False].
*)

Definition not P := 
(*D*) P -> False
.

(** *** Exercise 1:
    - Prove the negation of the excluded middle.
*)
Lemma ex0 P : not (P /\ not P).
Proof.
(*D*)by move=> [p np]; apply: np; apply p.
Qed.

(** *** Exercise 2:
    - Declare iff (the constructor being called [iff_intro]).
    - Define iff1 of the given type
*)
Inductive iff P Q :=
(*D*)  iff_intro (p2q : P -> Q) (q2p : Q -> P)
.

Definition iff1 P Q : iff P Q -> P -> Q :=
(*D*)  fun x => match x with iff_intro f _ => f end.

(** *** Exercise 3:
    - Declare xor: two constructors, both have two arguments
    - Prove the following lemmas
*)

Inductive xor P Q : Prop :=
(*D*) | xorL (p : P) (np : not Q)
(*D*) | xorR (no : not P) (q : Q)
.

Lemma xorC P Q : iff (xor P Q) (xor Q P).
Proof.
(*D*)apply: iff_intro; case=> [p nq|np q]; by [ apply: xorL | apply: xorR ].
Qed.


Lemma xor1 P Q : (xor P Q) -> not Q -> P.
Proof.
(*D*)case=> [p _| np q] nq.
(*D*)  by apply: p.
(*D*)case: (nq q).
Qed.

Lemma xor2 P Q Z : (xor P Q) -> (xor Q Z) -> iff P Z.
Proof.
(*D*)by case=> [??|??]; case=>[??|??].
Qed.

(** *** Exercise 4:
    - Declare exists2
    - Prove a lemma ex1 -> ex2 T
*)

Inductive ex2 T (P Q : pred T) : Prop :=
(*D*)  ex2_intro (x : T) (p : P x) (q : Q x)
.

Lemma ex2T T (P : pred T) : (exists x, P x) -> (ex2 T P P).
Proof.
(*D*)by case=> x px; apply: (ex2_intro _ _ _ x).
Qed.

(** *** Exercise 5:
    - Write the induction principle for lists
*)
Definition induction_seq A (P : seq A -> Prop) :
  P nil -> (forall a l, P l -> P (a :: l)) -> forall l, P l :=
(*D*) fun pn pc =>
(*D*)    fix IH l : P l :=
(*D*)       match l with nil => pn | cons a l1 => pc a l1 (IH l1) end
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
(*D*)by move=> /prime_gt1 -> /dvdn_leq ->.
Qed.

(** *** Exercise 7:
    - Define the indexed data type of Cherry tree:
      + the index is a bool and must be truee iff the tree is completely
        flourished
      + leaves can be either Flower or Bud
      + the third constructor is called Node and has two sub trees
*)
Inductive cherryt : bool -> Type :=
(*D*)  | Flower : cherryt true
(*D*)  | Bud    : cherryt false
(*D*)  | Node   f (l : cherryt f) (r :cherryt f) : cherryt f.

Check Node _ Flower Flower : cherryt true.
Check Node _ Bud Bud       : cherryt false.
Fail Check Node _ Flower Bud.


