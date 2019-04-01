
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----------------------------------------------------------
#<div class="slide">#
** Lesson 4: summary

- Curry Howard: the big picture
  + dependent function space
- Predicates and connectives
  + introduction
  + elimination
- Induction
- Consistency
- Dependent elimination

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Curry Howard

We link typed programs to statements with a proof.

Let's play a game in which we use inductive types
as our satements.

#<div>#
*)

Check nat : Type.

Definition zero : nat := 0.

Lemma zero_bis : nat.
Proof.
apply: 0.
Qed.

Print zero.
Print zero_bis.


(**
#</div>#

We learn that 0 is a term of type nat, but Coq
also accepts it as a proof of nat.

#<div style='color: red; font-size: 150%;'>#
In type theory: [p] is a proof of [T] 
means that [p] inhabits the type [T].
#</div>#

Now let's look at the function space.

#<div>#
*)

Check nat -> nat  :  Type.

Definition silly : nat -> nat := fun x => x.

Lemma sillier : nat -> nat.
Proof. move=> x. apply: x. Qed.

Print silly.
Print sillier.

(**
#</div>#

The function space [->] can represent implication.
An inhabitant of [A -> B] is a function turning
a proof of [A] into a proof of [B] (a program
taking in input a term of type [A] and returning
a term of type [B]).

The function space of type theory is *dependent*.

#<div>#
*)

Section DependentFunction.

Variable P : nat -> Type.
Variable p1 : P 1.


Check forall x, P x.
Check forall x : nat, P 1.

Check fun x : nat => p1.
     

(**
#</div>#

We managed to build (introduce) an arrow and a forall using [fun].
Let's see how we can use (eliminate) an arrow or a forall.

#<div>#
*)

Check factorial.
Check factorial 2.

Variable px1 : forall x, P x.+1.

Check px1.
Check px1 3.

End DependentFunction.

(**
#</div>#

Following the Curry Howard correspondence *application*
lets one call a function [f : A -> B] on [a : A] to
obtain a term of type [B]. If the type of [f] is
a dependent arrow (forall) [f : forall x : A, B x]
then the argument [a] appears in the type of
term we obtain, that is [f a] has type [B a].

In other words application instantiates universally
quantified lemmas and implements modus ponens.

Lemmas can be seen as views to transform assumptions.

#<div>#
*)

Section Views.

Variable P : nat -> Type.
Variable Q : nat -> Type.
Variable p2q : forall x, P x -> Q x.

Goal P 3 -> True.
Proof.
move=> (*/p2q*) p3.
Abort.

End Views.

(**
#</div>#

So far we used [nat] (and [P]) as a predicate and [->] for implication.

Can we use inductive types to model other predicates or connectives?

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 4.x of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#

----------------------------------------------------------
#<div class="slide">#
** Predicates and connectives

Let's start with #$$ \top $$#

Note: here the label [Prop] could be a synonym of [Type].

#<div>#
*)

Print True.

Definition trivial1 : True := I.

Definition trivial2 : True -> nat :=
  fun t =>
    match t with I => 3 end.

Lemma trivial3 : True -> nat.
Proof.
move=> t. case: t. apply: 3.
Qed.

(**
#</div>#

Now let's look at #$$ \bot $$#

#<div>#
*)

Print False.

Fail Definition hard1 : False := what.

Definition ex_falso A : False -> A :=
  fun abs => match abs with end.

Lemma ex_falso2 A : False -> A.
Proof.
move=> abs. case: abs.
Qed.

(**
#</div>#

Connectives: #$$ \land $$# and #$$\lor $$#

#<div>#
*)

Section Connectives.

Print and.

Variable A : Prop.
Variable B : Prop.
Variable C : Prop.

Variable a : A.
Variable b : B.

Check conj a b.

Definition and_elim_left : and A B -> A :=
  fun ab => match ab with conj a b => a end.


Lemma and_elim_left2 : and A B -> A.
Proof. case=> l r. apply: l. Qed.

Print or.

Check or_introl a : or A B.
Check or_intror b : or A B.

Definition or_elim :
  A \/ B -> (A -> C) -> (B -> C) -> C :=
 fun aob a2c b2c =>
   match aob with
   | or_introl a => a2c a
   | or_intror b => b2c b
   end.

Lemma or_elim_example : A \/ B -> C.
Proof.
move=> aob.
case: aob.
Abort.

(**
#</div>#

Quantifier #$$ \exists $$#

#<div>#
*)

Print ex.

Lemma ex_elim P : (exists x : A, P x) -> True.
Proof.
case => x px.
Abort.

End Connectives.

(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 4.x of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#
----------------------------------------------------------
#<div class="slide">#
** Induction

We want to prove theorems by induction, right?
Hence there must be a term that corresponds to the induction principle.
This term is a recursive function.

Note: [Fixpoint] is just sugar for [Definition] followed by [fix].

#<div>#
*)

About nat_ind.

Definition ind :
  forall P : nat -> Prop,
    P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n :=
  fun P p0 pS =>
    fix IH n : P n :=
      match n with
      | O => p0
      | S p => pS p (IH p)
      end.

(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 4.x of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

----------------------------------------------------------
#<div class="slide">#
** Consistency

We give here the intuition why some terms that are in principle
well typed are rejected by Coq and why Coq is consistent.

#<div>#
*)
Print False.
Print True.
(**
#</div>#

What does it mean that [t : T] and [T] is not [False]?

#<div>#
*)
Check (match 3 with O => I | S _ => I end) : True.
(**
#</div>#

Constructors are not the only terms that can inhabit a type.
Hence we cannot simply look at terms, but we could look at
their normal form.

Subject reduction: [t : T] and [t ~> t1] then [t1 : T].
We claim there is not such [t1] (normal form) that
inhabits [False].

We have to reject [t] that don't have a normal form.

Exaustiveness of pattern matching:

#<div>#
*)

Lemma helper x : S x = 0 -> False. Proof. by []. Qed.

Fail Definition partial n : n = 0 -> False :=
  match n with
  | S x => fun p : S x = 0 => helper x p
(*  | 0 => fun _ => I*)
  end.

Fail Check partial 0 (erefl 0). (* : False *)

Fail Compute partial 0 (erefl 0). (* = ??? : False *)

(**
#</div>#

According to Curry Howard this means that in a case
split we did not forget to consider a branch!

Termination of recursion:

#<div>#
*)

Fail Fixpoint oops (n : nat) : False := oops n.+1.

Fail Check oops 3. (* : False *)

Fail Compute oops 3. (* = ??? : False *)

(**
#</div>#

According to Curry Howard this means that we did not
do any circular argument.

Non termination is subtle since a recursive call could
be hidden in a box.

#<div>#
*)

Fail Inductive hidden := Hide (f : hidden -> False).

Fail Definition oops (hf : hidden) : False :=
  match hf with Hide f => f hf end.

Fail Check oops (Hide oops). (* : False *)

Fail Compute oops (Hide oops). (* = ??? : False *)

(**
#</div>#

This condition of inductive types is called positivity:
The type of [Hide] would be [(hidden -> False) -> hidden],
where the first occurrence of [hidden] is on the left (negative)
of the arrow.

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 3.2.3 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#

----------------------------------------------------------
#<div class="slide">#
** Inductive types with indexes (casse-tête)

... and their elimination.

The intuition, operationally.

Inductive types can express tricky invariants:

#<div>#
*)

(* Translucent box, we know if it is empty or not without opening it *)
Inductive tbox : bool -> Type :=
  | Empty          : tbox false
  | Full (n : nat) : tbox true.

Check Empty.
Check Full 3.

Definition default (d : nat) (f : bool) (b : tbox f) : nat :=
  match b with
  | Empty => d
  | Full x => x
  end.

(* Why this complication? (believe me, not worth it) *)
Definition get (b : tbox true) : nat :=
  match b with Full x => x end.

(* the meat: why is the elimination tricky? *)
Lemma default_usage f (b : tbox f) : 0 <= default 3 b .
Proof.
case: b.
Fail Check @default 3 f Empty.
  by [].
by [].
Qed.

(**
#</div>#

Take home:
- the elimination of an inductive data type with indexes
  expresses equations between the value of the indexes
  in the type of the eliminated term and the value of the
  indexes prescribed in the declatation of the inductive data
- the implicit equations are substituted automatically at
  elimination time
- working with indexed data is hard, too hard :-/
- we can still make good use of indexes when we define "spec" lemmas,
  argument of the next lecture

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 4.x of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Lesson 4: sum up

- In Coq terms/types play a double role:
  + programs and their types
  + statements and their proofs
- Inductives can be used to model predicates and
  connectives
- Pattern machind and recursion can model induction
- The empty type is, well, empty, hence Coq is consistent
- Inductives with indexes

#</div>#

*)
