From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(** 

----------------------------------------------------------
#<div class="slide">#
** The Coq proof assistant and the Mathematical Components library

Objective: learn the Coq system in the MC library

*** Roadmap

- #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/lesson1.html">lesson 1</a>#: Functions and computations
  - #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise1.html">exercise</a> <!-- and <a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise1-solution.html">solution</a>-->#

- #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/lesson2.html">lesson 2</a>#: First steps in formal proofs
  - #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise2.html">exercise</a> <!-- and <a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise2-solution.html">solution</a>-->#

- #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/lesson3.html">lesson 3</a>#: A few more steps in formal proofs
  - #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise3.html">exercise</a> <!-- and <a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise3-solution.html">solution</a>-->#

- #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/lesson4.html">lesson 4</a>#: Type theory
  - #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise4.html">exercise</a> <!-- and <a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise4-solution.html">solution</a>-->#

- #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/lesson5.html">lesson 5</a>#: Boolean reflection
  - #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise5.html">exercise</a> <!-- and <a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise5-solution.html">solution</a>-->#

- #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/lesson6.html">lesson 6</a>#: Real proofs, finally!
  - #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise6.html">exercise</a> <!-- and <a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise6-solution.html">solution</a>-->#

- #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/lesson7.html">lesson 7</a>#: Generic theories
  - #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise7.html">exercise</a> <!-- and <a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise7-solution.html">solution</a>-->#

- #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/lesson8.html">lesson 8</a>#: Subtypes
  - #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise8.html">exercise</a> <!-- and <a href="https://www-sop.inria.fr/teams/marelle/coq-18/exercise8-solution.html">solution</a>-->#

*** Teaching material

- Slides and exercises
  #<a href="https://www-sop.inria.fr/teams/marelle/coq-18/">https://www-sop.inria.fr/teams/marelle/coq-18/</a>#
- Coq (#<a href="https://coq.inria.fr/download">software</a>#
  and #<a href="https://coq.inria.fr/distrib/current/refman/">user manual</a>#, in particular the chapter about #<a href="https://coq.inria.fr/distrib/current/refman/proof-engine/ssreflect-proof-language.html">SSReflect</a>#)
- Mathematical Components
  (#<a href="http://math-comp.github.io/math-comp/">software</a># and
  #<a href="https://math-comp.github.io/mcb/">book</a>#)


#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#
You don't need to install Coq in order to follow this
class, you just need a recent browser thanks to
#<a href="https://github.com/ejgallego/jscoq">jsCoq</a>#.
#</div></div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Lesson 1: summary

- functions
- simple data
- containers
- symbolic computations
- higher order functions and mathematical notations

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Functions

Functions are built using the [fun .. => ..] syntax.
The command [Check] verifies that a term is well typed.

#<div>#
*)
Check (fun n => 1 + n + 1).
(**
#</div>#

Notice that the type of [n] was inferred and that
the whole term has type [nat -> nat], where [->]
is the function space.

Function application is written by writing the function
on the left of the argument (eg, not as in the mathematical
practice).

#<div>#
*)
Check 2.
Check (fun n => 1 + n + 1) 2.
(**
#</div>#

Notice how [2] has a type that fits, and hence
the type of the function applied to [2] is [nat].

Terms (hence functions) can be given a name using
the [Definition] command. The command offers some
syntactic sugar for binding the function arguments.

#<div>#
*)
Definition f := (fun n => 1 + n + 1).
(* Definition f n := 1 + n + 1. *)
(* Definition f (n : nat) := 1 + n + 1. *)
(**
#</div>#

Named terms can be printed.

#<div>#
*)
Print f.
(**
#</div>#

Coq is able to compute with terms, in particular
one can obtain the normal form via the [Eval lazy in]
command.

#<div>#
*)
Eval lazy in f 2.
(**
#</div>#

Notice that "computation" is made of many steps.
In particular [f] has to be unfolded (delta step)
and then the variable substituted for the argument
(beta).

#<div>#
*)
Eval lazy delta [f] in f 2.
Eval lazy delta [f] beta in f 2.
(**
#</div>#

Nothing but functions (and their types) are built-in in Coq.
All the rest is defined, even [1], [2] and [+] are not primitive.

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 1.1 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Data types

Data types can be declared using the [Inductive] command.

Many of them are already available in the Coq library called
[Prelude] that is automatically loaded. We hence just print
them.

[Inductive bool := true | false.]

#<div>#
*)
Print bool.
(**
#</div>#

This command declares a new type [bool] and declares
how the terms (in normal form) of this type are built.
Only [true] and [false] are canonical inhabitants of
[bool].

To use a boolean value Coq provides the [if..then..else..]
syntax.

#<div>#
*)
Definition twoVtree (b : bool) := if b then 2 else 3.
Eval lazy in twoVtree true.
Eval lazy delta in twoVtree true.
Eval lazy delta beta in twoVtree true.
Eval lazy delta beta iota in twoVtree true.
(**
#</div>#

We define a few boolean operators that will come in handy
later on.

#<div>#
*)
Definition andb (b1 b2 : bool) := if b1 then b2 else false.
Definition orb (b1 b2 : bool) := if b1 then true else b2.

Infix "&&" := andb.
Infix "||" := orb.

Check true && false || false.
(**
#</div>#

The [Infix] command lets one declare infix notations.
Precedence and associativity is already declared in the
prelude of Coq, here we just associate the constants
[andb] and [orb] to these notataions.

Natural numbers are defined similarly to booleans:

[Inductive nat := O | S (n : nat).]

#<div>#
*)
Print nat.
(**
#</div>#

Coq provides a special notation for literals, eg [3],
that is just sugar for [S (S (S O))].

The Mathematical Components library adds on top of that
the postfix [.+1], [.+2], .. for iterated applications
of [S] to terms other than [O].

#<div>#
*)
Check 3.
Check (fun x => (x + x).+2).
Eval lazy in (fun x => (x + x).+2) 1.
(**
#</div>#

In order to use natural numbers Coq provides two
tools. An extended [if..then..else..] syntax to
extract the argument of [S] and the [Fixpoint]
command to define recusrsive functions.

#<div>#
*)
Definition pred (n : nat) :=
  if n is p.+1 then p else 0.

Eval lazy in pred 7.
(**
#</div>#

Notice that [p] is a binder. When the [if..then..else..]
is evaluated, and [n] put in normal form, then if it
is [S t] the variable [p] takes [t] and the then-branch
is taken.

Now lets define addition using recursion

#<div>#
*)
Fixpoint addn n m :=
  if n is p.+1 then (addn p m).+1 else m.
Infix "+" := addn.
Eval lazy in 3 + 2.
(**
#</div>#

The [if..then..else..] syntax is just sugar for
[match..with..end].

#<div>#
*)
Print addn.
(**
#</div>#

Let's now write the equality test for natural numbers

#<div>#
*)
Fixpoint eqn n m :=
  match n, m with
  | 0, 0 => true
  | p.+1, q.+1 => eqn p q
  | _, _ => false
  end.
Infix "==" := eqn.
Eval lazy in 3 == 4.
(**
#</div>#

Other examples are subtraction and order

#<div>#
*)
Fixpoint subn m n : nat :=
  match m, n with
  | p.+1, q.+1 => subn p q
  | _ , _ => m
  end.

Infix "-" := subn.

Eval lazy in 3 - 2.
Eval lazy in 2 - 3. (* truncated *)

Definition leq m n := m - n == 0.

Infix "<=" := leq.

Eval lazy in 4 <= 5.
(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

All the constants defined in this slide are already
defined in Coq's prelude or in Mathematical Components.
The main difference is that [==] is not specific to
[nat] but overloaded (it works for most data types).
This topic is to be developed in lesson 4.

This slide corresponds to
section 1.2 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Containers

Containers let one aggregate data, for example to form a
pair or a list.  The interesting characteristic of containers
is that they are polymorphic: the same container can be used
to hold terms of many types.

[Inductive seq (A : Type) := nil | cons (hd : A) (tl : seq A).]

#<div>#
*)
Check nil.
Check cons 3 [::].
(**
#</div>#

We learn that [[::]] is a notation for the empty sequence
and that the type parameter [?A] is implicit.

#<div>#
*)
Check 1 :: nil.
Check [:: 3; 4; 5 ].
(**
#</div>#

The infix [::] notation stands for [cons]. This one is mostly
used to pattern match a sequence.

The notation [[:: .. ; .. ]] can be used to form sequences
by separating the elements with [;]. When there are no elements
what is left is [[::]] that is the empty seqeunce.

And of course we can use sequences with other data types

#<div>#
*)
Check [:: 3; 4; 5 ].
Check [:: true; false; true ].
(**
#</div>#

Let's now define the [size] function.

#<div>#
*)
Fixpoint size A (s : seq A) :=
  if s is _ :: tl then (size tl).+1 else 0.

Eval lazy in size [:: 1; 8; 34].
(**
#</div>#

Given that the contents of containers are of an
arbitrary type many common operations are parametrized
by functions that are specific to the type of the
contents.

[[
Fixpoint map A B (f : A -> B) s :=
if s is e :: tl then f e :: map f tl else nil.
]]

#<div>#
*)
Definition l := [:: 1; 2; 3].
Eval lazy in [seq x.+1 | x <- l].
(**
#</div>#

The #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.seq.html">seq</a>#
library of Mathematical Components contains many combinators. Their syntax
is documented in the header of the file.

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 1.3 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#

----------------------------------------------------------
#<div class="slide">#
** Symbols

The section mecanism is used to describe a context under
which definitions are made. Coq lets us not only define
terms, but also compute with them in that context.

We use this mecanism to talk about symbolic computation.

#<div>#
*)
Section symbols.
Variables v : nat.

Eval lazy in pred v.+1 .
Eval lazy in pred v .
(**
#</div>#

Computation can take place in presence of variables
as long as constructors can be consumed. When no
more constructors are available computation is
stuck.

Let's not look at a very common higher order
function.

#<div>#
*)

Fixpoint foldr A T f (a : A) (s : seq T) :=
  if s is x :: xs then f x (foldr f a xs) else a.
(**
#</div>#

The best way to understand what [foldr] does 
is to postulate a variable [f] and compute. 

#<div>#
*)

Variable f : nat -> nat -> nat.

Eval lazy in foldr f    3 [:: 1; 2 ].

(**
#</div>#

If we plug [addn] in place of [f] we
obtain a term that evaluates to a number.

#<div>#
*)

Eval lazy in foldr addn 3 [:: 1; 2 ].

End symbols.

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
sections 1.4 and 1.5 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Higher order functions and mathematical notations

Let's try to write this formula in Coq

#$$ \sum_{i=1}^n (i * 2 - 1) = n ^ 2 $$#

We need a bit of infrastruture

#<div>#
*)
Fixpoint iota m n := if n is u.+1 then m :: iota m.+1 u else [::].

Eval lazy in iota 0 5.

(**
#</div>#

Combining [iota] and [foldr] we can get pretty
close to the LaTeX source for the formula above.

#<div>#
*)

Notation "\sum_ ( m <= i < n ) F" :=
  (foldr (fun i a => F + a) 0 (iota m (n-m))).

Check \sum_(1 <= x < 5) (x * 2 - 1).
Eval lazy in \sum_(1 <= x < 5) (x * 2 - 1).
(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 1.6 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Lesson 1: sum up

- [fun .. => ..]
- [Check]
- [Definition]
- [Print]
- [Eval lazy]
- [Inductive] declarations [bool], [nat], [seq].
- [match .. with .. end] and [if .. is .. then .. else ..]
- [Fixpoint]
- [andb] [orb] [eqn] [leq] [addn] [subn] [size] [foldr]

#</div>#


*)
