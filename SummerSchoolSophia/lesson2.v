
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----------------------------------------------------------
#<div class="slide">#
** Lesson 2: summary

- statements
- proofs by computation
- proofs by case split
- proofs by rewriting

#<p><br/><p>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Formal proofs 

Today we learn how to state and prove theorems.
We don't do that in the void, nor without a methodology.

We work on top of the Mathematical Components library
and we follow the Small Scale Reflection approach using
the SSReflect proof language.

The Mathematical Components library can be
#<a href="http://math-comp.github.io/math-comp/">browsed online</a>#.
The modules of interest are
#<a href="https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/ssrnat.v">ssrnat</a>#
 and 
#<a href="https://github.com/coq/coq/blob/master/plugins/ssr/ssrbool.v">ssrbool</a>#
 (see the headers for the doc).

The SSReflect proof language
(#<a href="https://coq.inria.fr/distrib/current/refman/proof-engine/ssreflect-proof-language.html">reference manual</a>#)
is covered in full details by the Mathematical Components book.
Here we just cover the basics.


#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** Formal statements

Most of the statements that we consider in Mathematical
Components are equalities.

#<div>#
*)

Check (_ = _).
Locate "_ = _".

(**
#</div>#

For example, we can equate two expressions representing natural numbers.

#<div>#

*)

Lemma addnA: forall (m n k : nat), m + (n + k) = (m + n) + k.
Abort.

(**
#</div>#

Addition is defined as left-associative.

#<div>#
*)

Lemma addnA: forall (m n k : nat), m + (n + k) = m + n + k.
Abort.

(**
#</div>#

Quantifications can be set as parameters before the colon.

#<div>#
*)

Lemma addnA (m n k : nat) : m + (n + k) = m + n + k.
Abort.

(**
#</div>#

In lesson 1 we have defined many boolean tests that can
play the role of (decidable) predicates.

#<div>#
*)

Check 0 <= 4. (* not a statement *)
Check (0 <= 4) = true. (* a statement we can prove *)

(**
#</div>#

#<div style='color: red; font-size: 150%;'>#
Motto: whenever possible predicates are expressed as a programs.
#</div>#

This choice has a deep impact on the proofs we make in lesson 2 and 3 and
the way we can form new types in lesson 4.

Booleans can be coerced into statements.
#<div>#
*)

Check is_true (* Definition is_true b := b = true *).

(**
#</div>#

Tests can be turned into statements.

#<div>#
*)

Check (_ <= _).

Check is_true (_ <= _).

Lemma leq0n (n : nat) : is_true (0 <= n).
Abort.

(**
#</div>#

 the [is_true]
"coercion" is automatically inserted by Coq.

#<div>#
*)

Lemma leq0n (n : nat) : 0 <= n.
Abort.

(**
#</div>#

Equality statement between tests reads as  "if and only if".

#<div>#
*)

Print Nat.sub.

Lemma eqn_leq (m n : nat) : m == n = (m <= n) && (n <= m).
Abort.

(**
#</div>#

[(_ <= _) && (_ <= _)] has a special notation [(_ <= _ <= _)]

#<div>#
*)

Lemma eqn_leq (m n : nat) : m == n = (m <= n <= m).
Abort.

(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 2.1 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
** Proofs by computation

Our statements are programs. Hence they compute!

The [by[]] tactic solves trivial goal (mostly) by
computation.

<<
Fixpoint addn n m :=
  if n is p.+1 then (addn p m).+1 else m.
>>
#<div>#
*)

Goal  2 + 2 = 4.
Proof. by []. Qed.


Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof. by []. Qed.


(**
#</div>#
<<
Fixpoint subn m n : nat :=
  match m, n with
  | p.+1, q.+1 => subn p q
  | _ , _ => m
  end.
>>
#<div>#
*)

Goal  2 - 4 = 0.
Proof. by []. Qed.

Lemma subn0 m n : m.+1 - n.+1 = m - n.
Proof. by []. Qed.

(**
#</div>#
<<
Definition leq m n := m - n == 0.
>>
#<div>#
*)

Goal  0 <= 4.
Proof. by []. Qed.

(**
#</div>#

[_ < _] is just a notation for [_.+1 <= _].

#<div>#
*)

Goal  3 < 3 = false.
Proof. by []. Qed.

Goal  4 <= 3 = false.
Proof. by []. Qed.

Lemma leq0n n : 0 <= n.
Proof. by []. Qed.

Lemma ltn0 n : n.+1 <= 0 = false.
Proof. by []. Qed.

Lemma ltnS m n : (m.+1 <= n.+1) = (m <= n).
Proof. by []. Qed.

(**
#</div>#

Notice the naming convention.

#<div>#
*)

Print negb.
Locate "~~".
Search negb in ssr.ssrbool.

Lemma negbK (b : bool) : ~~ (~~ b) = b.
Proof. Fail by []. Abort.

(**
#</div>#

It is not always the case the computation solves all our
problems. In particular here there are no constructors to
consume, hence computation is stuck.

To prove [negbK] we need a case split.

#<p><br/><p>#


#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 2.2.1 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#


----------------------------------------------------------
#<div class="slide">#
** Proofs by case analysis 

The proof of [negbK] requires a case analysis: given that
[b] is of type bool, it can only be [true] or [false].

The [case: term] command performs this proof step.

#<div>#
*)

Lemma negbK b : ~~ (~~ b) = b.
Proof.
case: b.
  by [].
by [].
Qed.

Lemma andbC (b1 b2 : bool) : b1 && b2 = b2 && b1.
Proof.
by case: b1; case: b2.
Qed.

Lemma orbN b : b || ~~ b.
Proof.
by case: b.
Qed.

(**
#</div>#

The constructors of [bool] have no arguments, but for
example the second constructor of [nat] has one.

In this case one has to complement the command by supplying
names for these arguments.

#<div>#
*)

Lemma leqn0 n : (n <= 0) = (n == 0).
Proof.
case: n => [| p].
  by [].
by [].
Qed.

(**
#</div>#

Sometimes case analysis is not enough.

[[
Fixpoint muln (m n : nat) : nat :=
  if m is p.+1 then n + muln p n else 0.
]]

#<div>#
*)
Lemma muln_eq0 m n :
(m * n == 0) = (m == 0) || (n == 0).
Proof.
case: m => [|p].
  by [].
case: n => [|k]; last first. (* rotates the goals *)
  by [].
Abort.

(**
#</div>#

We don't know how to prove this yet.
But maybe someone proved it already...

#<div>#
*)
Search _ (_ * 0) in ssrnat. (*   :-(   *)
Search _ muln 0 in ssrnat.
Print right_zero.
Search right_zero.

(**
#</div>#

The [Search] command is quite primitive but also
your best friend. 

It takes a head pattern, the whildcard [_]
in the examples above, followed by term or patterns,
and finally a location, in this case the [ssrnat] library.

Our first attempt was unsuccessful because
standard properies (associativity, communtativity, ...)
are expressed in Mathematical Components using
higher order predicates.
In this way these lemmas are very consistent, but also
harder to find if one does not know that.

The second hit is what we need to complete the proof.

#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
sections 2.2.2 and 2.5 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** Proofs by rewriting

The [rewrite] tactic uses an equation. If offers many
more flags than the ones we will see (hint: check the
Coq user manual, SSReflect chapter).

#<div>#
*)

Lemma muln_eq0 m n :
  (m * n == 0) = (m == 0) || (n == 0).
Proof.
case: m => [|p].
  by [].
case: n => [|q].
  rewrite muln0.
  by [].
by [].
Qed.

(**
#</div>#

Let's now look at another example to learn more
about [rewrite].

#<div>#
*)
Lemma leq_mul2l m n1 n2 :
  (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.
rewrite /leq.
(* Search _ muln subn in ssrnat. *)
rewrite -mulnBr.
rewrite muln_eq0.
by [].
Qed.

(**
#</div>#


#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 2.2.3 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** Lesson 2: sum up

- [by []] trivial proofs (including computation)
- [case: m] case split
- [rewrite t1 -t2 /def] rewrite

#</div>#

*)
