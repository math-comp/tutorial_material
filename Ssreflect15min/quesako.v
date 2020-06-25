(*** SSReflect, an extension of Coq's tactic language ***)

(** History **)


(*

- 2006 : First version,  part of the Coq proof of the Four Colour Theorem
- 2008 : First standalone release of Ssreflect (v1.1),  for Coq v8.1
- 2009 : First version of the documentation manual 
- 2012 : Completion of the proof of the Odd Order Theorem
- 2017 : Integration in the standard distribution of Coq
- today : used in various coq developments, of various nature 
(analysis, quickchick, elliptic curves, coqcombi, etc.)
*)


(** Name **)

(* SSReflect is coined after "Small Scale Reflection",  a formalization 
methodology making the most of the status of computation in TT. 


Ssreflect may thus refer to three different things: a formalization methodology,
a tactic language, and a corpus of formalized libraries, based on the former
methodology and developped using the latter language. A more appropriate name
for the libraries is "Mathematical Components".

In this file, we give a describe the small scale reflection method in a nutshell, 
so as to illustrate  the motivations for some features of the tactic language.

We start by writing proof scripts that do not depend on the ssreflect extension
of the tactic language, because the methodology is independent.
*)


(* == Reminder: large scale reflection *)

From Coq Require Import ZArith.

Open Scope Z_scope.

Definition c : Z :=
  90377629292003121684002147101760858109247336549001090677693.


(* An oracle produces these numbers... *)
Definition f1 := 588120598053661.
Definition f2 := 260938498861057.
Definition f3 := 760926063870977.
Definition f4 := 773951836515617.

(* We can check this identity using Coq: *)
Lemma factors_c : c = f1 * f2 * f3 * f4. 
(* the proof goes "by computation", because '_ * _' is a program *)
Proof. Time reflexivity. Qed.

(* Computational proofs on moderate size objects, like in the above example
already require thinking a bit about data-structures and complexity. *)
Close Scope Z_scope.

(* E.g. unary numbes are not an option. *)
(* Fail Eval compute in (1000 * 1000 : nat). *)

(* A reflection-based tactic replace explicit deduction steps, 
logged in proof terms, with computational steps, checked by the kernel's 
reduction machine. Reflection uses an inductive type (the "reflected" one) 
as an abstract, symbolic, data strutcure which can be used to write programs. 
The tactic checks that these computations can be interpreted as a valid 
propositional equality on a source type. For instance, the ring tactic reflects
a type equipped with a, possibly axiomatic and non-computational,
 ring structure into a type for polynomial expressions. *)


Require Import Arith Ring.

Goal forall (n : nat) (b : bool) (f : bool -> nat), 
  n + (f b) * n + n * (n + 1) = n * (n + (f b)) + 2 * n. 
Proof.
intros. ring.
Qed.


(* == Small scale reflection *)

(* In this case as well, the central idea is to replace deductive steps
by computation. But at a smaller and pervasive scale. *)


(* Standard library's definition of <= on natural numbers: an
   inductive representation of proofs. *)

Print le.


(* A small scale reflection version: a boolean program. For the sake of
   modularity, we expess it using the pseudo-substraction on natural 
   numbers, combined with a boolean equality test. *)

Fixpoint subn (n m : nat) : nat :=
match n, m with
  |_, 0 => n
  |0, _ => n
  |S n, S m => subn n m
end.

Fixpoint eqn (n m : nat) : bool :=
match n, m with
 |0, 0 => true
 |S n, S m => eqn n m
 |_ , _ => false
end.

Definition leq (n m : nat) : bool := eqn (subn n m) 0.

(* Let us compare a proof that 16 <= 64, in both approaches *)
Goal le 16 64.
Proof.
auto.
auto 50.
Show Proof.
Qed.

Goal leq 16 64 = true.
auto.
Show Proof.
Qed.

(* Small scale reflection at work: *)
Goal forall n m, leq n m = true -> leq (S n) (S m) = true.
Proof.
intros n m h.
(* Just like the proof of factor_c was by "reflexivity", the
proof of the current goal is "exactly" h, because the left-hand
sides of the equalities are convertible. *)
apply h. 
Qed.

(* The same proof with the le definition require an explicit 
induction step *)
Goal forall n m, le n m -> le (S n) (S m).
Proof.
intros n m h.
induction h as [| m ihnm ihSS].
  easy.
constructor.
easy.
Qed.

(** Selected basic features of the ssreflect tactic language **)

(* From now on, we will use the tactic extension. It is distributed 
as part of the Coq proof assistant, and loaded by the following Import *)
From Coq Require Import ssreflect.

(* The extension implements an improved rewrite tactic language. We
mention only two important features:
  == a diferent matching algorithm, rigid on head symbols and using conversion
     for the internal subterms.
  == a pattern selection mechanism based on this matching. *)

Goal forall n m c : nat, (forall a b, a + b = c) ->
  (n + m) + m + (n + m) = (n + m) + n + (n + m).
Proof.
intros n m c h.
   rewrite [n + _]h.
Admitted.


(*  The extension implements a view mechanism, to combine deductive 
steps (e.g. using an implication), with bureaucracy ones (e.g. 
introduction/generalization, case analysis). This is quite useful
to manage going back and forth between bool and Prop. Note: bool can be seen
as a type reflecting (certain) inhabitants of Prop.
*)

From mathcomp Require Import ssrfun ssrbool.

Goal forall b1 b2 b3 : bool, b1 /\ b2 -> b1 && b2 || b3. 
intros b1 b2 b3.
move/andP.
case/andP.
 Admitted.


(* Another strong motivation behind the design choices applied in the 
ssreflect tactic langage is to ease the maintenance/upkeep of formal libraries.
Features associated with this objective are:
   == fewer tactics: case, apply, elim, rewrite (move) 
   == two main tacticals and many switches
   == clearing policy for an easier book-keeping
   == enhanced support for forward chaining: have, suff, wlog
*)


(** SSReflect is only a stepping stone to build libraries.
   Demo: Prove that the concatenation (s1 ++ s2) of two lists is
   duplicate-free if and only if (s2 ++ s2) is also duplicate-free. **)

From mathcomp Require Import all_ssreflect.

 Module ExerciseSeq.

(* Implement a unary predicate on lists characterizing
  "duplicate free lists" *)

  (* The standard library answer:
  Inductive NoDup (A : Type) : list A -> Prop :=
    NoDup_nil : NoDup nil
  | NoDup_cons : forall (x : A) (l : list A),
         ~ In x l -> NoDup l -> NoDup (x :: l)
   *)


(* Compcert's take:
Inductive list_norepet (A: Type) : list A -> Prop :=
  | list_norepet_nil: list_norepet nil
  | list_norepet_cons: forall hd tl,
         ~(In hd tl) -> list_norepet tl -> list_norepet (hd :: tl).
*)


(* Mathematical Components's take: *)


Section ListNorepet.

(* eqType packages:
     T : Type
_ == _ : T -> T -> bool
  eqP : forall x y, x == y <-> x = y
 *)

Variable T : eqType.
Implicit Type s : list T.

(* Lists on an eqType have a boolean membership unary predicate,
   with a generic infix notation *)

Variables (foolist : list T) (foox : T).

Check (mem foolist).
Check foox \in foolist.
Check foox \notin foolist.

Check forall s x, x \in x :: s (* = true *).

(* Now implement uniq *)
Fixpoint uniq s : bool :=
  if s is x :: s' then (x \notin s') && uniq s' else true.

Fact uniq_nil : uniq nil. Proof. done. Qed.

Fact uniq_cons x s : x \notin s -> uniq s -> uniq (x :: s).
Proof.
by move=> nsx us; rewrite /= nsx.
Qed.

Print has.

Lemma cat_uniq s1 s2 :
  uniq (s1 ++ s2) = [&& uniq s1, ~~ has (mem s1) s2 & uniq s2].
Proof.
elim: s1 => [| x s1 ihs1] /=;  first by rewrite has_pred0 //.
rewrite mem_cat negb_or. rewrite has_sym. rewrite /= negb_or.
rewrite -!andbA. do !bool_congr. rewrite has_sym. done.
Qed.

Fact uniq_cat s1 s2 : uniq (s1 ++ s2) = uniq (s2 ++ s1).
Proof.
rewrite !cat_uniq has_sym. do !bool_congr.
Qed.

End ListNorepet.

End ExerciseSeq.


