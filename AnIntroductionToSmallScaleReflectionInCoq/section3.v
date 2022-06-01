(******************************************************************************)
(* Solutions of exercises : A script language for structured proofs           *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import path choice fintype tuple finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(******************************************************************************)
(* Exercise 3.1.1                                                             *)
(******************************************************************************)

Section Tauto.

Variables A B C : Prop.

(* The exact tactic takes its argument on top of the goal stack *)
Lemma tauto1 : A -> A.
Proof.
exact.
Qed.

(* exact: hAB behaves like (by apply: hAB) and hence finds the hypothesis A
in the context needed to solve the goal *)
Lemma tauto2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
move=> hAB hBC hA.
apply: hBC.
exact: hAB.
Qed.

Lemma tauto4 : A /\ B <-> B /\ A.
Proof. by split; case=> h1 h2; split. Qed.
  
End Tauto.

(******************************************************************************)
(* Exercise 3.1.2                                                             *)
(******************************************************************************)

Section MoreBasics.

Variables A B C : Prop.
Variable P : nat -> Prop.

Lemma foo1 : ~(exists x, P x) -> forall x, ~P x.
move=> h x Px.
apply: h.
by exists x.
Qed.


Lemma foo2 : (exists x, A -> P x) -> (forall x, ~P x) -> ~A.
Proof.
case=> x hx hP hA.
apply: (hP x).
exact: hx.
Qed.
End MoreBasics.

(******************************************************************************)
(* Exercise 3.1.3                                                             *)
(******************************************************************************)

(* Try Search "<=" to see the various notations featuring <= *)

(* The first line of the returned answer gives the name of
   the predicate (leq) *)
Search "_ <= _".

(* The Print command shows that leq is defined using subtraction *)
Print leq.

(* This time we see that the first line of the answer gives the *)
(*answer: there is no constant defining "<" but the notation hides a *)
(* defintiion using leq *)

Search "_ < _".

(* Both cases gereated by the induction lead to trivial goals *)
Lemma tuto_subnn : forall n : nat, n - n = 0.
Proof. by elim=> [|n ihn]. Qed.
  
(* This proof is an induction on m, followed by a case  analysis on *)
(* the second n. Base case is trivial (hence discarded by the // *)
(* switch. *)
Lemma tuto_subn_gt0 : forall m n, (0 < n - m) = (m < n).
Proof. elim=> [|m IHm] [|n] //; exact: IHm. Qed.


(* This proof starts the same way as the one of subn_gt0. *)
(* Then two rewriting are chained to reach to trivial subgoals *)
Lemma tuto_subnKC : forall m n : nat, m <= n -> m + (n - m) = n.
Proof.
elim=> [|m IHm] [|n] // Hmn.
Search _ (_.+1 + _ = _.+1).
by rewrite addSn IHm.
Qed.
  
(* The first Search command suggests we need to use something like *)
(*subn_add2r, hence to transform n into n - p + p *)
(* The second Search command finds the appropriate lemma. We rewrite *)
(*it from right to left, only at the second occurrence of n, the *)
(*condition of the lemma is fullfilled thanks to the le_pn hypothesis, *)
(*hence the generated subgoal is closed by the // switch *)

Lemma tuto_subn_subA : forall m n p, p <= n -> m - (n - p) = m + p - n.
Proof. 
move=> m n p le_pn.
Search _ (_ + _ - _ = _) in ssrnat.
Search _ (_ - _ + _).
rewrite -{2}(subnK le_pn) // subnDr.
done. 
Qed.

(******************************************************************************)
(* Exercise 3.5.1                                                             *)
(******************************************************************************)

(* The Check instruction only gives the type of a constant, the *)
(*statement of a lemma. The Print command gives the body of the *)
(*definition, and possibly some extra information (scope, implicit *)
(*arguments,...). Print should not be used in general on lemmas *)
(* since the body of a proof is seldom relevant...*)

Print edivn.
Print edivn_rec.
Print edivn_spec.
(* The edivn_spec is defined as a CoInductive predicate. The intended *)
(* meaning is not to define an coinductive structure, but rather an *)
(* inductive one. CoInductive in this case indeed behaves as Inductive *)
(*but does not generate an induction principle, which would be is *)
(*useless in this case. *)


(******************************************************************************)
(* Exercise 3.5.2                                                             *)
(******************************************************************************)

(* At this point, the top of the goal stack was featuring three *)
(*natural numers: an induction on the first one generated two subgoals. *)
(*In the second subgoal, corresponding to the inductive case, the *)
(*generated natural number and induction hypothesis have  been *)
(*introduced by the branching intro pattern [| n IHn], which leaves *)
(*the first subgoal, corresponding to the base case of the induction, *)
(*unchanged. Then [|m] performs in both subgoals a case analysis on the *)
(*second natural number. This case analysis again leads to two new *)
(*subgoal for each initial branch (which makes four subgoals). In the *)
(*second case of the analysis, the new natural number is introduced *)
(*and named m. Then the third natural number is uniformly introdued in *)
(*the four cases under the name q. Finally the //= switch simplifies *)
(*in the four bracnhes and closes the goals that have become trivial *)
(*(i.e. which are solved by done). *)

(******************************************************************************)
(* Exercise 3.5.3                                                             *)
(******************************************************************************)

(* The pattern [// | le_dm] closes the first subgoal and introduces an *)
(*hypothesis named le_dm in the second subgoal. This is equivalent to *)
(* // le_dm. *)

(******************************************************************************)
(* Exercise 3.5.4                                                             *)
(******************************************************************************)

(* Replacing (ltnP m d) by ltnP does not change the behaviour of the *)
(*script: Coq's unification is powerful enough to guess the arguments *)
(*in this case since there is only one instance of the comparison in *)
(* (_ <_) the goal. Arguments are mandatory only in the case the frist *)
(*occurrence of the comparison is not the one the user whould like to *)
(*pick as support for ase analysis. *)

Check ltnP.
Print ltn_xor_geq.

(* For any two natural numbers n and m, (ltn_xor_geq m n) is a binary *)
(*relation on boolean. Its inductive definition has two constructors *)
(*and states that *)
(* - (false, true) is in the relation(ltn_xor_geq m n) as soon as 
     m < n *)
(* - (true, false) is in the relation(ltn_xor_geq m n) as soon as 
     n <= m *)
(* The inductive construction implies that these two rules are the *)
(*only ways to populate the relation.*)
(* Now the theorem:*)
(* ltnP :  forall m n : nat, ltn_xor_geq m n (n <= m)(m < n)*)
(*proves that for any two natural numbers m and n, there are only two*)
(*possible situations:*)
(* - either m < n (first rule of the relation definition), and in this *)
(*case n <= m = false and m < n = true *)
(* - or n <= m (second rule of the relation definition, and in this *)
(*case n <= m = true and m < n = false *)
(* A case analysis on this result hence generates two subgoals, one *)
(*for each constructor of ltn_xor_gep. In each subgoal the hypothesis *)
(*of the rule (repectively m < n and n <= m) appears on the stack. Also *)
(*every occurrence of (n <= m) and (m < n) is replaced by the value *)
(*imposed by the ltn_xor_gep constructor used in the branch.*)

CoInductive tuto_compare_nat (m n : nat) : bool -> bool -> bool -> Set :=
  | TCompareNatLt of m < n : tuto_compare_nat m n true false false
  | TCompareNatGt of m > n : tuto_compare_nat m n false true false
  | TCompareNatEq of m = n : tuto_compare_nat m n false false true.

(* Let's check against what is defined in the ssrnat library *)
(* CHANGE : min and max have been added *)
Lemma tuto_ltngtP : forall m n,
  compare_nat m n (minn n m) (minn m n) (maxn n m) 
	(maxn m n) (n == m) (m == n) (n <= m) (m <= n) 
    (n < m) (m < n).
Proof.
move=> m n.
rewrite !ltn_neqAle [_ == n]eq_sym; have [mn|] := ltnP m n.
  by rewrite ltnW // gtn_eqF //; constructor.
rewrite leq_eqVlt; case: ltnP; rewrite ?(orbT, orbF) => //= lt_nm eq_nm.
  by rewrite ltn_eqF //; constructor.
by rewrite eq_nm (eqP eq_nm); constructor.
Qed.
