(******************************************************************************)
(* Solutions of exercises : Type inference by canonical structures            *)
(******************************************************************************)


From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype  tuple finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(* Exercise 5.1.1                                                             *)
(******************************************************************************)
(* 2023 This has been updated to use HB *)

HB.mixin Record IsZmodule T := {
  zero : T;
  opp : T -> T;
  add : T -> T -> T;
  addA : associative add;
  addC: commutative add;
  addm0 : left_id zero add;
  add0m : left_inverse zero opp add
}.

#[short(type="zmodule")]
HB.structure Definition Zmodule := { T of IsZmodule T }.

#[verbose]
HB.instance Definition Bool_Zmodule :=
  IsZmodule.Build bool addbA addbC addFb addbb.

Notation "x \+ y" := (add x y)(at level 50,left associativity).

(* We first need to prove that zmadd is associative and commutative *)
(* The proof consists in breaking successivly the two nested records *)
(*to recover all the ingredients present in the zmodule_mixin. Then *)
(*the goal becomes trivial because the associative and commutative *)
(*requirements were present in the spec. *)
(* Update with HB, associativity and commutativity are available directly *)

Lemma zmaddA : forall m : zmodule, associative (@add m).
Proof. move=> m; apply: addA. Qed.

Lemma zmaddC : forall m : zmodule, commutative (@add m).
Proof. move=> m; apply: addC. Qed.


(* No we can conveniently prove the lemma *)
(* The ssreflect rewrite tactic allows rewrite redex selection by *)
(* pattern, and this is used here to select the occurrence where *)
(* commutativity should be used.*)
Lemma zmaddAC : forall (m : zmodule)(x y z : m), x \+ y \+ z = x \+ z \+ y.
Proof.
by move=> M x y z; rewrite -zmaddA [y \+ _]zmaddC zmaddA.
Qed.

(******************************************************************************)
(* Exercise 5.2.1                                                             *)
(******************************************************************************)

(* Be aware that the Print command shows terms as they are represented *)
(*by the system, which is possibliy syntactically slightly different *)
(*from the definition typed by the user (specially in the case of *)
(*nested pattern matching *)

HB.about hasDecEq.
HB.about hasDecEq.eq_op.
HB.about hasDecEq.eqP.

Print eqn.
Check @eqnP.

Print eqb.
Check @eqbP.

(* Look for nat, bool, Equality.sort in the answer of the command: *)
Print Canonical Projections.
(* The equations stored after these declarations are respectively :
eqn <- hasDecEq.eq_op ( ssrnat.HB_unnamed_factory_1 )
BinNat.N.eqb <- hasDecEq.eq_op ( ssrnat.HB_unnamed_factory_3 )
eqb <- hasDecEq.eq_op ( HB_unnamed_factory_4 )

[ Equality.sort ? == nat  ] => ? = nat_eqType
[ Equality.sort ? == bool ] => ? = bool_eqType
*)


(******************************************************************************)
(* Exercise 5.2.2                                                             *)
(******************************************************************************)

(* This script uses a complex intro pattern: the apply: (iffP andP) *)
(*tactic breaks the reflect goal into two subgoals for each *)
(*implication, while interpreting the first assumption of each *)
(*generated sugoal with the andP view. Then the [[] | [<- <- ]] // *)
(*intropattern simultaneously describes the introduction operations *)
(*performed on the two subgoals:*)
(*- on the first subgoal the [] casing intropattern splits the *)
(*conjunction hypothesis into two distinct assumptions.*)
(*   - on the second hypothesis the  [<- <- ] is composed of a [] *)
(*casing intropattern and two <- rewrite intropatterns. [] performs an *)
(*injection on the equality, generating two equalities, one for each *)
(*components of the pairs.  Then both equalities are rewritten form *)
(*left to right by <- <-.  This subgoal is now trivial hence closed by *)
(*// *)
Lemma tuto_pair_eqP : forall T1 T2, Equality.axiom (@pair_eq T1 T2).
Proof. 
move=> T1 T2 [u1 u2] [v1 v2] /=. 
apply: (iffP andP) => [[]|[<- <-]] //.
by do 2!move/eqP->.
Qed.


(******************************************************************************)
(* Exercise 5.3.1                                                             *)
(******************************************************************************)
Section SeqMem.

Variable T : eqType.

Implicit Type s : seq T.
Implicit Types x y : T.

Lemma tuto_in_cons : forall y s x,
  (x \in y :: s) = (x == y) || (x \in s).
Proof. by []. Qed.

(* by [] is an alternative syntax for the done tactic *)
Lemma tuto_in_nil : forall x, (x \in [::]) = false.
Proof. by []. Qed.

Lemma tuto_mem_seq1 : forall x y, (x \in [:: y]) = (x == y).
Proof. by move=> x y; rewrite in_cons orbF. Qed.

(* Here we do not even need to name the elements introduced since they *)
(*will never be used later in the script. We let the system choose *)
(*names using the move=> * tactic. *)
Lemma tuto_mem_head : forall x s, x \in x :: s.
Proof.  by move=> *; exact: predU1l. Qed.

(******************************************************************************)
(* Exercise 5.3.2                                                             *)
(******************************************************************************)

Lemma tuto_mem_cat : forall x s1 s2,
  (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Proof.
by move=> x s1 s2; elim: s1 => //= y s1 IHs; rewrite !inE /= -orbA -IHs.
Qed.

Lemma tuto_mem_behead: forall s, {subset behead s <= s}.
Proof. move=> [|y s] x //; exact: predU1r. Qed.

Fixpoint tuto_has (a : pred T) s := 
  if s is x :: s' then a x || tuto_has a s' else false.

Lemma tuto_hasP : forall (a : pred T) s,
  reflect (exists2 x, x \in s & a x) (has a s).
Proof.
move=> a; elim=> [|y s IHs] /=; first by right; case.
case ay: (a y); first by left; exists y; rewrite ?mem_head.
apply: (iffP IHs) => [] [x ysx ax]; exists x => //; first exact: mem_behead.
Search _ (_ \in cons _ _).
by move: ysx ax; rewrite in_cons; case/orP=> //; move/eqP->; rewrite ay.
Qed.

(* In fact, the last line of the previous script can be simplified by *)
(*the use of the predU1P view lemma. This is possible since the mem *)
(*function on sequences is exactly programmed as required by the statement *)
(*of predU1P. *)


Lemma tuto_hasP_alt: forall (a : pred T) s,
  reflect (exists2 x, x \in s & a x) (has a s).
Proof.
move=> a; elim=> [|y s IHs] /=; first by right; case.
case ay: (a y); first by left; exists y; rewrite ?mem_head.
apply: (iffP IHs) => [] [x ysx ax]; exists x => //; first exact: mem_behead.
by case: (predU1P ysx) ax => [->|//]; rewrite ay.
Qed.


Fixpoint tuto_all a s := if s is x :: s' then a x && tuto_all a s' else true.

(* We again use predU1P to shortcut the combination of incons and eqP *)
Lemma tuto_allP : forall (a : pred T) s,
    reflect (forall x, x \in s -> a x) (all a s).
Proof.
Proof.
move=> a; elim=> [|x s IHs]; first by left.
rewrite /= andbC; case: IHs => IHs /=.
  apply: (iffP idP) => [Hx y|]; last by apply; exact: mem_head.
  by case/predU1P=> [->|Hy]; auto.
by right; move=> H; case IHs; move=> y Hy; apply H; exact: mem_behead.
Qed.

End SeqMem.