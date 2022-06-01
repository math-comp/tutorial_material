(******************************************************************************)
(* Solutions of exercises : Type inference by canonical structures            *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype tuple finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(* Exercise 6.1.1                                                             *)
(******************************************************************************)

Lemma tuto_unit_enumP : Finite.axiom [:: tt]. Proof. by case. Qed.

Definition tuto_unit_finMixin := FinMixin tuto_unit_enumP.
Canonical Structure unit_finType := Eval hnf in FinType unit unit_finMixin.


(******************************************************************************)
(* Exercise 6.1.2                                                             *)
(******************************************************************************)

(* Here we use the multirule rewrite facility: the first rule in the *)
(*list which matches the goal is used. Note that this facility *)
(*complies with the ! and ? multiplicators. *)
Lemma tuto_option_enumP : forall T : finType, Finite.axiom (option_enum T).
Proof. by move=> T; case=> [x|]; rewrite /= count_map (count_pred0, enumP). Qed.

(******************************************************************************)
(* Exercise 6.1.3                                                             *)
(******************************************************************************)

Definition tuto_sum_enum (T1 T2 : finType) : seq (T1 + T2) :=
  map (@inl _ _) (Finite.enum T1) ++ map (@inr _ _) (Finite.enum T2).


(* We describe this script as a trace of the search for the proof.
   Note that the view mechanism used in apply/hasP complies with *)
(*negation. The first subgoal is trivial because of the equality
   between applied constructors inl and inr. (discriminate). For the
   two last subgoals, remember the [] casing intropattern perfroms an
   injection on equalities *)
Lemma tuto_sum_enum_uniq : forall T1 T2, uniq (sum_enum T1 T2).
Proof.
move=> T1 T2.
Search _ cat uniq.
rewrite cat_uniq.
Search _ uniq map.
rewrite !map_inj_uniq.
 Search _ uniq Finite.enum.
 Search _ Finite.enum.
 + rewrite -!enumT.
 Search _ (enum _) uniq.
 rewrite !enum_uniq /= andbT.
 apply/hasP => [[u]].
 case/mapP=> x hx -> /=.
 case/mapP.
 done.
 + by move=> x y [].
 + by move=> x y [].
Qed.

(* here is the clean script resulting from the proevious one *)

Lemma tuto_sum_enum_uniq_clean : forall T1 T2, uniq (sum_enum T1 T2).
Proof.
move=> T1 T2.
rewrite cat_uniq -!enumT !(enum_uniq, map_inj_uniq); try by move=> ? ? [].
by rewrite andbT; apply/hasP=> [[u]]; case/mapP=> x _ ->; case/mapP.
Qed.

(******************************************************************************)
(* Exercise 6.1.4                                                             *)
(******************************************************************************)

Check UniqFinMixin.

Definition tuto_prod_enum (T1 T2 : finType) : seq (T1 * T2) :=
  foldr (fun x1 => cat (map (pair x1) (enum T2))) [::] (enum T1).

Lemma prod_enum_uniq : forall T1 T2, uniq (tuto_prod_enum T1 T2).
Proof.
move=> T1 T2; rewrite /tuto_prod_enum; move: (enum_uniq T1) (enum_uniq T2).
elim: (enum T1) (enum T2)=> [|x1 l1 ihl1] l2 //=; case/andP=> hx1 uniq_l1 uniq_l2.
rewrite cat_uniq ihl1 // andbT map_inj_uniq; last by move=> x y [].
rewrite uniq_l2 /=; apply/hasP=> [[u]] /= h1; case/mapP=> y l2y e.
move: h1; rewrite e; elim: l1 hx1 {uniq_l1 ihl1} => [|x3 l3 ihl3 ] //=.
rewrite in_cons negb_or; case/andP=> h1 h2.
rewrite mem_cat; case/orP; last by apply: ihl3.
by case/mapP=> y' _ []; move/eqP; move/negPf: h1 => ->.
Qed.


(******************************************************************************)
(* Exercise 6.1.5                                                             *)
(******************************************************************************)

Section OpsTheory.

Variable T : finType.

Implicit Types A B C P Q : pred T.
Implicit Types x y : T.
Implicit Type s : seq T.

Lemma card0 : #|@pred0 T| = 0.
Proof. by rewrite cardE enum0. Qed.

Lemma cardT : #|T| = size (enum T).
Proof. by rewrite cardE. Qed.

Lemma card1 : forall x, #|pred1 x| = 1.
Proof. by move=> x; rewrite cardE enum1. Qed.

Lemma tuto_pred0P : forall P, reflect (P =1 pred0) (pred0b P).
Proof. move=> p; apply: (iffP eqP); [exact: card0_eq | exact: eq_card0]. Qed.

(******************************************************************************)
(* Exercise 6.1.6                                                             *)
(******************************************************************************)


Lemma tuto_cardUI : forall A B, #|[predU A & B]| + #|[predI A & B]| = #|A| + #|B|.
Proof. by move=> A B; rewrite !cardE /= !size_filter count_predUI. Qed.

Lemma tuto_eq_card : forall A B, A =i B -> #|A| = #|B|.
Proof. by move=> A B eqAB; rewrite !cardE (eq_enum eqAB). Qed.

(******************************************************************************)
(* Exercise 6.1.7                                                             *)
(******************************************************************************)

Lemma tuto_disjoint0 : forall A, [disjoint pred0 & A].
Proof. move=> A; exact/pred0P. Qed.

(* The congr tactic applies a congruence reasoning of the form *)
(* \overline{x} = \overline{y} -> f \overline{x} = f \overline{y}, *)
(* where f can be an n-ary function. It generates as many subgoals as *)
(* non-trivial pairwise equality between the arguments of f *)
Lemma tuto_disjoint_sym : forall A B, [disjoint A & B] = [disjoint B & A].
Proof. by move=> A B; congr eqn; apply: eq_card => x; apply: andbC. Qed. 


(* This is a difficult proof...And we need to investigate how disjoint is *)
(* defined. We see that its is defined using pred0b. *)
Search _ disjoint.
Print disjoint.

(* We first start a case analysis on the fact that [predI A & C] is empty *)
(* or not. *)

(* Then, one of the main trick is to avoid using congruence with pred0b, but *)
(* with == 0. Indeed, using congruence with pred0b would amount to prove *)
(* that some characteristic functions are (Leibniz) equal when they are *)
(* only extentionaly equal... *)
(* In the first subgoal, we use the ssreflect syntax to replace a subterm by a *)
(*convertible one: rewrite -[t1]/t2, where t1 is the term (or the *)
(*pattern) present in the goal and t2 the convertible counterpart. *)
(* We also use a declarative step suff, together with the -> *)
(* intropattern, which rewrites the lemms instead of introducing it *)
(* Finally, we use the move/(_ x) tactic, which specializes a *)
(* universally quantified assumption to a particular value *)
(* In the second subgoal, we use the negative counterpart of pred0P, *)
(* namely pred0Pn. Again there is no specific lemma on [predU _ & _] *)
(* and [predI _ & _], since there are in fact only boolean disjunctions *)
(* and conjunctions. Some rewrite steps might make the collective \in *)
(*momentarily disappear, replaced by the generic mem applicative *)
(*membership predicate. In that case, a simplification \= should put *)
(*back everything in order.*)
   
Lemma tuto_disjointU : forall A B C, 
  [disjoint predU A B & C] = [disjoint A & C] && [disjoint B & C].
Proof.
move=> A B C.
case dAC: ([disjoint A & C])=> /=.
  rewrite /disjoint /pred0b; congr (_ == 0); apply: eq_card=> x.
  rewrite -[x \in [predI _ & _]]/(((x \in A) || (x \in B)) && (x \in C)) andb_orl.
  suff -> :  (x \in A) && (x \in C) = false by done.
  by move/pred0P: dAC; move/(_ x).
apply/pred0P=> nABC; case/pred0Pn: dAC=> x; case/andP=> /= Ax Cx.
move: (nABC x)=> /=. 
by rewrite Cx /= -[x \in [predU A & B]]/((x \in A) || (x \in B)) Ax.
Qed.

(******************************************************************************)
(* Exercise 6.1.8                                                             *)
(******************************************************************************)
 
(* It can be usefull to browse the ssrbool library and/or to use the *)
(*Search command to find the most convenient reflexion lemmas, like *)
(*negbFE in this case *)
Lemma tuto_subsetP : forall A B,
  reflect {subset A <= B} (A \subset B).
Proof.
rewrite unlock.
move=> A B; apply: (iffP idP).
  by move/pred0P=> h x Ax; move: (h x)=> /=; rewrite Ax andbT; move/negbFE.
by move=> h; apply/pred0P=> x /=; case Ax : (x \in A); rewrite ?andbF // h.
Qed.

Lemma tuto_subsetPn : forall A B,
  reflect (exists2 x, x \in A & x \notin B) (~~ (A \subset B)).
Proof.
rewrite unlock.
move=> A B; apply: (iffP idP).
  by move/pred0Pn=> [x] /=; case/andP=> nAx Bx; exists x.
by case=> x Ax nBx; apply/pred0Pn; exists x; rewrite /= nBx.
Qed.

Lemma tuto_subset_eqP : forall A B,
  reflect (A =i B) ((A \subset B) && (B \subset A)).
Proof.
move=> A B; apply: (iffP andP) => [[sAB sBA] x| eqAB].
  by apply/idP/idP; apply: subsetP.
by rewrite !eq_subxx.
Qed.


(* In this proof, the tactic case/idP: (ltnn #|A|) on a False goal *)
(* proves false from (ltnn #|A|) := #|A| < #|A| = false, and generates *)
(*a new subgoal to prove that the current context implies  #|A| < #|A| *)
Lemma tuto_subset_cardP : forall A B,
  #|A| = #|B| -> reflect (A =i B) (A \subset B).
Proof.
move=> A B eqcAB; case: (@subsetP _ A B) (@subset_eqP _ A B) => //= sAB.
case: (@subsetP _ B A) => [//|[]] x Bx; apply/idPn => Ax.
case/idP: (ltnn #|A|); rewrite {2}eqcAB (cardD1 x B) Bx /=.
apply: subset_leq_card; apply/subsetP=> y Ay; rewrite inE /= andbC.
by rewrite sAB //; apply/eqP => eqyx; rewrite -eqyx Ay in Ax.
Qed.

End OpsTheory.

(******************************************************************************)
(* Exercise 6.1.9                                                             *)
(******************************************************************************)

Section Quantifiers.

Variable T : finType.
Variable P : pred T.

Lemma tuto_existsP : reflect (exists x, P x) [exists x, P x].
Proof. by apply: (iffP pred0Pn); case=> x; exists x. Qed.

Lemma tuto_forallP : reflect (forall x, P x) [forall x, P x].
Proof.
by apply: (iffP pred0P) => P_ x /=; rewrite ?P_ ?(negbFE (P_ x)).
Qed.

Lemma tuto_negb_forall :  ~~ [forall x, P x] = [exists x, ~~ P x].
Proof.  by []. Qed.

Lemma tuto_negb_exists : ~~ [exists x, P x] = [forall x, ~~ P x].
Proof.
rewrite negbK; congr (_ == 0); apply: eq_card => x.
by rewrite !inE /= negbK.
Qed.

End Quantifiers.
(******************************************************************************)
(* Exercise 6.1.10                                                            *)
(******************************************************************************)

Section Extremas.

Variable T : finType.
Variable P : pred T.
Variable F : T -> nat.

(* P is non empty *)
Variable i0 : T.
Hypothesis Pi0 : P i0.

(* The small scale reflection methodology leads to defining boolean *)
(*predicates as often as possible *)

(* We hence first define a boolean predicate characterizing an *)
(*extremum of F for the arbirary boolean relation ord *)

(* We use here the ssreflect notation to define predicates :
[pred i | p i] defines the predicate (i => p i) *)

(* We also use the boolean implication ==> *)
Definition is_extremum ord := 
  [pred i | P i && [forall x, P x ==> ord (F i) (F x)]].

(* Now let's characterize the notion of extremum in a logical (Prop) *)
(*way *)
Inductive extremum_spec (ord : rel nat) : T -> Prop :=
  ExtremumSpec i of P i & (forall j, P j -> ord (F i) (F j))
  : extremum_spec ord i.

(* Being minimimum for F is being extremum for leq *)
Definition is_min := is_extremum leq.

(* Being maxmimum for F is being extremum for geq *)
Definition is_max := is_extremum geq.


(* Now the pick function extracts a witness for a given predicates, *)
(*under the form of an option type. The odflt operator lifts an *)
(*element of the option type (option T) back to T by assigning a *)
(*default value to None. Here the default value is i0, the *)
(*nonemptiness witness *)
Definition Fmin := odflt i0 [pick x | is_min x].

Definition Fmax := odflt i0 [pick x | is_max x].

(* Let us prove that Fmin is an extremum for leq *)
(* The specification of the pick operation is pickP *)
(* The specification of the ex_minn operation is ex_minnP. Applying it *)
(*to a proof that a nat predicates is non empty generates the value *)
(*and its minimality property *)
Lemma Fmin_correct : extremum_spec leq Fmin.
rewrite /Fmin; case: pickP => [i | no_i] /=.
  by case/andP=> Pi; move/forallP=> min_i; split=> // j; exact/implyP.
pose Fvals i := [exists x, P x && (F x == i)].
have exFval : exists n, Fvals n.
  by exists (F i0); rewrite /Fvals; apply/existsP; exists i0; rewrite Pi0 eqxx.
case/ex_minnP: exFval=> m; case/existsP=> j; case/andP=> Pj e m_is_min.
case/idP: (no_i j); rewrite /= Pj; apply/forallP=> x; apply/implyP=> Px.
by rewrite (eqP e); apply: m_is_min; apply/existsP; exists x; rewrite eqxx Px.
Qed.

(* here we need to show that F is bounded on T. In fact, the explicit *)
(* value of the maximum of F on the whole finType T can be computed by *)
(*iterating the binary  maximum operator maxn on the enumeration of *)
(*the elements of T. We show that it is a correct bound by induction *)
(*on the list enumerating the lements of T *)

Lemma Fmax_correct : extremum_spec geq Fmax.
Proof.
rewrite /Fmax; case: pickP => [i | no_i].
  by case/andP=> Pi; move/forallP=> max_i; split=> // j; exact/implyP.
pose Fvals i := [exists x, P x && (F x == i)].
have exFval : exists n, Fvals n.
  by exists (F i0); rewrite /Fvals; apply/existsP; exists i0; rewrite Pi0 eqxx.
have: forall n, Fvals n -> n <= foldr maxn 0 (map F (enum P)).
  move=> n; case/existsP=> i; rewrite -[P i]mem_enum andbC; case/andP.
  move/eqP <-; elim: (enum P) => //= j e IHe.
  rewrite inE => /orP[/eqP->|/IHe /leq_trans->//]; first by rewrite leq_maxl.
  exact: leq_maxr.
case/ex_maxnP=> // n ex_i max_i; case/pred0P: ex_i => i.
apply/andP=> [[Pi def_n]]; case/idP: (no_i i); rewrite /= Pi.
apply/forallP=> j; apply/implyP=> Pj; rewrite (eqP def_n) max_i //;apply/existsP.
by exists j; rewrite eqxx Pj.
Qed.

End Extremas.
(******************************************************************************)
(* Exercise 6.1.11 to 6.1.21                                                  *)
(******************************************************************************)

(* The solution is the begining of the path.v file. Copy and play... *)

(******************************************************************************)
(* Exercise 6.2.1                                                             *)
(******************************************************************************)

Section Def.

Variable n : nat.
Variable T : Type.
(* The coercion is defined on the fly by the :> mark *)
Structure tuto_tuple_of  : Type := 
  TutoTuple {tuto_tval :> seq T; _ : size tuto_tval == n}.

Canonical Structure tuple_subType :=
  Eval hnf in [subType for tuto_tval].

End Def.

Canonical Structure nil_tuto_tuple (T : Type) :=
   TutoTuple (erefl _ : @size T [::] == 0).

Canonical Structure cons_tuto_tuple n T x (t : tuto_tuple_of n T) :=
   TutoTuple (valP t : size (x :: t) == n.+1).

Lemma tuto_cat_tupleP : forall T n1 n2 (t1 : n1.-tuple T) (t2 : n2.-tuple T),
  size (t1 ++ t2) == n1 + n2.
Proof. by move=> T n1 n2 t1 t2; rewrite size_cat !size_tuple. Qed.
Canonical Structure cat_tuple T n1 n2 t1 t2 := Tuple (@cat_tupleP T n1 n2 t1 t2).


Lemma drop_tupleP : forall T n m (t : n.-tuple T), size (drop m t) == n - m.
Proof. by move=> T n m t; rewrite size_drop size_tuple. Qed.

Canonical Structure drop_tuple T n m t := Tuple (@drop_tupleP T n m t).

Lemma take_tupleP : forall T n m (t : n.-tuple T), size (take m t) == minn m n.
Proof. by move=> T n m t; rewrite size_take size_tuple eqxx. Qed.

Canonical Structure take_tuple T n m t := Tuple (@take_tupleP T n m t).

Lemma rot_tupleP : forall T n m (t : n.-tuple T), size (rot m t) == n.
Proof. by move=> T n m t; rewrite size_rot size_tuple. Qed.

Canonical Structure rot_tuple T n m t := Tuple (@rot_tupleP T n m t).

(******************************************************************************)
(* Exercise 6.2.1                                                             *)
(******************************************************************************)

Section TuplesExercises.

(* Note that this time we need a finType, so that cardinality is well *)
(*defined *)
Variables (T : finType)(n : nat).

Lemma tuto_size_tuple : forall (t : n.-tuple T), size t = n.
Proof. move=> f; exact: (eqP (valP f)). Qed.

Lemma leq_card_tuple : forall (t : n.-tuple T), #|t| <= n.
Proof. by move=> t; move: (card_size t); rewrite size_tuple. Qed.

Lemma uniq_card_tuple : forall (t : n.-tuple T), uniq t -> #|t| = n.
Proof. by move=> t; move/card_uniqP; rewrite size_tuple. Qed.

Search _"'I_ _".
Print ordinal.

(* The subtype is defined by:

Section OrdinalSub.

Variable n : nat.

Inductive ordinal : predArgType := Ordinal m of m < n.

Canonical Structure ordinal_subType :=
  [subType for nat_of_ord].

End OrdinalSub.
*)

Lemma tuto_tnth_nth : forall (x : T) (t : n.-tuple T) i, tnth t i = nth x t i.
Proof. by move=> x t i; apply: set_nth_default; rewrite size_tuple. Qed.


(******************************************************************************)
(* Exercise 6.2.3                                                             *)
(******************************************************************************)

(* A first possibility uses the constructor of the ordinal inductive *)
(* type *)

Definition two := Ordinal (ltnSn 2).
Check two.
Eval compute in (val two).


(* Orelse we can cast the definition with the expected type and use *)
(*the generic subType constructor Sub *)
Definition two' : [subType of 'I_3] := Sub 2 (ltnSn 3).
Check (two' : 'I_3).

(* But in fact we only need to claim that the boolean test will *)
(*evaluate to true, and let the system check that for us *)
Definition two'' : [subType of 'I_3] := Sub 2 (refl_equal true).
Check two''.
Eval compute in (val two'').

Inductive odds : Set := Odds x of (odd x).

(* As opposed to the tuple case, this time the function from odds to *)
(*the type it should be a subtype of has to be defined manually*)
Definition nat_of_odds i := let: Odds m _ := i in m.

(* And now the subType definition, which should declared as canonical *)
Canonical Structure odds_subType :=
  Eval hnf in [subType for nat_of_odds by odds_rect].

(* Check that this require a canonical structure by replacing above
Canonical Structure odds_subType := by Definition .... := *)
Definition three : odds := Sub 3 (refl_equal true).

(******************************************************************************)
(* Exercise 6.2.4                                                             *)
(******************************************************************************)


(* WARNING : to be effective when the library where they are defined *)
(*is loaded, canonical structures should be defined (or re-defined) *)
(*outside sections... *)
Definition odds_eqMixin := Eval hnf in [eqMixin of odds by <:].

Canonical Structure odds_eqType := Eval hnf in EqType odds odds_eqMixin.

Definition tuto_tuple_eqMixin := Eval hnf in [eqMixin of n.-tuple T by <:].

Canonical Structure tuto_tuple_eqType :=
  Eval hnf in EqType (n.-tuple T) tuto_tuple_eqMixin.

Lemma tuto_map_tnth_enum : forall (t : n.-tuple T),
   map (tnth t) (enum 'I_n) = t.
Proof.
move=> t; case def_t: {-}(val t) => [|x0 t'].
  by rewrite [enum _]size0nil // -cardE card_ord -(size_tuple t) def_t.
apply: (@eq_from_nth _ x0) => [|i]; rewrite size_map.
  by rewrite -cardE size_tuple card_ord.
move=> lt_i_e; have lt_i_n: i < n by rewrite -cardE card_ord in lt_i_e.
by rewrite (nth_map (Ordinal lt_i_n)) // (tnth_nth x0) nth_enum_ord.
Qed.

Lemma tuto_eq_from_tnth : forall (t1 t2 : n.-tuple T),
  tnth t1 =1 tnth t2 -> t1 = t2.
Proof.
move=> *; apply: val_inj; rewrite /= -2!map_tnth_enum; exact: eq_map.
Qed.


End TuplesExercises.

(******************************************************************************)
(* Exercise 6.3.1                                                             *)
(******************************************************************************)

Section setOpsExos.

Variable T : finType.

Implicit Types a x : T.
Implicit Types A B C D : {set T}.

Lemma tuto_eqEsubset : forall A B,
   (A == B) = (A \subset B) && (B \subset A).
Proof. by move=> A B; apply/eqP/subset_eqP; move/setP. Qed.

Lemma tuto_set1P : forall x a, reflect (x = a) (x \in [set a]).
Proof. move=> x a; rewrite inE; exact: eqP. Qed.

Lemma tuto_setD1P : forall x A b,
  reflect (x != b /\ x \in A) (x \in A :\ b).
Proof. move=> x A b; rewrite !inE; exact: andP. Qed.

Lemma tuto_setIA : forall A B C, A :&: (B :&: C) = A :&: B :&: C.
Proof. by move=> A B C; apply/setP=> x; rewrite !inE andbA. Qed.

Lemma tuto_setUIl : forall A B C,
   (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
Proof. by move=> A B C; apply/setP => x; rewrite !inE orb_andl. Qed.

Lemma tuto_setCU : forall A B, ~: (A :|: B) = ~: A :&: ~: B.
Proof. by move=> A B; apply/setP => x; rewrite !inE -negb_or. Qed.

End setOpsExos.

(******************************************************************************)
(* Exercise 6.3.2                                                             *)
(******************************************************************************)


Section MinSet.

Variable T : finType.
Notation sT := {set T}.

Implicit Types A B C : sT.
Implicit Type P : pred sT.

Definition tuto_minset P A := 
  [forall B : sT, (B \subset A) ==> ((B == A) == P B)].

Lemma tuto_minset_eq : forall P1 P2 A,
  P1 =1 P2 -> minset P1 A = minset P2 A.
Proof. by move=> P1 P2 A eP12; apply: eq_forallb => B; rewrite eP12. Qed.

Lemma tuto_minsetP : forall P A,
reflect ((P A) /\ (forall B, P B -> B \subset A -> B = A))
       (minset P A).
Proof.
move=> P A; apply: (iffP forallP) => [minA | [PA minA] B].
  split; first by have:= minA A; rewrite subxx eqxx /=; move/eqP.
  by move=> B PB sBA; have:= minA B; rewrite PB sBA /=; do 2!move/eqP.
apply/implyP=> sBA; apply/eqP; apply/eqP/idP=> [-> //|]; move/minA; exact.
Qed.

Lemma tuto_minsetp : forall P A, minset P A -> P A.
Proof.  by move=> P A; case/minsetP. Qed.


Lemma tuto_minsetinf : forall P A B,
  minset P A -> P B -> B \subset A -> B = A.
Proof. by move=> P A B; case/minsetP=> _; exact. Qed.

Lemma tuto_ex_minset : forall P, (exists A, P A) -> {A | minset P A}.
Proof.
move=> P exP; pose pS n := [pred B | P B && (#|B| == n)].
pose p n := ~~ pred0b (pS n); have{exP}: exists n, p n.
  by case: exP => A PA; exists #|A|; apply/existsP; exists A; rewrite PA /=.
case/ex_minnP=> n; move/pred0P; case: (pickP (pS n)) => // A.
case/andP=> PA; move/eqP=> <- {n} _ minA; exists A => //.
apply/minsetP; split=> // B PB sBA; apply/eqP; rewrite eqEcard sBA.
by apply: minA; apply/pred0Pn; exists B; rewrite /= PB /=.
Qed.

Lemma tuto_minset_exists : forall P C,
   P C -> {A | minset P A & A \subset C}.
Proof.
move=> P C PC; have{PC}: exists A, P A && (A \subset C).
  by exists C; rewrite PC /=.
case/ex_minset=> A; case/minsetP; case/andP=> PA sAC minA; exists A => //.
apply/minsetP; split=> // B PB sBA; apply: minA => //.
by rewrite PB (subset_trans sBA).
Qed.

End MinSet.


