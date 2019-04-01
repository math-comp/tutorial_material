From mathcomp Require Import all_ssreflect.

Module  easy.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:
    - look for lemmas supporting contrapositive reasoning
    - use the eqP view to finish the proof.
*)
Lemma bool_gimmics1 a : a != a.-1 -> a != 0.
(*D*)Proof. by apply: contra; move => /eqP E; rewrite E. Qed.

(** *** Exercise 2:
   - it helps to find out what is behind [./2] and [.*2] in order to [Search]
   - any proof would do, but there is one not using [implyP]
*)
Lemma view_gimmics1 p a b : p -> (p ==> (a == b.*2)) -> a./2 = b.
(*D*)Proof. by move=> -> /eqP->; exact: doubleK. Qed.

(** *** Exercise 3:
  - Prove this view by unfolding maxn and then using [leqP]
*)
Lemma maxn_idPl m n : reflect (maxn m n = m) (m >= n).
Proof. apply: (iffP idP).
(*D*)by rewrite /maxn; case: leqP.
(*D*)by move=> <-; rewrite /maxn; case: leqP.
Qed.

(** *** Exercise 4:
  - there is no need to prove [reflect] with [iffP]: here just use [rewrite] and [apply]
  - check out the definitions and theory of [leq] and [maxn]
  - proof sketch:
<<
   n <= m = n - m == 0
          = m + n - m == m + 0
          = maxn m n == m
>> *)
Lemma maxn_idPl_bis m n : reflect (maxn m n = m) (m >= n).
(*D*)Proof. by rewrite -subn_eq0 -(eqn_add2l m) addn0 -maxnE; apply: eqP. Qed.

End easy.



Module reflect1.


(** *** Exercise 5:
- Prove some reflection lemmas for the proposed  reflect definition 
 *)

(** 
- A possible definition for reflect 
 *)

Inductive reflectl (P : Prop) b :=
 | RT (p : P) (e : b = true)
 | RF (p : ~ P) (e : b = false).
About reflect.


Lemma andP (b1 b2 : bool) : reflectl (b1 /\ b2) (b1 && b2).
Proof.
(*D*)by case: b1; case: b2; [ left | right => //= [[l r]] ..].
Qed.

Lemma orP (b1 b2 : bool) : reflectl (b1 \/ b2) (b1 || b2).
Proof.
(*D*)case: b1; case: b2; [ left; by [ move | left | right ] .. |].
(*D*)by right=> // [[l|r]].
Qed.

Lemma implyP (b1 b2 : bool) : reflectl (b1 -> b2) (b1 ==> b2).
Proof.
(*D*)by case: b1; case: b2; [ left | right | left ..] => //= /(_ isT).
Qed.

End reflect1.





(** *** Exercise 6:
- Get excluded-middle when P is equivalent to a "bool" "decidable"
 *)

(** Equivalence definition *)

Definition bool_Prop_equiv (P : Prop) (b : bool) := b = true <-> P.
Lemma test_bool_Prop_equiv b P : bool_Prop_equiv P b -> P \/ ~ P.
Proof.
(*D*)case: b; case => hlr hrl.
(*D*)  by left; apply: hlr.
(*D*)by right => hP; move: (hrl hP).
Qed.

(** *** Exercise 7:
- Let's use standard reflect (and iffP, idP etc...)
 *)
Lemma iffP_lr (P : Prop) (b : bool) :
  (P -> b) -> (b -> P) -> reflect P b.
Proof.
(*D*)by move=> *; apply: (iffP idP).
Qed.

Lemma iffP_rl (P : Prop) (b : bool) :
  reflect P b -> ((P -> b) /\ (b -> P)).
Proof.
(*D*) by case: b; case=> p; split. 
Qed.


Lemma eqnP {n m : nat} :
  reflect (n = m) (eqn n m).
Proof.
(*D*)apply: (iffP idP) => [|->]; last by elim: m.
(*D*)by elim: n m => [[]|n IH [//|m] /IH ->].
Qed.


(** *** Exercise 8:
If you have time.. more reflections

- leq_max : use leq_total maxn_idPl
- dvdn_fact: use leq_eqVlt dvdn_mulr dvdn_mull
 *)

Lemma nat_inj_eq T (f : T -> nat) x y :
  injective f ->
    reflect (x = y) (eqn (f x) (f y)).
Proof. 
(*D*)by move=> f_inj; apply: (iffP eqnP) => [/f_inj|-> //]. 
Qed.

Lemma leq_max m n1 n2 : (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
(*D*)wlog le_n21: n1 n2 / n2 <= n1 => [th_sym|].
(*D*)  by case/orP: (leq_total n2 n1) => /th_sym; last rewrite maxnC orbC.
(*D*)by rewrite (maxn_idPl le_n21) orb_idr // => /leq_trans->.
Qed.


Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Proof.
(*D*)case: m => //= m; elim: n => //= n IHn; rewrite ltnS leq_eqVlt.
(*D*)by case/orP=> [/eqP-> | /IHn]; [apply: dvdn_mulr | apply: dvdn_mull].
Qed.

Lemma prime_above m : exists2 p, m < p & prime p.
Proof.
(*D*)have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
(*D*)exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
(*D*)by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.

(** 
For this section:                                                   
   only move=> h, move/V: h => h, case/V: h, by ... allowed         
 *)

Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
(*D*) move=> P Q h hp. by move/h: hp => hp.
Qed.

Goal forall (P : nat -> Prop) (Q : Prop),
     (P 0 -> Q)
  -> (forall n, P n.+1 -> P n)
  -> P 4 -> Q.
Proof.
(*D*) move=> P Q P0Q Hp.
(*D*) by move/Hp/Hp/Hp/Hp.
Qed.


(**  No case analysis on b, b1, b2 allowed  *)
Goal forall (b b1 b2 : bool), (b1 -> b) -> (b2 -> b) -> b1 || b2 -> b.
Proof. 
(*D*) move=> b b1 b2 h1 h2 h. case/orP: h.
(*D*)   by move/h1.
(*D*)   by move/h2.
Qed.

Goal forall (Q : nat -> Prop) (p1 p2 : nat -> bool) x,
  ((forall y, Q y -> p1 y /\ p2 y) /\ Q x) -> p1 x && p2 x.
Proof.
(*D*) move=> Q p1 p2 x h. case: h. move=> /(_ x) h qx.
(*D*) move/h: qx. by move/andP.
Qed.

Goal forall (Q : nat -> Prop) (p1 p2 : nat -> bool) x,
  ((forall y, Q y -> p1 y \/ p2 y) /\ Q x) -> p1 x || p2 x.
Proof.
(*D*) move=> Q p1 p2 x h. case: h. move=> /(_ x) h qx.
(*D*) move/h: qx. by move/orP.
Qed.

(** 
 No xxxP lemmas allowed, but reflectT and reflectF and case analysis allowed ,                                            
 *)
Lemma myidP: forall (b : bool), reflect b b.
Proof.
(*D*) move=> b; case: b.
(*D*)   exact: ReflectT.
(*D*)   exact: ReflectF.
Qed.

Lemma mynegP: forall (b : bool), reflect (~ b) (~~ b).
Proof.
(*D*) move=> b. case: b.
(*D*)   exact: ReflectF.
(*D*)   exact: ReflectT.
Qed.

Lemma myandP: forall (b1 b2 : bool), reflect (b1 /\ b2) (b1 && b2).
Proof.
(*D*) move=> b1 b2. case: b1.
(*D*)  case b2.
(*D*)    exact: ReflectT.
(*D*)    apply: ReflectF. move=> h. by case: h.
(*D*)  case b2.
(*D*)    apply: ReflectF. move=> h. by case: h.
(*D*)    apply: ReflectF. move=> h. by case: h.
Qed.

Lemma myiffP:
  forall (P Q : Prop) (b : bool),
    reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Proof.
(*D*) move=> P Q b Pb PQ QP. move: Pb. case: b.
(*D*)   move=> h. case: h.
(*D*)     move/PQ=> hp. by apply: ReflectT.
(*D*)     move=> hNp. apply: ReflectF. move/QP=> hp.
(*D*)     by move/hNp: hp.
(*D*)   move=> h. case: h.
(*D*)     move/PQ=> hq. by apply: ReflectT.
(*D*)     move=> hNp. apply: ReflectF. move/QP=> hp.
(*D*)     by move/hNp: hp.
Qed.


(** 
  Some arithmetics                                        
 *)

Fixpoint len (n m : nat) : bool :=
  match n, m with
  | 0    , _     => true
  | n'.+1, 0     => false
  | n'.+1, m'.+1 => len n' m'
  end.

Lemma lenP: forall n m, reflect (exists k, k + n = m) (len n m).
Proof.
(*D*) move=> n; elim: n.
(*D*)   move=> m. apply: (iffP idP).
(*D*)     move=> _. by exists m.
(*D*)     by [].
(*D*)   move=> n IH m. apply: (iffP idP).
(*D*)     case: m. by [].
(*D*)       move=> m /= le_nm. move/IH: le_nm=> le_nm.
(*D*)       case: le_nm. move=> k eq_xk_m. exists k.
(*D*)       by rewrite -eq_xk_m addnS.
(*D*)     case: m.
(*D*)       case. move=>k. by rewrite addnS.
(*D*)       move=> m h. case: h => k.
(*D*)       rewrite addnS. move=> eq_kSn_k. case: eq_kSn_k.
(*D*)       move=> eq_kn_m. apply/IH. by exists k.
Qed.


(* --------------------------------------------------------------------*)
