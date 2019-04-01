From mathcomp Require Import all_ssreflect.

Module  easy.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:
    - look for lemmas supporting contrapositive reasoning
    - use the eqP view to finish the proof.
*)
Lemma bool_gimmics1 a : a != a.-1 -> a != 0.

(** *** Exercise 2:
   - it helps to find out what is behind [./2] and [.*2] in order to [Search]
   - any proof would do, but there is one not using [implyP]
*)
Lemma view_gimmics1 p a b : p -> (p ==> (a == b.*2)) -> a./2 = b.

(** *** Exercise 3:
  - Prove this view by unfolding maxn and then using [leqP]
*)
Lemma maxn_idPl m n : reflect (maxn m n = m) (m >= n).
Proof. apply: (iffP idP).
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
Qed.

Lemma orP (b1 b2 : bool) : reflectl (b1 \/ b2) (b1 || b2).
Proof.
Qed.

Lemma implyP (b1 b2 : bool) : reflectl (b1 -> b2) (b1 ==> b2).
Proof.
Qed.

End reflect1.





(** *** Exercise 6:
- Get excluded-middle when P is equivalent to a "bool" "decidable"
 *)

(** Equivalence definition *)

Definition bool_Prop_equiv (P : Prop) (b : bool) := b = true <-> P.
Lemma test_bool_Prop_equiv b P : bool_Prop_equiv P b -> P \/ ~ P.
Proof.
Qed.

(** *** Exercise 7:
- Let's use standard reflect (and iffP, idP etc...)
 *)
Lemma iffP_lr (P : Prop) (b : bool) :
  (P -> b) -> (b -> P) -> reflect P b.
Proof.
Qed.

Lemma iffP_rl (P : Prop) (b : bool) :
  reflect P b -> ((P -> b) /\ (b -> P)).
Proof.
Qed.


Lemma eqnP {n m : nat} :
  reflect (n = m) (eqn n m).
Proof.
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
Qed.

Lemma leq_max m n1 n2 : (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
Qed.


Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Proof.
Qed.

Lemma prime_above m : exists2 p, m < p & prime p.
Proof.
Qed.

(** 
For this section:                                                   
   only move=> h, move/V: h => h, case/V: h, by ... allowed         
 *)

Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
Qed.

Goal forall (P : nat -> Prop) (Q : Prop),
     (P 0 -> Q)
  -> (forall n, P n.+1 -> P n)
  -> P 4 -> Q.
Proof.
Qed.


(**  No case analysis on b, b1, b2 allowed  *)
Goal forall (b b1 b2 : bool), (b1 -> b) -> (b2 -> b) -> b1 || b2 -> b.
Proof. 
Qed.

Goal forall (Q : nat -> Prop) (p1 p2 : nat -> bool) x,
  ((forall y, Q y -> p1 y /\ p2 y) /\ Q x) -> p1 x && p2 x.
Proof.
Qed.

Goal forall (Q : nat -> Prop) (p1 p2 : nat -> bool) x,
  ((forall y, Q y -> p1 y \/ p2 y) /\ Q x) -> p1 x || p2 x.
Proof.
Qed.

(** 
 No xxxP lemmas allowed, but reflectT and reflectF and case analysis allowed ,                                            
 *)
Lemma myidP: forall (b : bool), reflect b b.
Proof.
Qed.

Lemma mynegP: forall (b : bool), reflect (~ b) (~~ b).
Proof.
Qed.

Lemma myandP: forall (b1 b2 : bool), reflect (b1 /\ b2) (b1 && b2).
Proof.
Qed.

Lemma myiffP:
  forall (P Q : Prop) (b : bool),
    reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Proof.
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
Qed.


(* --------------------------------------------------------------------*)
