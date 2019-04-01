(** Cheat sheet available at
      #<a href='https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf'>https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf</a>#
*)

From mathcomp Require Import all_ssreflect.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** 
    Try to prove the following theorems using no
    lemma and minimizing the number of applications of
    the tactic case
*)

(** *** Exercise 1:
*)

Lemma andTb p : true && p = p.
(*D*)Proof. by []. Qed.

(** *** Exercise 2:
*)

Lemma andbT p : p && true = p.
(*D*)Proof. by case: p. Qed.

(** *** Exercise 3:
*)

Lemma orbC p q : p || q = q || p.
(*D*)Proof. by case: p; case: q. Qed.

(** *** Exercise 4:
*)
Goal forall p q,    (p && q) || (   p && ~~ q) || 
                 (~~ p && q) || (~~ p && ~~ q). 
(*D*)Proof. by move=> p q; case: p; case: q. Qed.

(** *** Exercise 5 :
*)
Goal forall p q r, (p || q) && r = r && (p || q).
(*D*)Proof. by move=> p q r; case: (p || q); case: r. Qed.

Goal forall n, n < n.+1.
by [].
Qed.

(** *** Exercise 6  :
   - look up what [==>] 
*)
(*D*)Locate "==>".
(*D*)Print implb.
Lemma implybE p q : p ==> q = ~~ p || q.
(*D*) Proof. by case: p. Qed.

(** *** Exercise 7  :
    Try to prove using the case tactic and alternatively
    without using the case tactic
*)

Lemma negb_imply p q : ~~ (p ==> q) = p && ~~ q.
(*D*) (* Proof. by case: p. Qed. *)
(*D*) Proof. by rewrite implybE negb_or negbK. Qed.


(** *** Exercise 8  :
    Try to prove using the case tactic and alternatively
    without using the case tactic
*)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
(*D*) (* Proof. by case: p; case: q. Qed. *)
(*D*) Proof. by rewrite implybE negb_imply implybE orbK orNb. Qed.


(** *** Exercise 9 :
    - what is [(+)] ?
    - prove this using move and rewrite
*)
Lemma find_me p q :  ~~ p = q -> p (+) q.
(*D*)Locate "(+)".
(*D*)Search _ addb negb.
(*D*)Proof. by move=> np_q; rewrite -np_q addbN negb_add. Qed.


(** ***
    maxn defines the maximum of two numbers 
*)

Print maxn.
Search maxn in ssrnat.

(** ***
    We define the maxinum of three number as 
    folllow  
*)

Definition max3n a b c :=
   if a < b then maxn b c else maxn a c.

(** ***
    Try to prove the following theorem
    (you may use properties of maxn)
*)


(** *** Exercise 10
*)

Lemma max3n3n a : max3n a a a = a.
(*D*) Proof. by rewrite /max3n if_same maxnn. Qed.

(** *** Exercise 11
*)
Lemma max3E a b c : max3n a b c = maxn (maxn a b) c.
(*D*) Proof. by rewrite /max3n /maxn; case: (a < b). Qed.

(** *** Exercise 12
*)
Lemma max3n_213 a b c : max3n a b c = max3n b a c.
(*D*) Proof. by rewrite max3E (maxnC a) -max3E. Qed.

(** *** Exercise 13
*)
Lemma max3n_132 a b c : max3n a b c = max3n a c b.
(*D*) Proof. by rewrite max3E -maxnA (maxnC b) maxnA -max3E. Qed.

(** *** Exercise 14
*)
Lemma max3n_231 a b c : max3n a b c = max3n b c a.
(*D*) Proof. by rewrite max3n_213 max3n_132. Qed.

(** ***
    We define functions that test if 3 natural numbers are
    in increasing (or decreasing) order 
*)

Definition order3n (T : Type) (r : rel T) x y z := (r x y) && (r y z).
Definition incr3n := order3n nat (fun x y => x <= y).
Definition decr3n := order3n nat (fun x y => y <= x).

(** *** Exercise 15
*)
Lemma incr3n_decr a b c : incr3n a b c = decr3n c b a.
(*D*) Proof. by rewrite /incr3n /order3n andbC. Qed.

(** *** Exercise 16
*)

Lemma incr3_3n a : incr3n a a a.
(*D*) by rewrite /incr3n /order3n leqnn. Qed.

(** *** Exercise 17
*)

Lemma decr3_3n a : decr3n a a a.
(*D*) by rewrite -incr3n_decr incr3_3n. Qed.

(** *** Exercise 18
*)

Lemma incr3n_leq12 a b c : incr3n a b c -> a <= b.
(*D*) by rewrite /incr3n /order3n; case: (_ <= _). Qed.

(** *** Exercise 19
*)
Lemma incr3n_leq23 a b c : incr3n a b c -> b <= c.
(*D*) by rewrite /incr3n /order3n; case: (_ <= _). Qed.

(** *** Exercise 20
*)
Lemma incr3n_eq a b c : incr3n a b a = (a == b).
(*D*) by rewrite /incr3n /order3n eqn_leq. Qed.
 
