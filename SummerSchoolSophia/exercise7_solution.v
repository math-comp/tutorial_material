From mathcomp Require Import all_ssreflect.


(** *** Exercise 1 :
    - Prove this statement by induction  using big_nat_recr and big_geq
    - alternatively by using big_morph
*)

Lemma sum_mull f (k n : nat) :
  k * (\sum_(0 <= i < n) f i) = \sum_(0 <= i < n) (k * f i).
Proof.
(*D*)(* elim: n => [|n IH]; first by rewrite !big_geq. *)
(*D*)(* by rewrite !big_nat_recr //= mulnDr IH. *)
(*D*)by apply: (big_morph (fun n => k * n)) => // x y; rewrite mulnDr.
Qed.

(** *** Exercise 2 :
    - Prove this statement by using big_morph
*)

Lemma sum_mulr f (k n : nat) :
  (\sum_(0 <= i < n) f i) * k = \sum_(0 <= i < n) (f i * k).
Proof.
(*D*)(* elim: n => [|n IH]; first by rewrite !big_geq. *)
(*D*)(* by rewrite !big_nat_recr //= mulnDl IH. *)
(*D*)by apply: (big_morph (fun n => n * k)) => // x y; rewrite mulnDl.
Qed.


(** *** Exercise 3 :
    - Prove this statement by induction.
    - Relevant lemmas are
        - doubleS odd_double addn0 addnn mulnn
        - big_mkcond big_nat_recr big_geq
*)

Lemma sum_odd n : \sum_(0 <= i < n.*2 | odd i) i = n ^ 2.
Proof.
(*D*)elim: n => [|n IHn]; first by rewrite big_geq.
(*D*)rewrite doubleS big_mkcond 2?big_nat_recr // -big_mkcond /=.
(*D*)rewrite {}IHn odd_double /= addn0 -addnn -!mulnn.
(*D*)by rewrite mulSn mulnC mulSn addnA addSn addnC.
Qed.


(** *** Exercise 4 :
    - Prove this statement by induction.
    - Relevant lemmas are
        - doubleD muln2 addn2 big_nat_recr big_geq
*)

Lemma sum_gauss n : (\sum_(0 <= i < n) i).*2 = n * n.-1.
Proof.
(*D*)elim: n => [|n IH]; first by rewrite big_geq.
(*D*)rewrite big_nat_recr //= doubleD {}IH.
(*D*)case: n => [|n /=]; first by rewrite muln0.
(*D*)by rewrite -muln2 -mulnDr addn2 mulnC.
Qed.


(**
   In what follows we are going to mimic the proof of Gauss :

<<
       1 +     2 + .....        +  n.-2     + n.-1
 +  n.-1 +  n.-2 +              +     2     +    1

   = n.-1 * n
>>

**)


(** *** Exercise 5 :
    - Prove this statement without induction.
    - Relevant lemma is big_nat_rev
*)

Lemma sum_gauss_rev n : \sum_(0 <= i < n) (n.-1 - i)  = \sum_(0 <= i < n) i.
Proof.
(*D*)rewrite [RHS]big_nat_rev /=.
(*D*)by case: n => //.
Qed.

(** *** Exercise 6 :
    - Prove this statement without induction.
    - Relevant lemma is addnn
*)
Lemma sum_gauss_double n : (\sum_(0 <= i < n) i).*2  =
       \sum_(0 <= i < n) i + \sum_(0 <= i < n) (n.-1 - i).
Proof.
(*D*)by rewrite sum_gauss_rev addnn.
Qed.


(** *** Exercise 7 :
    - Prove this statement without induction.
    - Relevant lemma are big_split and eq_big_nat
*)

Lemma sum_gaussD n :
  \sum_(0 <= i < n) i + \sum_(0 <= i < n) (n.-1 - i) =
           \sum_(0 <= i < n) n.-1.
Proof.
(*D*)rewrite -big_split /=.
(*D*)apply: eq_big_nat => i Hi.
(*D*)rewrite addnC subnK //.
(*D*)by case: n Hi.
Qed.


(** *** Exercise 8 :
    - Prove this statement without induction.
    - Relevant lemma are sum_nat_const_nat
*)

Lemma sum_gauss_const n k : \sum_(0 <= i < n) k = n * k.
Proof.
(*D*)by rewrite sum_nat_const_nat subn0.
Qed.


(** *** Exercise 9 :
    - Prove this statement using exercises 5-8
*)
Lemma sum_gauss_alt1 n : (\sum_(0 <= i < n) i).*2 = n * n.-1.
Proof.
(*D*)by rewrite sum_gauss_double sum_gaussD sum_gauss_const.
Qed.


(** *** Exercise 10 :
    - Prove this statement directly without using the lemmas
    - defined in exercises 5-9
*)

Lemma sum_gauss_alt2 n : (\sum_(0 <= i < n) i).*2 = n * n.-1.
Proof.
(*D*)rewrite -addnn [X in X + _ = _]big_nat_rev -big_split /=.
(*D*)rewrite -[X in _ = X * _]subn0 -sum_nat_const_nat.
(*D*)apply: eq_big_nat => i.
(*D*)by case: n => // n /andP[iP iLn]; rewrite [_ + _]subnK.
Qed.


(** ***  Now we try to prove the sum of squares.

**)

(** ***  We first define the property for a function to be increasing
**)


Definition fincr f := forall n, f n <= f n.+1.

(** *** Exercise 11 :
    - Prove this statement by induction
*)

Lemma fincrD f m n : fincr f -> f m <= f (n + m).
Proof.
(*D*)move=> Hf; elim: n => // n H; exact: leq_trans H (Hf _).
Qed.


(** *** Exercise 12 :
    - Prove this statement using exercise 11
    - Hint : subnK
*)

Lemma fincr_leq f m n : fincr f -> m <= n -> f m <= f n.
Proof.
(*D*)by move=> Hf Hn; rewrite -(subnK Hn) fincrD.
Qed.


(** *** Exercise 13 :
        - Proof by induction
        - Hints : addnCA subnK fincr_leq big_geq
*)

Lemma sum_consecutive n f :
  fincr f -> f n = \sum_(0 <= i < n) (f i.+1 - f i) + f 0.
Proof.
(*D*)move=> Hf.
(*D*)elim: n => [|n IH]; first by  rewrite big_geq.
(*D*)by rewrite big_nat_recr //= addnAC -IH addnC subnK.
Qed.


(** *** Exercise 14 :
        - Proof using the previous lemma
        - Hints : leq_exp2r
*)
Lemma sum_consecutive_cube n :
  n^3 = \sum_(0 <= i < n) (i.+1 ^ 3 - i ^ 3).
Proof.
(*D*)rewrite (sum_consecutive _ (fun i => i ^ 3)) ?addn0 //.
(*D*)by move=> m; rewrite leq_exp2r.
Qed.


(** *** We give the proof of a technical result
*)

Ltac sring :=
  rewrite !(expn1, expnS, =^~mul2n, mulSn, mulnS, addnS, addSn,
          mulnDr, mulnDl, add0n, addn0, muln0, addnA, mulnA);
  do ! congr (S _);
  do ! ((congr (_ + _); [idtac]) ||  (rewrite [in LHS]addnC ?[in LHS]addnA //)).

Lemma succ_cube n : n.+1 ^ 3 = n ^ 3  + (3 * n ^ 2 + 3 * n + 1).
Proof. sring. Qed.

(** *** Exercise 15 :
        - Hints : big_split sum_mull sum_gauss sum_gauss_const
*)
Lemma sum_sum3 n :
  \sum_(0 <= i < n) (6 * i ^ 2 + 6 * i + 2) =
   6 * (\sum_(0 <= i < n)  i ^ 2) + 3 * n * n.-1 + n.*2.
Proof.
(*D*)rewrite big_split big_split /=.
(*D*)rewrite -!sum_mull sum_gauss_const.
(*D*)by rewrite -mulnA -sum_gauss // -mul2n mulnA muln2.
Qed.


(** *** Exercise 16 :
        - Hints : big_split sum_mull sum_gauss sum_gauss_const
*)
Lemma sum_sum4 n :
 (n ^ 3).*2 = 6 * (\sum_(0 <= i < n)  i ^ 2) + 3 * n * n.-1 + n.*2.
Proof.
(*D*)rewrite sum_consecutive_cube -sum_sum3 -mul2n sum_mull.
(*D*)apply: eq_big_nat => i Hi.
(*D*)by rewrite succ_cube addKn 2!mulnDr !mulnA.
Qed.

(** *** Another technical lemma
*)

Lemma sum_tech n : (n ^ 3).*2 = n * n.-1 * n.-1.*2.+1 + 3 * n * n.-1 + n.*2.
Proof. by case: n => //= n1; sring. Qed.


(** *** Exercise 17 :
      - Hint : addIn sum_sum4 sum_tech.
*)
Lemma sum_square n : 6 * (\sum_(0 <= i < n)  i ^ 2) =  n * n.-1 * n.-1.*2.+1.
Proof.
(*D*)apply: (@addIn (3 * n * n.-1 + n.*2)).
(*D*)by rewrite addnA -sum_sum4 sum_tech !addnA.
Qed.

(** *** Exercise 18 :
     - Prove the theorem directly using only sum_gauss and the tactic sring.
*)
Lemma sum_square_alt n : 6 * (\sum_(0 <= i < n)  i ^ 2) =  n * n.-1 * n.-1.*2.+1.
Proof.
(*D*)apply: (@addIn (3 * n * n.-1 + n.*2)).
(*D*)rewrite addnA -[6]/(2 * 3) -!mulnA mul2n (big_morph _ (mulnDr _) (muln0 _)).
(*D*)rewrite -{1}sum_gauss -doubleMr (big_morph _ (mulnDr _) (muln0 _)).
(*D*)rewrite -{3}[n]muln1 -{3}[n]subn0 -sum_nat_const_nat.
(*D*)rewrite -!doubleD -!big_split /=.
(*D*)rewrite (eq_big_nat _ _ (_ : forall i, _ -> _ = i.+1 ^ 3 - i ^3)) => [|i H]; last first.
(*D*)  rewrite -[LHS](addKn (i ^ 3)); congr (_ - _).
(*D*)  by sring.
(*D*)apply: etrans (_ : (n^3).*2 = _).
(*D*)  congr (_.*2).
(*D*)  elim: n => [|n IH]; first by rewrite big_geq.
(*D*)  by rewrite big_nat_recr //= IH addnC subnK // leq_exp2r.
(*D*)by case: n => //= n1; sring.
Qed.
