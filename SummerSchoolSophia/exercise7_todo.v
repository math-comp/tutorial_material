From mathcomp Require Import all_ssreflect.


(** *** Exercise 1 :
    - Prove this statement by induction or
    - alternatively by using big_morph
*)

Lemma sum_mull f (k n : nat) : 
  k * (\sum_(0 <= i < n) f i) = \sum_(0 <= i < n) (k * f i).
Proof.
Qed.

(** *** Exercise 2 :
    - Prove this statement by using big_morph
*)

Lemma sum_mulr f (k n : nat) : 
  (\sum_(0 <= i < n) f i) * k = \sum_(0 <= i < n) (f i * k).
Proof.
Qed.


(** *** Exercise 3 :
    - Prove this statement by induction.
    - Relevant lemmas are
        - doubleS odd_double addn0 addnn mulnn
        - big_mkcond big_nat_recr big_geq
*)

Lemma sum_odd n : \sum_(0 <= i < n.*2 | odd i) i = n ^ 2.
Proof.
Qed.


(** *** Exercise 4 :
    - Prove this statement by induction.
    - Relevant lemmas are
        - doubleD muln2 addn2 big_nat_recr big_geq
*)

Lemma sum_gauss n : (\sum_(0 <= i < n) i).*2 = n * n.-1.
Proof.
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
Qed.

(** *** Exercise 6 :
    - Prove this statement without induction.
    - Relevant lemma is addnn
*)
Lemma sum_gauss_double n : (\sum_(0 <= i < n) i).*2  = 
       \sum_(0 <= i < n) i + \sum_(0 <= i < n) (n.-1 - i).
Proof.
Qed.


(** *** Exercise 7 :
    - Prove this statement without induction.
    - Relevant lemma are big_split and eq_big_nat
*)

Lemma sum_gaussD n :       
  \sum_(0 <= i < n) i + \sum_(0 <= i < n) (n.-1 - i) =
           \sum_(0 <= i < n) n.-1.
Proof.
Qed.


(** *** Exercise 8 :
    - Prove this statement without induction.
    - Relevant lemma are sum_nat_const_nat
*)

Lemma sum_gauss_const n k : \sum_(0 <= i < n) k = n * k.
Proof.
Qed.


(** *** Exercise 9 :
    - Prove this statement using exercises 5-8
*)
Lemma sum_gauss_alt1 n : (\sum_(0 <= i < n) i).*2 = n * n.-1.
Proof.
Qed.


(** *** Exercise 10 :
    - Prove this statement directly without using the lemmas
    - defined in exercises 5-9
*)

Lemma sum_gauss_alt2 n : (\sum_(0 <= i < n) i).*2 = n * n.-1.
Proof.
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
Qed.


(** *** Exercise 12 :
    - Prove this statement using exercise 9
    - Hint : subnK
*)

Lemma fincr_leq f m n : fincr f -> m <= n -> f m <= f n.
Proof. 
Qed.


(** *** Exercise 13 :
        - Proof by induction
        - Hints : addnCA subnK fincr_leq big_geq
*)

Lemma sum_consecutive n f :  
  fincr f -> f n = \sum_(0 <= i < n) (f i.+1 - f i) + f 0.
Proof.
Qed.


(** *** Exercise 14 :
        - Proof using the previous lemma
        - Hints : leq_exp2r
*)
Lemma sum_consecutive_cube n :  
  n^3 = \sum_(0 <= i < n) (i.+1 ^ 3 - i ^ 3).
Proof.
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
        - Hints : big_split sum_mll sum_gauss sum_gauss_const
*)
Lemma sum_sum3 n : 
  \sum_(0 <= i < n) (6 * i ^ 2 + 6 * i + 2) =
   6 * (\sum_(0 <= i < n)  i ^ 2) + 3 * n * n.-1 + n.*2.
Proof.
Qed.


(** *** Exercise 16 :
        - Hints : big_split sum_mll sum_gauss sum_gauss_const
*)
Lemma sum_sum4 n : 
 (n ^ 3).*2 = 6 * (\sum_(0 <= i < n)  i ^ 2) + 3 * n * n.-1 + n.*2.
Proof.
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
Qed.

(** *** Exercise 18 :
     - Prove the theorem directly using only sum_gauss and the tactic sring.
*)
Lemma sum_square_alt n : 6 * (\sum_(0 <= i < n)  i ^ 2) =  n * n.-1 * n.-1.*2.+1.
Proof.
Qed.
