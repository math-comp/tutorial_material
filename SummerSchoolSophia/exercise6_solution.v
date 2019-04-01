From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:

Prove that the equation #$$ 8y = 6x + 1 $$# has no solution.

- Hint 1: take the modulo 2 of the equation.
- Hint 2: [Search _ modn addn] and [Search _ modn muln]
#<br/><div># *)
Lemma ex1 x y : 8 * y != 6 * x + 1.
Proof.
(*D*)apply/negP => /eqP /(congr1 (modn^~ 2)).
(*D*)by rewrite -modnMml mul0n -modnDml -modnMml.
(*A*)Qed.

(** #</div>#
*** Exercise 2:

The ultimate Goal of this exercise is to find the solutions of the equation
#$$ 2^n = a^2 + b^2,$$# where n is fixed and a and b unkwown.

We hence study the following predicate:
#<div># *)
Definition sol n a b := [&& a > 0, b > 0 & 2 ^ n == a ^ 2 + b ^ 2].
(** #</div>#
- First prove that there are no solutions when n is 0.

  - Hint: do enough cases on a and b.
#<div># *)
Lemma sol0 a b : ~~ sol 0 a b.
(*A*)Proof. by move: a b => [|[|[|a]]] [|[|[|b]]]. Qed.
(** #</div>#
- Now prove the only solution when n is 1.

  - Hint: do enough cases on a and b.
#<div># *)
Lemma sol1 a b : sol 1 a b = (a == 1) && (b == 1).
(*A*)Proof. by move: a b => [|[|[|a]]] [|[|[|b]]]. Qed.
(** #</div>#
- Now prove a little lemma that will guarantee that a and b are even.

  - Hint 1: first prove [(x * 2 + y) ^ 2 = y ^ 2 %[mod 4]].
  - Hint 2: [About divn_eq] and [Search _ modn odd]
#<div># *)
Lemma mod4Dsqr_even a b : (a ^ 2 + b ^ 2) %% 4 = 0 -> (~~ odd a) && (~~ odd b).
Proof.
(*D*)have sqr_x2Dy_mod4 x y : (x * 2 + y) ^ 2 = y ^ 2 %[mod 4].
(*D*)  rewrite sqrnD addnAC mulnAC [2 * _]mulnC -mulnA -[2 * 2]/4.
(*D*)  by rewrite expnMn -[2 ^ 2]/4 -mulnDl -modnDml modnMl.
(*D*)rewrite {1}(divn_eq a 2) {1}(divn_eq b 2) -modnDm.
(*D*)by rewrite !sqr_x2Dy_mod4 modnDm !modn2; do 2!case: odd.
(*A*)Qed.
(** #</div>#
- Deduce that if n is greater than 2 and a and b are solutions, then they are even.
#<div># *)
Lemma sol_are_even n a b : n > 1 -> sol n a b -> (~~ odd a) && (~~ odd b).
Proof.
(*D*)case: n => [|[|n]]// _; rewrite /sol => /and3P[_ _ /eqP eq_a2Db].
(*D*)by rewrite mod4Dsqr_even// -eq_a2Db !expnS mulnA modnMr.
(*A*)Qed.
(** #</div>#
- Prove that the solutions for n are the halves of the solutions for n + 2.

  - Hint: [Search _ odd double] and [Search _ "eq" "mul"].

#<div># *)
Lemma solSS n a b : sol n.+2 a b -> sol n a./2 b./2.
Proof.
(*D*)move=> soln2ab; have [//|a_even b_even] := andP (sol_are_even _ soln2ab).
(*D*)rewrite /sol -[a]odd_double_half -[b]odd_double_half in soln2ab.
(*D*)rewrite (negPf a_even) (negPf b_even) ?add0n ?double_gt0 in soln2ab.
(*D*)rewrite /sol; move: soln2ab => /and3P[-> -> /=].
(*D*)by rewrite -(addn2 n) expnD -!muln2 !expnMn -mulnDl eqn_mul2r.
(*A*)Qed.
(** #</div>#
- Prove there are no solutions for n even

  - Hint: Use [sol0] and [solSS].
#<div># *)
Lemma sol_even a b n : ~~ sol (2 * n) a b.
Proof.
(*D*)elim: n => [|n IHn] in a b *; first exact: sol0.
(*D*)by apply/negP; rewrite mulnS => /solSS; apply/negP.
(*A*)Qed.
(** #</div>#
- Certify the only solution when n is odd.

  - Hint 1: Use [sol1], [solSS] and [sol_are_even].
  - Hint 2: Really sketch it on paper first!
#<div># *)
Lemma sol_odd a b n : sol (2 * n + 1) a b = (a == 2 ^ n) && (b == 2 ^ n).
Proof.
(*D*)apply/idP/idP=> [|/andP[/eqP-> /eqP->]]; last first.
(*D*)  by rewrite /sol !expn_gt0/= expnD muln2 addnn -expnM mulnC.
(*D*)elim: n => [|n IHn] in a b *; first by rewrite sol1.
(*D*)rewrite mulnS !add2n !addSn => solab.
(*D*)have [//|/negPf aNodd /negPf bNodd] := andP (sol_are_even _ solab).
(*D*)rewrite /sol -[a]odd_double_half -[b]odd_double_half aNodd bNodd.
(*D*)by rewrite -!muln2 !expnSr !eqn_mul2r IHn// solSS.
(*A*)Qed.
(** #</div>#
*** Exercise 3:
Certify the solutions of this problem.

- Hint: Do not hesitate to take advantage of Coq's capabilities
  for brute force case analysis
#<div># *)
Lemma ex3 n : (n + 4 %| 3 * n + 32) = (n \in [:: 0; 1; 6; 16]).
Proof.
(*D*)apply/idP/idP => [Hn|]; rewrite !inE; last first.
(*D*)  by move=> /or4P[] /eqP->.
(*D*)have : n + 4 %| 3 * n + 32 - 3 * (n + 4) by rewrite dvdn_sub// dvdn_mull.
(*D*)by rewrite mulnDr subnDl /= {Hn}; move: n; do 21?[case=>//].
(*A*)Qed.
(** #</div>#
*** Exercise 4:

Certify the result of the euclidean division of
#$$a b^n - 1\quad\textrm{  by  }\quad b ^ {n+1}$$#

#<div># *)
Lemma ex4 a b n : a > 0 -> b > 0 -> n > 0 ->
   edivn (a * b ^ n - 1) (b ^ n.+1) =
   ((a - 1) %/ b, ((a - 1) %% b) * b ^ n + b ^ n - 1).
Proof.
(*D*)move=> a_gt0 b_gt0 n_gt0; rewrite /divn modn_def.
(*D*)have [q r aB1_eq r_lt] /= := edivnP (a - 1).
(*D*)rewrite b_gt0 /= in r_lt.
(*D*)have /(congr1 (muln^~ (b ^ n))) := aB1_eq.
(*D*)rewrite mulnBl mulnDl mul1n.
(*D*)move=> /(congr1 (addn^~ (b ^ n - 1))).
(*D*)rewrite addnBA ?expn_gt0 ?b_gt0// subnK; last first.
(*D*)  by rewrite -[X in X <= _]mul1n leq_mul2r a_gt0 orbT.
(*D*)rewrite -mulnA -expnS -addnA => ->.
(*D*)rewrite edivn_eq addnBA ?expn_gt0 ?b_gt0//.
(*D*)rewrite subnS subn0 prednK ?addn_gt0 ?expn_gt0 ?b_gt0 ?orbT//.
(*D*)rewrite -[X in _ + X]mul1n -mulnDl addn1 expnS.
(*D*)by rewrite leq_mul2r r_lt orbT.
(*A*)Qed.
(** #</div>#
*** Exercise 5:

Prove that the natural number interval #$$[n!+2\ ,\ n!+n]$$#
contains no prime number.

- Hint: Use [Search _ prime dvdn], [Search _ factorial], ...

#<div># *)
Lemma ex5 n m : n`! + 2 <= m <= n`! + n -> ~~ prime m.
Proof.
(*D*)move=> m_in; move: (m_in); rewrite -[m](@subnKC n`!); last first.
(*D*)  by rewrite (@leq_trans (n`! + 2)) ?leq_addr//; by case/andP: m_in.
(*D*)set k := (_ - _); rewrite !leq_add2l => /andP[k_gt1 k_le_n].
(*D*)apply/primePn; right; exists k.
(*D*)  by rewrite k_gt1/= -subn_gt0 addnK fact_gt0.
(*D*)by rewrite dvdn_add// dvdn_fact// k_le_n (leq_trans _ k_gt1).
(*A*)Qed.
(** #</div># *)