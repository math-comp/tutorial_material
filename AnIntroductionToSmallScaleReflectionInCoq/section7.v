(******************************************************************************)
(* Solutions of exercises : Appendix                                          *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype tuple finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(* Exercise 7.0.3                                                             *)
(******************************************************************************)

Search _ "_ * _".
Print muln.
Print muln_rec.

Search _ "_ ==> _".
Print implb.
Search (_ ==> true).

Search _ (_ && _ = _ && _).

(******************************************************************************)
(* Exercise 7.0.4                                                             *)
(******************************************************************************)


(* According to the name of the operator and to the table of suffixes *)
(*it should be mulnC *)
Search (_ * _ = _ * _).
(* The above command does not work since commutativity for muln is *)
(*stated using the predicate on binary operations *)
Search _ commutative muln.

Check orbCA.
Print left_commutative.
