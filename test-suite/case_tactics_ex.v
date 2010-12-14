(*******************************************************************)
(* Copyright 2010 Alexandre Pilkiewicz                             *)
(*     <alexandre.pilkiewicz@polytechnique.org >                   *)
(* This program is free software. It comes without any warranty,   *)
(* to the extent permitted by applicable law. You can redistribute *)
(* it and/or modify it under the terms of the WTFPL, Version 2, as *)
(* published by Sam Hocevar. See http://sam.zoy.org/wtfpl/COPYING  *)
(* for more details.                                               *)
(*******************************************************************)


(* this small example suppose that you have included insert-cases.el
   in your .emacs. If you have not, you can of course run the file,
   but reproducing it might be a bit painful ! *)

Add Rec LoadPath "../theories" as Case_Tactics.
Add ML Path "../src".
Require Import Case_Tactics.

(* the (S* )Case tactics, by Aaron Bohannon
   http://www.cis.upenn.edu/~bcpierce/sf/Basics.html#lab27
 *)

(* The Case tactic allows you to add "comments" in your code, telling
   which subcase you are dealing with*)

Goal (True -> 1 = 1 -> False) -> False.
Proof.
  intro H.
  apply H.
  Case "True".
  (* Notice that the hypothesis have been modified *)
  constructor.
  Case "1 = 1".
  reflexivity.
Qed.



(* But it is more powerful than simple comments. If you try to enter a
   new case before finishing the current one, it fails. So imagine
   that the goal changes slightly *)

Inductive pack := Pack: True -> pack.

Goal (pack -> 1 = 1 -> False) -> False.
Proof.
  intro H.
  apply H.
  Case "True".
  constructor.
  (* The subgoal has not been eliminated. Try to un-comment the next line *)
  (*Case "1 = 1".*) 
  (* It fails with "Tactic failure: because we are working on a
     different case."*)
  constructor.

  Case "1 = 1".
  reflexivity.
Qed.

(* This helps a lot with maintainability: you know precisely which
   sub-goal fails *)



(* Inductive types *)

(* when working with inductive types, it is recommended to write a
tactic that automatically apply the proper (S* )Case tactic to each
subgoal when performing a destruction or induction 

http://www.cis.upenn.edu/~bcpierce/sf/Rel.html#lab260
*)

Inductive pack2 (A:Prop) : Prop :=
|Pack1: (A /\ True)-> pack2 A
|Pack2: A -> pack2 A.

Tactic Notation "pack2_cases" tactic(first) tactic(c) :=
  first;
  [ c "Pack1" | c "Pack2"].

Goal forall A, pack2 A -> A.
intros A PACK2.
pack2_cases (destruct PACK2) Case.

(* notice that Case := "Pack1" is already in the hypothesis. If you
   are lazy, just press C-c C-a C-q or C-c C-a C-z to copy it directly
   *)
Case "Pack1".
destruct H. assumption.
Case "Pack2".
assumption.
Qed.


(* But this can quickly become tedious, especially if you are working
   with big inductive (like this one
   http://compcert.inria.fr/doc/html/Op.html#operation )

   Here comes the goal of this contribution: automatically build such tactic.
   *)

Goal forall n, n = n + 0.
Proof.
  intros n.
  (* don't miss the ' at the end of induction' *)
  induction' n; simpl.

  (* Notice this is already in the goal *)
  Case "0".
  reflexivity.

  (* and this too *)
  Case "S".
  f_equal. assumption.
Qed.

(*when you use an intro pattern, it is used to build nicer names for subgoals *)
Goal forall A B (f: A -> B) l, length l = length (List.map f l).
Proof.
  intros A B f l.
  induction' l as [| a l'].

  Case "@nil".
  reflexivity.

  Case "cons a l'".
  simpl. f_equal. assumption.
Qed.

(* the library only defines induction' and destruct', because I
   usually don't use case or elim. But you can of course do the
   same. The only tactic related to inductive that I do not know how
   to deal with is the inversion tactic since it does not produce the
   same number of goal *)



(* another tactic defined in the ml library is the "string of foo in
   H" tactic. It builds a coq string from any term, and put it in
   H. Lets see how this can be useful *)

Lemma nat_eq_dec : forall (n m: nat), {n = m} + {n <> m}.
Proof.
  decide equality.
Qed.

Notation "x == y" := (nat_eq_dec x y) (at level 70, no associativity).


Tactic Notation "dest" constr(a) "==" constr(b) :=
  (* the tactic cannot just return the string, it has to be stored in
     some hypothesis *)
  let A := fresh in
  let B := fresh in
  string of a in A; string of b in B;
  let strA := eval cbv in A in
  let strB := eval cbv in B in
  clear A; clear B;
  destruct (a == b); [ fst_Case_tac (strA ^^ " = " ^^ strB)
                     | fst_Case_tac (strA ^^ " <> " ^^ strB)].

Tactic Notation "dest" "==" :=
  match goal with
    | H : context[?a == ?b] |- _ =>
      dest a == b
    | |- context[?a == ?b] =>
      dest a == b
  end.

Goal forall foo bar baz, 
  (if foo == bar then 
    if bar == baz then
      False
    else
      (foo <> baz -> False)
   else
     if bar == baz then
      (foo <> baz -> False)
    else
      False
  ) -> False.
Proof.
  intros foo bar baz H. repeat (dest ==); try assumption.

  (* here the C-c C-a C-q command can be pretty handy *)
  Case "foo = bar"; SCase "bar <> baz".
  apply H. subst. assumption.

  Case "foo <> bar"; SCase "bar = baz".
  apply H. subst. assumption.
Qed.


(* let's show how the apply' (and eapply') work *)

Lemma refl: forall (n m: nat) (EQ: n = m), m = n.
Proof. auto. Qed.

Lemma trans : forall (n m:nat) 
  (nEQm: n = m) (p:nat), m = p-> n = p.
Proof. congruence. Qed.


Lemma refl_trans: forall (n m p: nat), n = m -> m = p -> p = n.
Proof.
  intros n m p EQnm EQmp.
  (* we first apply refl *)
  apply' refl.
  (* Case := "EQ" has been automatically inserted (ok, not super
     useful here since we have only one subgoal. But it's an exemple
     file *)
  Case "EQ".
  eapply' trans.
  SCase "nEQm".
  eassumption.
  (* Note here that this hypothesis was not named. An arbitrary name
     has been chosen. It can be replaced by the NSCase tactic *)
  NSCase "mEQp".
  assumption.
Qed.