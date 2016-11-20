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
Proof.
  intros A PACK2.
  pack2_cases (destruct PACK2) Case.

  (* notice that Case := "Pack1" is already in the hypothesis. If you
     are lazy, are using emacs and have added the insert_case.el in
     your .emacs, just press C-c C-a C-q or C-c C-a C-z to copy it
     directly *)
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
  (* don't miss the ' at the end of induction' *)
  induction' n; simpl.

  (* Notice this is already in the goal *)
  Case "O".
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

(* it also works with destruct' and case' *)
Goal forall n, n = 0 \/ n <> 0.
Proof.
  destruct' n as [|n'].
  Case "O".
    left; reflexivity.
  Case "S n'".
    right. intro H. inversion H.
Qed.

Require Import List.
Goal forall l: list nat, l = nil \/ l = hd 0 l :: tl l.
Proof.
  case' l as [|n l'] _eqn.
  Case "@nil".
    left. reflexivity.
  Case "cons n l'".
    right. simpl. reflexivity.
Qed.

(* the library only defines induction', destruct' and case', because
   those are the only one I use. But you can of course do the
   same. The only tactic related to inductive that I do not know how
   to deal with is the inversion tactic since it does not produce the
   same number of goal. There is in fact a inversion' tactics, but it
   fails every time some subgoals are automatically eliminated *)


(* the primed tactics don't always use the name of the
   constructor. There are two special cases for or (\/) and sumbool
   ({}+{}) where the content of the hypothesis is put in the tag *)

Lemma nat_eq_dec : forall (n m: nat), {n = m} + {n <> m}.
Proof.
  decide equality.
Qed.

Notation "x == y" := (nat_eq_dec x y) (at level 70, no associativity).

Tactic Notation "dest" constr(a) "==" constr(b) :=
  (* the tactic cannot just return the string, it has to be stored in
     some hypothesis *)
  destruct' (a == b).

Tactic Notation "dest" "==" :=
  match goal with
    | H : context[?a == ?b] |- _ =>
      dest a == b
    | |- context[?a == ?b] =>
      dest a == b
  end.

Goal forall foo,
  (if foo == 42 then
     False
   else
     False
  ) -> False.
Proof.
  intro. dest ==.
  (* note that the notation for 42 is used *)
  Case "foo = 42".
    auto.
  Case "foo <> 42".
    auto.
Qed.

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


(* it also works with bindings and when lemma needs to be reducesed *)
Definition true_imp_true:= forall (TRUE_in:True), True.
Lemma useless: forall (n:nat) (EQ:n = n) (TRUE_out:True), true_imp_true.
Proof. red. auto. Qed.

(* Other example *)
Axiom classicT : forall P:Prop, {P} + {~P}.

Notation "'_If' X 'then' Y 'else' Z" := (if classicT X then Y else Z) (at level 100).


Ltac case_if :=
  match goal with
    | |- _If ?P then _ else _ =>
      destruct' (classicT P)
  end.


Goal forall a: nat, _If a = 0 then 0 = a else 0 <> a.
Proof.
  intro.
  case_if.
  Case "a = 0".
    auto.
  Case "a <> 0".
    auto.
Qed.

(* another tactic defined in the ml library is the "string of foo in
   H" tactic. It builds a coq string from any term, and put it in
   H. The wraper string_of is easier to use, even if it is written in
   CPS style *)

Ltac Case_Goal :=
  match goal with
    | |- ?G =>
      string_of G (fun strG =>
        fst_Case_tac strG)
  end.

Goal (True /\ 1 = 1).
Proof.
  split; Case_Goal.
  Case "True".
    constructor.
  Case "1 = 1".
    reflexivity.
Qed.



(* one might have noticed that notations were used with the string_of
   tactic, but not with the induction' tactic.*)

(* to make the 'ed tactics use notation (this works only for
   constructors without arguments for now), use *)
Set Notations With Case.
Goal forall n:nat, n >= 0.
Proof.
  induction' n as [|n'].
  Case "0". (* notice the 0 *)
    auto.
  Case "S n'".
    auto.
Qed.


(* to get a string without notations, use string_of_without *)

Ltac Case_Goal' :=
  match goal with
    | |- ?G =>
      string_of_without G (fun strG =>
        fst_Case_tac strG)
  end.

Goal (1 <= 2 /\ 1 <> 2).
Proof.
  split; Case_Goal'.
  Case "le (S O) (S (S O))".
    constructor. constructor.
  Case "not (eq (S O) (S (S O)))".
    congruence.
Qed.
