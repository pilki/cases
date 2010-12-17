(*******************************************************************)
(* Copyright 2010 Alexandre Pilkiewicz                             *)
(*     <alexandre.pilkiewicz@polytechnique.org >                   *)
(* This program is free software. It comes without any warranty,   *)
(* to the extent permitted by applicable law. You can redistribute *)
(* it and/or modify it under the terms of the WTFPL, Version 2, as *)
(* published by Sam Hocevar. See http://sam.zoy.org/wtfpl/COPYING  *)
(* for more details.                                               *)
(*******************************************************************)

Declare ML Module "case_tactics_plugin".

(* (S* )Case tactics by Aaron Bohannon *)
Require String. Open Scope string_scope.

Notation "s1 ^^ s2" := (String.append s1 s2) (right associativity, at level 60).

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); simpl in x; move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Ltac Case name := Case_aux Case name.
Ltac SCase name := Case_aux SCase name.
Ltac SSCase name := Case_aux SSCase name.
Ltac SSSCase name := Case_aux SSSCase name.
Ltac SSSSCase name := Case_aux SSSSCase name.
Ltac SSSSSCase name := Case_aux SSSSSCase name.
Ltac SSSSSSCase name := Case_aux SSSSSSCase name.
Ltac SSSSSSSCase name := Case_aux SSSSSSSCase name.

(* The R(S* )Case tactics rename the case. Usefull for the apply'
   tactic *)

Tactic Notation "RCase_aux" ident(x) constr(old) constr(new) :=
  first [
   assert_eq x old; clear x; set (x := new); simpl in x;  move_to_top x
  | fail 1 "because we are working on a different case" ].

Ltac RCase old new := RCase_aux Case old new.
Ltac RSCase old new := RCase_aux SCase old new.
Ltac RSSCase old new := RCase_aux SSCase old new.
Ltac RSSSCase old new := RCase_aux SSSCase old new.
Ltac RSSSSCase old new := RCase_aux SSSSCase old new.
Ltac RSSSSSCase old new := RCase_aux SSSSSCase old new.
Ltac RSSSSSSCase old new := RCase_aux SSSSSSCase old new.
Ltac RSSSSSSSCase old new := RCase_aux SSSSSSSCase old new.

(* N(S* )Case are instanciation of RS*Case on "NONAMEGOAL", the name
   produce by apply' when no name is available *)
Ltac NCase := RCase "NONAMEGOAL".
Ltac NSCase := RSCase "NONAMEGOAL".
Ltac NSSCase := RSSCase "NONAMEGOAL".
Ltac NSSSCase := RSSSCase "NONAMEGOAL".
Ltac NSSSSCase := RSSSSCase "NONAMEGOAL".
Ltac NSSSSSCase := RSSSSSCase "NONAMEGOAL".
Ltac NSSSSSSCase := RSSSSSSCase "NONAMEGOAL".
Ltac NSSSSSSSCase := RSSSSSSSCase "NONAMEGOAL".



(* tacic to get the first available (S* )Case tactic *)
Tactic Notation "exists_hyp" hyp(H) :=
  idtac.

Tactic Notation "fst_Case_aux" ident(x) tactic(t) constr(s):=
  first [exists_hyp x; fail 1 | t s].

Ltac fst_Case_tac s :=
  first
    [ fst_Case_aux Case (Case) s
    | fst_Case_aux SCase (SCase) s
    | fst_Case_aux SSCase(SSCase) s
    | fst_Case_aux SSSCase (SSSCase) s
    | fst_Case_aux SSSSCase (SSSSCase) s
    | fst_Case_aux SSSSSCase (SSSSSCase) s
    | fst_Case_aux SSSSSSCase (SSSSSSCase) s
    | fst_Case_aux SSSSSSSCase (SSSSSSSCase) s].

Register First Case fst_Case_tac.


(* [cases ty tac c] runs the tactic tac and produces the cases of
   inductive ty with tactic c. If ty is not an inductive but has an
   inductive type, its type is used *)
Ltac ind_type ty :=
    match type of ty with
      | Prop => ty
      | Type => ty
      | Set => ty
      | ?T => T
    end.

Tactic Notation "put_in_case" ident(id) tactic(c):=
  (let n := eval cbv in id in clear id; c n).
Tactic Notation "put_in_fst_case" ident (id) :=
  put_in_case id fst_Case_tac.


Tactic Notation "cases" constr(ind) tactic(ftac) tactic(c) :=
  let t := ind_type ind in
  let constr_name := fresh "CONSTR_NAME" in
  (run_tac (ftac) on t in constr_name);
  put_in_case constr_name c.

Tactic Notation "cases" constr(ind) tactic(ftac) :=
  cases ind (ftac) (fst_Case_tac).


Tactic Notation "cases" constr(ind) tactic(ftac)
     "as" simple_intropattern(pat) tactic(c) :=
  let t := ind_type ind in
  let constr_name := fresh "CONSTR_NAME" in
  (run_tac (ftac) on t as pat in constr_name);
  put_in_case constr_name c.

Tactic Notation "cases" constr(ind) tactic(ftac)
     "as" simple_intropattern(pat) :=
  cases ind ftac as pat fst_Case_tac.


Tactic Notation "induction'" ident(id) tactic(c) :=
  cases id (induction id) c.
Tactic Notation "induction'" ident(id):=
  cases id (induction id).

Tactic Notation "induction'" ident(id)
     "as" simple_intropattern(pat) tactic(c) :=
  cases id (induction id as pat) as pat c.
Tactic Notation "induction'" ident(id)
     "as" simple_intropattern(pat):=
  cases id (induction id as pat) as pat.


Tactic Notation "destruct'" ident(id) tactic(c) :=
  cases id (destruct id) c.
Tactic Notation "destruct'" ident(id):=
  cases id (destruct id).

Tactic Notation "destruct'" ident(id)
     "as" simple_intropattern(pat) tactic(c) :=
  cases id (destruct id as pat) as pat c.
Tactic Notation "destruct'" ident(id)
     "as" simple_intropattern(pat):=
  cases id (destruct id as pat) as pat.

Tactic Notation "destruct'" ident(id)
     "as" simple_intropattern(pat) "_eqn" tactic(c) :=
  cases id (destruct id as pat _eqn) as pat c.
Tactic Notation "destruct'" ident(id)
     "as" simple_intropattern(pat) "_eqn":=
  cases id (destruct id as pat _eqn) as pat.


(*Tactic Notation "apply'" constr(*_with_bindings*)(thm) tactic(c) :=
  let name_of_case := fresh "NAMEOFCASE" in
  (apply_aux thm resin name_of_case);
  put_in_case name_of_case c.

Tactic Notation "apply'" constr(*_with_bindings*)(thm) :=
  apply' thm fst_Case_tac.

Tactic Notation "eapply'" constr(*_with_bindings*)(thm) tactic(c):=
  let name_of_case := fresh "NAMEOFCASE" in
  (eapply_aux thm resin name_of_case);
  put_in_case name_of_case c.

Tactic Notation "eapply'" constr(*_with_bindings*)(thm) :=
  eapply' thm fst_Case_tac.
*)



(* constructor' does not come with the tactic version, because it does
   not parse. I really don't understand what is going on with this
   integer thing *)
(*
Tactic Notation "constructor'":=
  let name_of_case := fresh "NAMEOFCASE" in
  (constructor_aux resin name_of_case);
  put_in_case name_of_case fst_Case_tac.

Tactic Notation "constructor'" integer(n) :=
  let name_of_case := fresh "NAMEOFCASE" in
  (constructor_aux n resin name_of_case);
  put_in_case name_of_case fst_Case_tac.
*)




Notation "H : T1 → T2" := (forall (H:T1), T2) (at level 100, only parsing, right associativity).

Goal (n : nat →  T : True → (n = n)).
intros.
auto.
Qed.

Definition foo {A} (a:A) := a.
Notation "H : T1 --> T2" := (forall (H:T1), T2) (at level 100, only parsing, right associativity).

Goal (n : foo nat -->  T : foo True --> n = n).
intros.
auto.
Qed.
