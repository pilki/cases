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
Ltac S3Case name := Case_aux S3Case name.
Ltac S4Case name := Case_aux S4Case name.
Ltac S5Case name := Case_aux S5Case name.
Ltac S6Case name := Case_aux S6Case name.
Ltac S7Case name := Case_aux S7Case name.
Ltac S8Case name := Case_aux S8Case name.
Ltac S9Case name := Case_aux S9Case name.
Ltac S10Case name := Case_aux S10Case name.
Ltac S11Case name := Case_aux S11Case name.
Ltac S12Case name := Case_aux S12Case name.
Ltac S13Case name := Case_aux S13Case name.
Ltac S14Case name := Case_aux S14Case name.
Ltac S15Case name := Case_aux S15Case name.

(* The R(S* )Case tactics rename the case. Usefull for the apply'
   tactic *)

Tactic Notation "RCase_aux" ident(x) constr(old) constr(new) :=
  first [
   assert_eq x old; clear x; set (x := new); simpl in x;  move_to_top x
  | fail 1 "because we are working on a different case" ].

Ltac RCase old new := RCase_aux Case old new.
Ltac RSCase old new := RCase_aux SCase old new.
Ltac RSSCase old new := RCase_aux SSCase old new.
Ltac RS3Case old new := RCase_aux S3Case old new.
Ltac RS4Case old new := RCase_aux S4Case old new.
Ltac RS5Case old new := RCase_aux S5Case old new.
Ltac RS6Case old new := RCase_aux S6Case old new.
Ltac RS7Case old new := RCase_aux S7Case old new.
Ltac RS8Case old new := RCase_aux S8Case old new.
Ltac RS9Case old new := RCase_aux S9Case old new.
Ltac RS10Case old new := RCase_aux S10Case old new.
Ltac RS11Case old new := RCase_aux S11Case old new.
Ltac RS12Case old new := RCase_aux S12Case old new.
Ltac RS13Case old new := RCase_aux S13Case old new.
Ltac RS14Case old new := RCase_aux S14Case old new.
Ltac RS15Case old new := RCase_aux S15Case old new.

(* N(S* )Case are instanciation of RS*Case on "NONAMEGOAL", the name
   produce by apply' when no name is available *)
Ltac NCase := RCase "NONAMEGOAL".
Ltac NSCase := RSCase "NONAMEGOAL".
Ltac NSSCase := RSSCase "NONAMEGOAL".
Ltac NS3Case := RS3Case "NONAMEGOAL".
Ltac NS4Case := RS4Case "NONAMEGOAL".
Ltac NS5Case := RS5Case "NONAMEGOAL".
Ltac NS6Case := RS6Case "NONAMEGOAL".
Ltac NS7Case := RS7Case "NONAMEGOAL".
Ltac NS8Case := RS8Case "NONAMEGOAL".
Ltac NS9Case := RS9Case "NONAMEGOAL".
Ltac NS10Case := RS10Case "NONAMEGOAL".
Ltac NS11Case := RS11Case "NONAMEGOAL".
Ltac NS12Case := RS12Case "NONAMEGOAL".
Ltac NS13Case := RS13Case "NONAMEGOAL".
Ltac NS14Case := RS14Case "NONAMEGOAL".
Ltac NS15Case := RS15Case "NONAMEGOAL".



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
    | fst_Case_aux S3Case (S3Case) s
    | fst_Case_aux S4Case (S4Case) s
    | fst_Case_aux S5Case (S5Case) s
    | fst_Case_aux S6Case (S6Case) s
    | fst_Case_aux S7Case (S7Case) s
    | fst_Case_aux S8Case (S8Case) s
    | fst_Case_aux S9Case (S9Case) s
    | fst_Case_aux S10Case (S10Case) s
    | fst_Case_aux S11Case (S11Case) s
    | fst_Case_aux S12Case (S12Case) s
    | fst_Case_aux S13Case (S13Case) s
    | fst_Case_aux S14Case (S14Case) s
    | fst_Case_aux S15Case (S15Case) s].

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

Tactic Notation "ointros_id" ident(id) :=
  first [exists_hyp id | intros until id].

Tactic Notation "ointros" constr(id) :=
  try (ointros_id id).


Tactic Notation "induction'" constr(id) tactic(c) :=
  ointros id;
  cases id (induction id) c.
Tactic Notation "induction'" constr(id):=
  ointros id;
  cases id (induction id).


Tactic Notation "induction'" constr(id)
     "as" simple_intropattern(pat) tactic(c) :=
  ointros id;
  cases id (induction id as pat) as pat c.
Tactic Notation "induction'" constr(id)
     "as" simple_intropattern(pat):=
  ointros id;
  cases id (induction id as pat) as pat.


Tactic Notation "destruct'" constr(id) tactic(c) :=
  ointros id;
  cases id (destruct id) c.
Tactic Notation "destruct'" constr(id):=
  ointros id;
  cases id (destruct id).

Tactic Notation "destruct'" constr(id)
     "as" simple_intropattern(pat) tactic(c) :=
  ointros id;
  cases id (destruct id as pat) as pat c.
Tactic Notation "destruct'" constr(id)
     "as" simple_intropattern(pat):=
  ointros id;
  cases id (destruct id as pat) as pat.

Tactic Notation "destruct'" constr(id)
     "as" simple_intropattern(pat) "_eqn" tactic(c) :=
  ointros id;
  cases id (destruct id as pat _eqn) as pat c.
Tactic Notation "destruct'" constr(id)
     "as" simple_intropattern(pat) "_eqn":=
  ointros id;
  cases id (destruct id as pat _eqn) as pat.

