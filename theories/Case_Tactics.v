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

(*(* the S*Case' tactics also create an "End_of_case" subgoal *)


Definition __End_of_Case' (name:String.string) := True -> name = name.
Definition __End_of_SCase' (name:String.string) := True -> name = name.
Definition __End_of_SSCase' (name:String.string) := True -> name = name.
Definition __End_of_S3Case' (name:String.string) := True -> name = name.
Definition __End_of_S4Case' (name:String.string) := True -> name = name.
Definition __End_of_S5Case' (name:String.string) := True -> name = name.
Definition __End_of_S6Case' (name:String.string) := True -> name = name.
Definition __End_of_S7Case' (name:String.string) := True -> name = name.
Definition __End_of_S8Case' (name:String.string) := True -> name = name.
Definition __End_of_S9Case' (name:String.string) := True -> name = name.
Definition __End_of_S10Case' (name:String.string) := True -> name = name.
Definition __End_of_S11Case' (name:String.string) := True -> name = name.
Definition __End_of_S12Case' (name:String.string) := True -> name = name.
Definition __End_of_S13Case' (name:String.string) := True -> name = name.
Definition __End_of_S14Case' (name:String.string) := True -> name = name.
Definition __End_of_S15Case' (name:String.string) := True -> name = name.

Lemma EOC1 (name:String.string) :  __End_of_Case' name.
Proof.
  intro; reflexivity. 
Qed.

Lemma __End_of_case'_aux:
  {P:String.string -> Prop| forall name, P name}.
Proof.
  apply (@exist _ _ (fun s => s = s)). intro. auto.
Qed.

Let __End_of_case' := proj1_sig __End_of_case'_aux.
Let EOC0 : forall name, __End_of_case' name := proj2_sig __End_of_case'_aux.

Goal __End_of_case' "salut".
apply (EOC0 "salut").




Lemma EOC2 (name:String.string) :  __End_of_SCase' name. intro; reflexivity. Qed.
Lemma EOC3 (name:String.string) :  __End_of_SSCase' name. intro; reflexivity. Qed.
Lemma EOC4 (name:String.string) :  __End_of_S3Case' name. intro; reflexivity. Qed.
Lemma EOC5 (name:String.string) :  __End_of_S4Case' name. intro; reflexivity. Qed.
Lemma EOC6 (name:String.string) :  __End_of_S5Case' name. intro; reflexivity. Qed.
Lemma EOC7 (name:String.string) :  __End_of_S6Case' name. intro; reflexivity. Qed.
Lemma EOC8 (name:String.string) :  __End_of_S7Case' name. intro; reflexivity. Qed.
Lemma EOC9 (name:String.string) :  __End_of_S8Case' name. intro; reflexivity. Qed.
Lemma EOC10 (name:String.string) :  __End_of_S9Case' name. intro; reflexivity. Qed.
Lemma EOC11 (name:String.string) :  __End_of_S10Case' name. intro; reflexivity. Qed.
Lemma EOC12 (name:String.string) :  __End_of_S11Case' name. intro; reflexivity. Qed.
Lemma EOC13 (name:String.string) :  __End_of_S12Case' name. intro; reflexivity. Qed.
Lemma EOC14 (name:String.string) :  __End_of_S13Case' name. intro; reflexivity. Qed.
Lemma EOC15 (name:String.string) :  __End_of_S14Case' name. intro; reflexivity. Qed.
Lemma EOC16 (name:String.string) :  __End_of_S15Case' name. intro; reflexivity. Qed.

Global Opaque __End_of_Case'
 __End_of_SCase'
 __End_of_SSCase'
 __End_of_S3Case'
 __End_of_S4Case'
 __End_of_S5Case'
 __End_of_S6Case'
 __End_of_S7Case'
 __End_of_S8Case'
 __End_of_S9Case'
 __End_of_S10Case'
 __End_of_S11Case'
 __End_of_S12Case'
 __End_of_S13Case'
 __End_of_S14Case'
 __End_of_S15Case'.


Lemma Case_aux' {P:Type} (A:Type): P -> A -> P.
Proof.
  tauto.
Qed.

Tactic Notation "Case_aux'" ident(x) constr(name) constr(endof):=
  first [
    set (x := name); simpl in x; move_to_top x;
    apply (Case_aux' (endof name));[|simpl]
  | fail 1 "Case' tactics create new cases, they do not check existing ones" ].

Ltac Case' name := Case_aux' Case name __End_of_Case'.
Ltac SCase' name := Case_aux' SCase name __End_of_SCase'.
Ltac SSCase' name := Case_aux' SSCase name __End_of_SSCase'.
Ltac S3Case' name := Case_aux' S3Case name __End_of_S3Case'.
Ltac S4Case' name := Case_aux' S4Case name __End_of_S4Case'.
Ltac S5Case' name := Case_aux' S5Case name __End_of_S5Case'.
Ltac S6Case' name := Case_aux' S6Case name __End_of_S6Case'.
Ltac S7Case' name := Case_aux' S7Case name __End_of_S7Case'.
Ltac S8Case' name := Case_aux' S8Case name __End_of_S8Case'.
Ltac S9Case' name := Case_aux' S9Case name __End_of_S9Case'.
Ltac S10Case' name := Case_aux' S10Case name __End_of_S10Case'.
Ltac S11Case' name := Case_aux' S11Case name __End_of_S11Case'.
Ltac S12Case' name := Case_aux' S12Case name __End_of_S12Case'.
Ltac S13Case' name := Case_aux' S13Case name __End_of_S13Case'.
Ltac S14Case' name := Case_aux' S14Case name __End_of_S14Case'.
Ltac S15Case' name := Case_aux' S15Case name __End_of_S15Case'.


Ltac End_of_Case' name := apply (EOC1 name).
Ltac End_of_SCase' name := apply (EOC2 name).
Ltac End_of_SSCase' name := apply (EOC3 name).
Ltac End_of_S3Case' name := apply (EOC4 name).
Ltac End_of_S4Case' name := apply (EOC5 name).
Ltac End_of_S5Case' name := apply (EOC6 name).
Ltac End_of_S6Case' name := apply (EOC7 name).
Ltac End_of_S7Case' name := apply (EOC8 name).
Ltac End_of_S8Case' name := apply (EOC9 name).
Ltac End_of_S9Case' name := apply (EOC10 name).
Ltac End_of_S10Case' name := apply (EOC11 name).
Ltac End_of_S11Case' name := apply (EOC12 name).
Ltac End_of_S12Case' name := apply (EOC13 name).
Ltac End_of_S13Case' name := apply (EOC14 name).
Ltac End_of_S14Case' name := apply (EOC15 name).
Ltac End_of_S15Case' name := apply (EOC16 name).

Goal True.
  SCase' "lol".
  constructor.
  End_of_SCase' "llol".
  End_of_Case' "mlol".
*)
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

(* register fst_Case_aux so it can be called from the ml code *)
Register First Case fst_Case_tac.


(* tactic to get the string of a constructor, in CPS style *)
Tactic Notation "string_of" constr(a) tactic(cont) :=
    let A := fresh in
    string of a in A;
    let strA := eval cbv in A in
    clear A;
    cont strA.

Tactic Notation "string_of_without" constr(a) tactic(cont) :=
    let A := fresh in
    string of a without notations in A;
    let strA := eval cbv in A in
    clear A;
    cont strA.


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
  (* special cases for or and or_bool *)
  match t with
    | ?P1 \/ ?P2 =>
      string_of P1 (fun strP1 =>
      string_of P2 (fun strP2 =>
      ftac; [c strP1 | c strP2]))
    | {?P1} + {?P2} =>
      string_of P1 (fun strP1 =>
      string_of P2 (fun strP2 =>
      ftac; [c strP1 | c strP2]))
    | _ =>
      let constr_name := fresh "CONSTR_NAME" in
      (run_tac (ftac) on t in constr_name);
      put_in_case constr_name c
  end.

Tactic Notation "cases" constr(ind) tactic(ftac) :=
  cases ind (ftac) (fst_Case_tac).


Tactic Notation "cases" constr(ind) tactic(ftac)
     "as" simple_intropattern(pat) tactic(c) :=
  let t := ind_type ind in
  (* special cases for or and or_bool *)
  match t with
    | ?P1 \/ ?P2 =>
      string_of P1 (fun strP1 =>
      string_of P2 (fun strP2 =>
      ftac; [c strP1 | c strP2]))
    | {?P1} + {?P2} =>
      string_of P1 (fun strP1 =>
      string_of P2 (fun strP2 =>
      ftac; [c strP1 | c strP2]))
    | _ =>
      let constr_name := fresh "CONSTR_NAME" in
        (run_tac (ftac) on t as pat in constr_name);
        put_in_case constr_name c
  end.

Tactic Notation "cases" constr(ind) tactic(ftac)
     "as" simple_intropattern(pat) :=
  cases ind ftac as pat fst_Case_tac.

Tactic Notation "apply_mutual_ind" constr(lemma) "on" constr_list(inds) :=
  let constr_name := fresh "CONSTR_NAME" in
    (run_tac (apply lemma) ons inds in constr_name);
    put_in_case constr_name (fst_Case_tac).


(*Ltac ointros id :=
  first [exists_hyp id | intros until id | idtac].*)

Tactic Notation "ointros" constr(id) :=  idtac.
Tactic Notation "ointros" ident(id) :=
  first [exists_hyp id | intros until id|idtac].

Tactic Notation "induction'" ident(id) tactic(c):=
  ointros id;
  cases id (induction id) c.
Tactic Notation "induction'" ident(id):=
  ointros id;
  cases id (induction id).


Tactic Notation "induction'" ident(id)
     "as" simple_intropattern(pat) tactic(c) :=
  ointros id;
  cases id (induction id as pat) as pat c.
Tactic Notation "induction'" ident(id)
     "as" simple_intropattern(pat):=
  ointros id;
  cases id (induction id as pat) as pat.

Tactic Notation "induction'" "1" :=
  intros *;
  let H := fresh in intro H; induction' H.
Tactic Notation "induction'" "2" :=
  intros *; intro; induction' 1.
Tactic Notation "induction'" "3" :=
  intros *; intro; induction' 2.
Tactic Notation "induction'" "4" :=
  intros *; intro; induction' 3.
Tactic Notation "induction'" "5" :=
  intros *; intro; induction' 4.


Tactic Notation "destruct'" constr(id) tactic(c) :=
  ointros id;
  cases id (destruct id) c.
Tactic Notation "destruct'" constr(id):=
  cases id (destruct id).
Tactic Notation "destruct'" ident(id):=
  ointros id;
  cases id (destruct id).

Tactic Notation "destruct'" constr(id)
     "as" simple_intropattern(pat) tactic(c) :=
  cases id (destruct id as pat) as pat c.
Tactic Notation "destruct'" ident(id)
     "as" simple_intropattern(pat) tactic(c) :=
  ointros id;
  cases id (destruct id as pat) as pat c.

Tactic Notation "destruct'" constr(id)
     "as" simple_intropattern(pat):=
  cases id (destruct id as pat) as pat.
Tactic Notation "destruct'" ident(id)
     "as" simple_intropattern(pat):=
  ointros id;
  cases id (destruct id as pat) as pat.

Tactic Notation "destruct'" constr(id)
     "as" simple_intropattern(pat) "_eqn" tactic(c) :=
  cases id (destruct id as pat _eqn) as pat c.
Tactic Notation "destruct'" ident(id)
     "as" simple_intropattern(pat) "_eqn" tactic(c) :=
  ointros id;
  cases id (destruct id as pat _eqn) as pat c.

Tactic Notation "destruct'" constr(id)
     "as" simple_intropattern(pat) "_eqn":=
  cases id (destruct id as pat _eqn) as pat.
Tactic Notation "destruct'" ident(id)
     "as" simple_intropattern(pat) "_eqn":=
  ointros id;
  cases id (destruct id as pat _eqn) as pat.


Tactic Notation "destruct'" constr(id)
     "as" simple_intropattern(pat) "_eqn" tactic(c) ":" ident(H) :=
  cases id (destruct id as pat _eqn:H) as pat c.
Tactic Notation "destruct'" ident(id)
     "as" simple_intropattern(pat) "_eqn" tactic(c) ":" ident(H) :=
  ointros id;
  cases id (destruct id as pat _eqn:H) as pat c.

Tactic Notation "destruct'" constr(id)
     "as" simple_intropattern(pat) "_eqn" ":" ident(H) :=
  cases id (destruct id as pat _eqn:H) as pat.
Tactic Notation "destruct'" ident(id)
     "as" simple_intropattern(pat) "_eqn" ":" ident(H) :=
  ointros id;
  cases id (destruct id as pat _eqn:H) as pat.


(* since multiple destruct is not supported, we do not need to specify
   a pattern to be allowed to use the _eqn extension *)


Tactic Notation "case'" constr(id) tactic(c) :=
  ointros id;
  cases id (case id) c.
Tactic Notation "case'" constr(id):=
  cases id (case id).
Tactic Notation "case'" ident(id):=
  ointros id;
  cases id (case id).

Tactic Notation "case'" constr(id)
     "as" simple_intropattern(pat) tactic(c) :=
  cases id (case id as pat) as pat c.
Tactic Notation "case'" ident(id)
     "as" simple_intropattern(pat) tactic(c) :=
  ointros id;
  cases id (case id as pat) as pat c.

Tactic Notation "case'" constr(id)
     "as" simple_intropattern(pat):=
  cases id (case id as pat) as pat.
Tactic Notation "case'" ident(id)
     "as" simple_intropattern(pat):=
  ointros id;
  cases id (case id as pat) as pat.

Tactic Notation "case'" constr(id)
     "as" simple_intropattern(pat) "_eqn" tactic(c) :=
  cases id (case id as pat _eqn) as pat c.
Tactic Notation "case'" ident(id)
     "as" simple_intropattern(pat) "_eqn" tactic(c) :=
  ointros id;
  cases id (case id as pat _eqn) as pat c.

Tactic Notation "case'" constr(id)
     "as" simple_intropattern(pat) "_eqn":=
  cases id (case id as pat _eqn) as pat.
Tactic Notation "case'" ident(id)
     "as" simple_intropattern(pat) "_eqn":=
  ointros id;
  cases id (case id as pat _eqn) as pat.

(* since multiple case is not supported, we do not need to specify
   a pattern to be allowed to use the _eqn extension *)


(* XXXXX this does NOT work in the general case *)
Tactic Notation "inversion'" hyp(id) tactic(c):=
  cases id (inversion id) c.
Tactic Notation "inversion'" hyp(id):=
  cases id (inversion id).


Inductive _MARK_CLEAR_ : Prop :=
  _MARK_CLEAR_INTRO_: _MARK_CLEAR_.

Ltac header_clear' :=
  generalize _MARK_CLEAR_INTRO_;
  repeat match reverse goal with
    | H : String.string |- _ =>
      let strA := eval cbv in H in
      match strA with
        | String.EmptyString => revert H
        | String.String _ _ => revert H
      end
  end.

Ltac footer_clear' :=
  repeat match goal with
           | H : _MARK_CLEAR_ |- _ => fail 1
           | |- _ => intro at top
         end;
  match goal with
    | H : _MARK_CLEAR_ |- _ => clear H
  end.

Tactic Notation "clear'" :=
  header_clear'; clear; footer_clear'.

Tactic Notation "clear'" "-" hyp_list(Hl) :=
  header_clear'; clear - Hl; footer_clear'.

Definition __END_OF_ASSERT__ (str: String.string) (A:Type) := A.
Lemma remove__END_OF_ASSERT__ str A:
  A -> __END_OF_ASSERT__  str A. unfold __END_OF_ASSERT__; auto. Qed.
Lemma add__END_OF_ASSERT__ str A:
  __END_OF_ASSERT__ str A -> A. unfold __END_OF_ASSERT__; auto. Qed.
Global Opaque __END_OF_ASSERT__.

Tactic Notation "End_of_assert" := apply (remove__END_OF_ASSERT__ "").
Tactic Notation "End_of_assert" ident(id) :=
  string_of id (fun strid =>
    apply (remove__END_OF_ASSERT__ strid)).
Tactic Notation "assert'" constr(H) :=
  assert (H);[fst_Case_tac "Assert" | apply (add__END_OF_ASSERT__ "")].
  
Tactic Notation "assert'" constr(H)  "as" ident(id):=
  pose proof (Coq.Init.Logic.I) as id;
  string_of id (fun strid =>
  clear id;
  assert (H) as id;[ fst_Case_tac ("Assert: " ^^ strid)
                   | apply (add__END_OF_ASSERT__ strid)]).
Tactic Notation "split'" :=
  match goal with
    |  |- _ <-> _ =>
      split ; [fst_Case_tac "->" | fst_Case_tac "<-"]
    | |- _ /\ _ =>
      split ; [fst_Case_tac "left" | fst_Case_tac "right"]
  end.



(* verification *)

Goal forall n, n >0 -> True.
induction' n; auto.
Qed.

Goal forall n, n >0 -> True.
intros. induction' n; auto.
Qed.

Goal forall n, n > 0 -> True.
  destruct' n; auto.
Qed.

Goal forall n, n > 0 -> True.
  destruct' 12; auto.
Qed.
