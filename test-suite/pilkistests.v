Require Import Constructors Bvector.
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

Tactic Notation "cases" constr(ind) tactic(ftac) tactic(c) :=
  let t := ind_type ind in
  let constr_name := fresh "CONSTR_NAME" in
  (run_tac (ftac) on t in constr_name);
  (let n := eval cbv in constr_name in clear constr_name; c n).

Tactic Notation "cases" constr(ind) tactic(ftac) :=
  let t := ind_type ind in
  let constr_name := fresh "CONSTR_NAME" in
  (run_tac (ftac) on t in constr_name);
  (let n := eval cbv in constr_name in clear constr_name; fst_Case_tac n).

Tactic Notation "cases" constr(ind) tactic(ftac)
     "as" simple_intropattern(pat) tactic(c) :=
  let t := ind_type ind in
  let constr_name := fresh "CONSTR_NAME" in
  (run_tac (ftac) on t as pat in constr_name);
  (let n := eval cbv in constr_name in clear constr_name; c n).

Tactic Notation "cases" constr(ind) tactic(ftac)
     "as" simple_intropattern(pat) :=
  let t := ind_type ind in
  let constr_name := fresh "CONSTR_NAME" in
  (run_tac (ftac) on t as pat in constr_name);
  (let n := eval cbv in constr_name in clear constr_name; fst_Case_tac n).


Tactic Notation "induction'" ident(id) tactic(c) :=
  cases id (induction id) c.
Tactic Notation "induction'" ident(id):=
  cases id (induction id).

Tactic Notation "induction'" ident(id)
     "as" simple_intropattern(pat) tactic(c) :=
  cases id (induction id) as pat c.
Tactic Notation "induction'" ident(id)
     "as" simple_intropattern(pat):=
  cases id (induction id) as pat.




Inductive foo : Type :=
| foo1 : nat -> foo
| foo2 : foo.


Inductive bar: nat -> Prop :=
| barO: forall b:bool, bar O
| barS: forall n (f: False), bar (S n).


Goal forall (f: foo) (n: nat) (l: list (bar n)), True.
Proof.
  intros.
  induction' f as [n'|]. induction' n. induction' l.
  Case "foo1 n'"; SCase "0"; SSCase "@nil".
  auto.
  Case "foo1 n'"; SCase "0"; SSCase "cons".
  auto.
  Case "foo1 n'"; SCase "S".
  auto.
  Case "foo2".
  auto.
Qed.
