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

Tactic Notation "cases" constr(ind) tactic(ftac) tactic(c) :=
  let constr_name := fresh "CONSTR_NAME" in
  (run_tac (ftac) on ind in constr_name);
  (let n := eval cbv in constr_name in clear constr_name; c n).

Tactic Notation "cases" constr(ind) tactic(ftac) :=
  let constr_name := fresh "CONSTR_NAME" in
  (run_tac (ftac) on ind in constr_name);
  (let n := eval cbv in constr_name in clear constr_name; fst_Case_tac n).

Tactic Notation "induction'" ident(id) tactic(c) :=
  let t := type of id in
  cases t (induction id) c.
Tactic Notation "induction'" ident(id):=
  let t := type of id in
  cases t (induction id).


Inductive foo : Type :=
| foo1 : nat -> foo
| foo2 : foo.


Inductive bar: nat -> Prop :=
| barO: forall b:bool, bar O
| barS: forall n (f: False), bar (S n).


Goal forall (f: foo) (n: nat) (l: list (bar n)), True.
Proof.
  intros.
  induction' f. induction' n. induction' l.
  Case "foo1". SCase "0". SSCase "@nil".
  auto.
  Case "foo1". SCase "0". SSCase "cons".
  auto.
  Case "foo1". SCase "S".
  auto. 
  Case "foo2".
  auto.
Qed.
  