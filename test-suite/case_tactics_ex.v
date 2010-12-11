Require Import Case_Tactics.



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
