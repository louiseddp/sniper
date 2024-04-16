From Sniper Require Import elimination_fixpoints.
Require Import List.
Import ListNotations.

Section example.

Variable toto : nat -> nat.

Goal False -> False. intros. 
assert (H0 : (forall (A : Type) (l : list A), 
length l = (fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) l)) by reflexivity. 
eliminate_fix_hyp H0.
assert (H1 : (forall (A : Type) (l : list A), 
length l = (fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) l) -> False -> True) by (intros H1 HFalse; destruct HFalse).
eliminate_fix_hyp H1.
assert (H2 : forall n m, toto (Nat.add n m) =
(fix add (n m : nat) :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end) n m) by admit.
eliminate_fix_hyp H2.
assert (H3 : forall A l, toto (length l) = toto ((fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) l) -> True) by admit. eliminate_fix_hyp H3.
Abort.

End example.