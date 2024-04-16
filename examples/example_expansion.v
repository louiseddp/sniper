From Sniper Require Import expand.

Section example.

Variable (f g : nat -> nat -> bool).
Variable (H : f = g).

Goal False.
expand_hyp H.
assert (H1 : length = fun A : Type =>
fix length (l : list A) : nat :=
  match l with
  | nil => 0
  | (_ :: l')%list => S (length l')
  end) by reflexivity.
expand_hyp H1.
Abort.

End example.
