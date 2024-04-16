From Sniper Require Import elimination_pattern_matching.
Require Import List.
Import ListNotations.

Section example.

Fixpoint nth {A : Type} (n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, _other => default
      | S m, [] => default
      | S m, x :: t => nth m t default
    end.

Goal True.
assert (H : forall n m : nat,
     n + m = match n with
             | 0 => m
             | S p => S (p + m)
             end) by (intros; destruct n ; reflexivity).
eliminate_dependent_pattern_matching H.
assert (H' : forall (A : Type) (l : list A),
    length l =
    match l with
    | nil => 0
    | (_ :: l')%list => S (length l')
    end) by (intros; destruct l; reflexivity).
eliminate_dependent_pattern_matching H'.
assert (H'' : forall (A : Type) (n : nat) (l : list A) (default : A),
    nth n l default =
    match n with
    | 0 => match l with
           | [] => default
           | x :: _ => x
           end
    | S m =>
        match l with
        | [] => default
        | _ :: t => nth m t default
        end
    end) by (intros; destruct l ; reflexivity).
eliminate_dependent_pattern_matching H''.
Abort.

End example.