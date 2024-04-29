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

Inductive vect (A : Type) : nat -> Type :=
  |nil : vect A 0
  |cons : forall (h:A) (n:nat), vect A n -> vect A (S n).

Definition vect_tail {A: Type} (n: nat) (v: vect A n) :=
  match v as x
  return match x with 
    | nil => vect A 0
    | cons x n h => vect A n
  end with
    | nil => nil A
    | cons x n h => h
  end.

Goal True.
assert (H : forall (A: Type) (n: nat) (v : vect A n), 
  vect_tail n v =
  match v with
    | nil => nil A
    | cons x n h => h
  end) by (intros; destruct v; reflexivity).
eliminate_dependent_pattern_matching H.
Abort.

End example.