From Sniper Require Import Sniper.
Require Import List.
Import ListNotations.


Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) -> ((forall (x1 x2 : bool) (y1 y2 : nat), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : nat) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : bool) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2))).
intro H. 
elimination_polymorphism. (* version of instantiation which looks at the parameters 
of the inductive types *)
Restart.
intro H.
inst. (* version of instantiation which looks at all the subterms of type Type *)
split. assumption. split. assumption. assumption.
Qed.

Goal (forall (A: Type) (l: list A), l = [] \/ exists x xs, l = x :: xs)
-> (forall (l : list nat), l = [] \/ exists x xs, l = x :: xs).
intro H.
elimination_polymorphism app_nil_r. (* it is possible to give lemmas to the tactic 
and they will be monomorphized *)
Restart.
intro H.
inst app_nil_r.
Abort.
