From Sniper Require Import Sniper. 

Goal (forall (A B : Type) (a: A) (l : list B) (f : A -> B -> A), 
List.fold_left f nil a = a).
intros. 
prenex_higher_order. Abort.

Goal (forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
List.map g (List.map f l) = map (fun x => g (f x)) l).
intros.
prenex_higher_order.
Abort.