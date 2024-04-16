From Sniper Require Import Sniper.

Goal (forall (A: Type) (x :A), (fun (A: Type) (x: A) => x) A x = x).
Proof. 
anonymous_funs.
Abort.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
Proof.
intros.
assert (H : (fun x => x + 1) 42 = 43) by reflexivity.
anonymous_funs. Abort. 