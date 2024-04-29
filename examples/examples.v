(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyright (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* Imports made if you have installed the opam package.
If you used `make`, write `Require Import Sniper.` instead *)

From Sniper Require Import Sniper.
From SMTCoq Require Import SMTCoq.
From Sniper Require Import tree.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.


Local Open Scope Z_scope.

(** Examples on lists *)

(* Note that if you run the examples, the call to the SMT solver veriT 
produces a warning.
It is not linked to the preprocessing part but to an issue from 
SMTCoq : https://github.com/smtcoq/smtcoq/issues/108 *)


(* A simple example *)
Goal forall (l : list Z) (x : Z), hd_error l = Some x -> (l <> nil).
Proof. snipe. Qed.

(* The `snipe` and `snipe_no_check` tactics requires instances of equality to be decidable.
   It is in particular visible with type variables. *)
Section Generic.

  Variable A : Type.
  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof.
   scope. 3: verit. 
    (* New goals are open that require instances of equality to be
       decidable. On usual types such as `Z` in the previous example,
       these goals are automatically discharged. On other concrete
       types, it is up to the user to prove it or admit it. *)
  Abort.

  (* On abstract type, it has to be assumed. *)
  Hypothesis HA : CompDec A.
  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof. snipe. Qed.

End Generic.

(* A more involved example *)
Section destruct_auto.

  Variable A : Type.
  Variable HA : CompDec A.


(* This theorem needs a case analysis on x and y *)
 Theorem app_eq_unit (x y:list A) (a:A) :
      x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof.
    destruct x as [|a' l]; [ destruct y as [|a' l] | destruct y as [| a0 l0] ];
      simpl.
    intros H; discriminate H.
    left; split; auto.
    intro H; right; split; auto.
    generalize H.
    generalize (app_nil_r l); intros E.
    rewrite -> E; auto.
    intros H.
    injection H as [= H H0].
    assert ([] = l ++ a0 :: l0) as H1 by auto.
    apply app_cons_not_nil in H1 as [].
  Qed.

(* This example is in the manuscript *)

Theorem app_eq_unit_auto :
    forall (x y: list A) (a:A),
      x ++ y = a :: nil -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof. snipe. Qed.


End destruct_auto.

Section higher_order.

Variable A B C: Type.
Variable HA : CompDec A.
Variable HB : CompDec B.
Variable HC : CompDec C.

(* This example is in the manuscript. 
It is still slow because almost all the transformations are triggered *)

Lemma map_compound : forall (f : A -> B) (g : B -> C) (l : list A), 
map g (map f l) = map (fun x => g (f x)) l.
Proof.
induction l; snipe. Qed.

End higher_order.

Section search.

Variable (A: Type).
Variable (H : CompDec A).


(* Example of searching an element in a list *)
Fixpoint search (x : A) l :=
  match l with
  | [] => false
  | x0 :: l0 => eqb_of_compdec H x x0 || search x l0
  end.

Lemma search_app : forall (x: A) (l1 l2: list A),
    search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof.
  intros x l1 l2. induction l1 as [ | x0 l0 IH].
  - reflexivity.
  - simpl. destruct (eqb_of_compdec H x x0).
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

(* The proof of this lemma, except induction, can be automatized *)
Lemma search_app_snipe : forall (x: A) (l1 l2: list A),
    @search x (l1 ++ l2) = ((@search x l1) || (@search x l2))%bool.
Proof. intros x l1 l2. induction l1 as [ | x0 l0 IH]; snipe. Qed. 


(* Manually using this lemma *)
Lemma search_lemma : forall (x: A) (l1 l2 l3: list A),
    search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof.
  intros x l1 l2 l3. rewrite !search_app.
  rewrite orb_comm with (b1 := search x l3).
  rewrite orb_comm  with (b1 := search x l2) (b2 := search x l1 ).
  rewrite orb_assoc.
  reflexivity.
Qed.

(* It can be fully automatized *)
Lemma snipe_search_lemma : forall (x: A) (l1 l2 l3: list A),
search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof. pose proof search_app. snipe. Qed.

Lemma in_inv : forall (a b:A) (l:list A),
    search b (a :: l) -> orb (eqb_of_compdec H a b) (search b l).
Proof. snipe. Qed.


(*  Another example with an induction *)
Lemma app_nil_r : forall (A: Type) (H: CompDec A) (l:list A), (l ++ [])%list = l.
Proof. intros ; induction l; snipe. Qed. 

End search.

(** Examples on trees *)

Lemma empty_tree_Z2 : forall (t : @tree Z) a t' b,
is_empty t = true -> t <> Node a t' b.
Proof. intros t a t' b; snipe. Qed.

Lemma rev_elements_app :
 forall A (H:CompDec A) s acc, tree.rev_elements_aux A acc s = ((tree.rev_elements A s) ++ acc)%list.
Proof. intros A H s ; induction s.
- pose proof List.app_nil_r; snipe.
- pose proof app_ass ; pose proof List.app_nil_r; snipe. 
Qed.

Lemma rev_elements_node c (H: CompDec c) l x r :
 rev_elements c (Node l x r) = (rev_elements c r ++ x :: rev_elements c l)%list.
Proof. pose proof app_ass ; pose proof rev_elements_app ; snipe. Qed.