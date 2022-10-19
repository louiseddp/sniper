From MetaCoq.Template Require Import utils All.
Unset MetaCoq Strict Unquote Universe Mode.
From SMTCoq Require Import SMTCoq.
Require Import Sniper.
Import MCMonadNotation.
Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.
Require Import Bool.

(* A first example :
- mem n l is true whenever n belongs to l 
- the plugin linearize the type of MemMatch because n is mentionned twice (and 
we want to define a function by pattern matching so we need fresh pattern variables)
- then it generates an equivalent boolean fixpoint defined by pattern matching
on the list 
- it also generates the correctness lemma and uses a tactic based on
heuristics to inhabitate it
*) 

Inductive mem : Z -> list Z -> Prop :=
    MemMatch : forall (xs : list Z) (n : Z), mem n (n :: xs)
  | MemRecur : forall (xs : list Z) (n n' : Z), mem n xs -> mem n (n' :: xs).

(* running the main command *)
MetaCoq Run (decide mem []). 
Next Obligation.
(* the proof can be automatized thanks to tactics :
it generates a proof term decidable_proof that we use here
*)
apply decidable_proof. Qed.

(* Another parametric example : 
the predicate smaller_than_all holds between a
natural number and a list of integers whenever the term is
smaller than all the elements of the list
Here, we need to pass the quotations of Z.le, the boolean version of Z.le and the proof 
of equivalence as arguments to the command
*) 

Inductive smaller_than_all : Z -> list Z -> Prop :=
 | sNil  : forall n, smaller_than_all n nil
 | sCons : forall n n' l, BinInt.Z.le n n' -> smaller_than_all n l -> smaller_than_all n (n' :: l).


(* Here the proof should be done manually because we need to use an
intermediate lemma Z.leb_le *)
MetaCoq Run (decide (smaller_than_all) [(<%Z.le%>, <%Z.leb%>, <%Z.leb_le%>)]).
Next Obligation.
split.
- intros H1. induction H1; auto.
simpl. apply Z.leb_le in H. rewrite H. rewrite IHsmaller_than_all. auto.
- intros H1. induction H0. constructor. simpl in H1;
elim_and_and_or. constructor. apply Z.leb_le. assumption. apply IHlist. assumption. Qed.


(* Example of proof automation with snipe and the decided predicates *)

Lemma mem_imp_not_nil_fail : (forall (n : Z) (l : list Z), 
mem n l -> l <> []).
Proof. Fail snipe. (* snipe does not know about inductive predicates *) Abort.

(* We add to Trakt's database the information that mem_linear_decidable
is a decidable version of mem and the proof of this fact 
and snipe will use it to reason about the boolean function instead
of the predicate *)

Trakt Add Relation 2 mem mem_linear_decidable decidable_lemma.

Lemma mem_imp_not_nil : (forall (n : Z) (l : list Z), 
mem n l -> l <> []).
Proof. snipe. Qed.

(* We do the same for smaller_than_all *)
Trakt Add Relation 2 smaller_than_all smaller_than_all_decidable decidable_lemma0.

Lemma smaller_than_all_nil : (forall (z: Z), smaller_than_all z nil).
Proof. snipe. Qed.

(* An example with an inductive type which takes a parameter: 
all the elements of the list are smaller than the one given as parameters *)

Inductive elt_smaller_than (n : nat) : list nat -> Prop :=
| smThanNil : elt_smaller_than n nil
| smThanCons : forall (n' : nat) (l : list nat), Nat.le n' n -> elt_smaller_than n l -> 
elt_smaller_than n (n' :: l).

MetaCoq Run (decide (elt_smaller_than) [(<%Nat.le%>, <%Nat.leb%>, <%Nat.leb_le%>)]).
Next Obligation.
split.
- intro Hyp. induction Hyp. auto. simpl. rewrite IHHyp. simpl. rewrite Nat.leb_le. 
assumption.
- intros Hyp. induction H. constructor. constructor; simpl in Hyp; 
elim_and_and_or. apply Nat.leb_le. assumption. apply IHlist. assumption. Qed.

Trakt Add Relation 2 elt_smaller_than elt_smaller_than_decidable decidable_lemma1.

Lemma smaller_than_mem : 
forall (n n' : Z) (l : list Z), smaller_than_all n l -> mem n' l -> Z.le n n'.
Proof.
intros n n' l H1 H2. induction l; snipe. Qed.


  







