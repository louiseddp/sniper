From Sniper Require Import Sniper.

Require Import List Bool.
Import ListNotations.

Section Generic.

  Goal forall (l : list nat) (x : nat),  hd_error l = Some x -> (l <> nil).
  Proof. 
    snipe. 
  Qed.
    (* `snipe` open new goals that require instances of equality to be
       decidable. On usual types such as integers in the previous
       example, these goals are automatically discharged. On other
       concrete types, it is up to the user to prove it or admit it. On
       type variables, it should be added as an hypothesis. *)

  Goal forall (A: Type) (HA : CompDec A) (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof.
    snipe. 
  Qed.

(* Another example with an induction *)
Lemma app_nil_r : forall (A: Type) (H: CompDec A) (l:list A), (l ++ [])%list = l.
Proof. intros A H; induction l; snipe. Qed.


End Generic.

Section Search.

Fixpoint search {A : Type} {H: CompDec A} (x : A) l :=
  match l with
  | [] => false
  | x0 :: l0 => eqb_of_compdec H x x0 || search x l0
  end.

(* The proof of this lemma, except induction, can be automatized *)
Lemma search_app_snipe : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A),
    search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof. induction l1 ; snipe. Qed.

(* Using a lemma *)
Lemma snipe_search_lemma : forall (A : Type) (H : CompDec A) (x: A) (l1 l2 l3: list A),
search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof. snipe @search_app_snipe. Qed.

(* Another example with search *)
Lemma in_inv : forall (A: Type) (HA : CompDec A) (a b:A) (l:list A),
    search b (a :: l) -> eqb_of_compdec HA a b \/ search b l.
Proof. snipe. Qed.

End Search.







