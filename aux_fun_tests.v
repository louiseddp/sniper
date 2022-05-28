

(*** Metavariables conventions ***)
(* indu : inductive  (the 1st argument of the constructor tInd )*)
(* mind: mutual_inductive_body *)
(* ooind : one_inductive_body *)
(* p : number of parameters of an inductive *)
(* i : rank of an oind in a mind *) 
(* n : number of oind's in a mind *)

Require Import utilities. 
Require Import interpretation_algebraic_types.
Require Import elimination_polymorphism.
Require Import eliminators.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import ZArith.

(* function to comment :  pose_inductive_tac *)

Open Scope string_scope.  

Import ListNotations MonadNotation. 


Print list.

Inductive nelist {A : Type} : Type :=
	sing :  A -> nelist    | necons : A -> nelist -> nelist .
   
   
Example blut := @nelist nat.

Inductive biclist {A B : Type} : Type :=
(*  sing1 : A -> biclist  
  | sing2 : B -> biclist *)
  | bicnil : biclist
  | cons1 : A -> biclist -> biclist
  | cons2 : B -> biclist -> biclist. 

(*

Ltac proj k n x :=
   let k0 := n - k 
   match k with
   | 0 => match 

let x := fresh in pose constr:(k - 1) constr:(n -1) 
*)


Definition get_ind_ident (kerna : kername) := let (mdp , idind) := kerna in idind.


Locate pose_inductive_tac.

MetaCoq Quote Definition Type_reif := Eval hnf in Type.
MetaCoq Quote Definition Prop_reif := Eval hnf in Prop.
MetaCoq Quote Definition Set_reif := Eval hnf in Set.
MetaCoq Quote Definition eq_reif := Eval hnf in @eq. 

MetaCoq Quote Definition nat_reif := nat.
MetaCoq Quote Recursively Definition nat_env_reif := nat.



Definition list_nat := @list nat.
MetaCoq Quote Definition list_nat_reif :=  (@list nat).
MetaCoq Quote Recursively Definition list_nat_env_reif := list_nat.             
MetaCoq Quote Definition cons_nat_type_reif := (nat -> list_nat -> list_nat).
MetaCoq Quote Definition nil_type_reif := (forall (A : Type), list A).
(* \Q nil_type_reif and cons_nat_reif do not work because do not
currently have  the right universes levels *)


MetaCoq Quote Definition cons_reif := cons.
MetaCoq Quote Definition sing_reif := sing.
MetaCoq Quote Definition necons_reif := necons.


MetaCoq Quote Definition bicnil_reif := bicnil.
MetaCoq Quote Definition cons1_reif := cons1.
MetaCoq Quote Definition cons2_reif := cons2.





MetaCoq Quote Definition zero_reif := 0.
MetaCoq Quote Definition one_reif := 1.
MetaCoq Quote Definition two_reif := 2.


MetaCoq Quote Definition nil_nat_reif := Eval cbn in (@nil nat).
MetaCoq Quote Definition list_one_two_reif := Eval cbn in [1 ; 2].
MetaCoq Quote Definition list_one_two_two_reif := Eval cbn in [1 ; 2 ; 2].

MetaCoq Quote Definition list_one_two_two_reif' := (List.app [1] [2 ; 2]).



(** Reified objects functions *)
 
Definition cons_nat := @cons nat.



MetaCoq Quote Definition length_reif := @List.length.
MetaCoq Quote Definition le_reif := le.
MetaCoq Quote Definition S_reif := Eval cbn in S.
MetaCoq Quote Recursively Definition S_env_reif := S.
Print S_env_reif.
Print S_reif. 
MetaCoq Quote Definition O_reif := O.
MetaCoq Quote Definition add_reif := Eval cbn in Nat.add.
MetaCoq Quote Definition nil_reif := nil.
MetaCoq Quote Recursively Definition nil_env_reif := nil.
MetaCoq Quote Recursively Definition cons_env_reif := cons.
MetaCoq Quote Recursively Definition cons_nat_env_reif := cons_nat.
MetaCoq Quote Definition cons_nat_reif := cons_nat.
MetaCoq Quote Definition list_reif := @list.
MetaCoq Quote Recursively Definition list_env_reif := @list.

MetaCoq Quote Definition nelist_reif := @nelist.
Print nelist_reif.
Print list_reif.
MetaCoq Quote Recursively Definition nelist_env_reif := @nelist.

MetaCoq Quote Definition biclist_reif := @biclist.

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

MetaCoq Quote Definition even_reif := even.
MetaCoq Quote Definition odd_reif := odd.




MetaCoq Quote Definition cons_typ_reif := (forall (A: Type), A -> list A -> list A).

Print list_env_reif.

Definition nat_indu := ltac:(let s := fresh in  pose_inductive_tac nat s ; exact s).
Definition list_indu := ltac:(let s := fresh in  pose_inductive_tac list s ; exact s).
Definition list_nat_indu := ltac:(let s := fresh in  pose_inductive_tac list s ; exact s).


(* \TODO eliminate the "let in" which currently appear in list_mind *)
Definition nat_mind :=  ltac:(let x := fresh in pose_mind_tac nat x ; cbn in x ; exact x).
Definition list_mind :=  ltac:(let x := fresh in pose_mind_tac list x ; cbn in x ; exact x).
Definition nelist_mind :=  ltac:(let x := fresh in pose_mind_tac @nelist x ; cbn in x ; exact x).
Definition biclist_mind :=  ltac:(let x := fresh in pose_mind_tac @biclist x ; cbn in x ; exact x).
Print biclist_mind.


Goal False.
let x:= constr:(get_params_from_mind biclist_mind) in pose x as biclist_params ; compute in biclist_params.
Abort.


Definition nat_oind := {|
ind_name := "nat"%string;
ind_type := tSort (Universe.of_levels (inr Level.lSet));
ind_kelim := IntoAny;
ind_ctors := [("O"%string, tRel 0, 0);
             ("S"%string,
             tProd
               {|
               binder_name := nAnon;
               binder_relevance := Relevant |}
               (tRel 0) (tRel 1), 1)];
ind_projs := [];
ind_relevance := Relevant |}.




Ltac pose_oind_tac t i idn := let s := fresh "s" in pose_mind_tac t s ; pose (nth i s.(ind_bodies)  nat_oind) as idn; simpl in idn ; clear s.
(* pose_oind take an (unreified) inductive  I and outputs the i-th one_inductive_block of I *) 
(* when I is not a mutual inductive, i should be equal to 0 *)
(* the tactic uses nat_oind as the defaut value for nth *)

Definition list_oind := ltac:(let s := fresh in pose_oind_tac list 0 s ; compute in s ; exact s).


(* pose_list_ctor_oind t i idn computes the lists of types of the constructors of i-th one inductive block of t and poses it as idn.
   Then, idn has type list term
*)
Ltac pose_list_ctor_oind t i idn := let x := fresh  in  pose_oind_tac t i x ; let lctor := constr:(list_ctor_oind x) in pose lctor as idn ; compute in idn ; clear x.

Goal False.
pose_list_ctor_oind list 0 kik.
clear.
pose_list_ctor_oind even 0 evenctor.
pose_list_ctor_oind even 1 oddctor.
let x := constr:(debruijn0 list_indu 2) in pose x as kik ; unfold debruijn0 in kik ; unfold utilities.switch_inductive in kik ; simpl in kik.

Abort.

(*testing get_ctors_and_types *)
Goal False. 
let x := constr:(get_ctors_and_types_i list_indu 1 1 0 [] list_oind) in pose x as gttlist ; compute in gttlist.
Abort.

(* \TMP
Definition get_ctors_and_types_i (indu : inductive) (p :nat) (n: nat) (i : nat) (u : Instance.t) (oind : one_inductive_body ) *)
             

Ltac kooooo t na :=
   constr:((4,5)).

Goal False.
let x := kooooo list blut in pose x as kik.
ltac:(let x := get_eliminators_st_return0 list ik in pose x as kik).
Abort.

Ltac split_info1 I na := 
   let I_info := fresh "I_info" in get_info_quote I  I_info ; 
   let I_indu := fresh I "_indu" in 
   pose (I_info.2) as I_indu ; compute in I_indu;
   let I_app := fresh I "_app" in 
   pose I_info.1.2 as I_app ; compute in I_app ;
   let I_lpars := fresh I "_lpars" in 
   pose I_info.1.1.2 as I_lpars ; compute in I_lpars ;
   let I_tot_args := fresh I "_tot_args" in 
   pose I_info.1.1.1.2 as I_tot_args ; compute in  I_tot_args;
   let I_list_args := fresh I "_list_args" in 
   pose I_info.1.1.1.1.2 as I_list_args ; compute in I_list_args;
   let I_list_ty := fresh I "_list_ty" in 
   pose I_info.1.1.1.1.1.2 as I_list_ty ; compute in I_list_ty ;
   let I_ty_pars := fresh I "_list_pars" in 
   pose I_info.1.1.1.1.1.1.2 as I_ty_pars;  compute in I_ty_pars;
   let I_npars := fresh I "_npars" in  
   pose I_info.1.1.1.1.1.1.1 as I_npars ;  compute in I_npars; clear I_info.

(*   x := constr:((((((((npars,ty_pars),list_ty),
   list_args),total_args),list_of_pars_rel),I_app),I_indu)) 
      *)


(*  _list_of_pars_rel : list term censé représenter ????
*  nat_list_of_pars_rel = []
*  list_list_of_pars_rel = [Rel 3]
*   _list_of_pars_rel = [Rel 4]   
* \TODO trouver exemple où cardinal > 1
*)

(* _list_ctors_reif : list term   \Q pourquoi forcément appli avec 0 ou 1 evar ?
* nat_list_ctors_reif = [nat_reif [] ; S_reif []]
* list_list_ctors_reif = [nil_reif [evar fresh] ; cons_reif [evar fresh]]
* nelist_list_ctors_reif = [sing_reif [evar fresh] ; necons_reif [evar fresh]
*)

(* _list_ty_default := lift_rec_rev list_ty_default0  : list term
*  nat_list_ty_default = [nat_reif ]
*  list_list_ty_default = [list_reif [Rel 1] ; Rel 0 ]
*  nelist_list_ty_default = [nelist_reif [Rel 2] ; Rel 1 ; Rel 0]
*)

(* _list_ty_default0 := flatten list_args : list term
*  nat_list_ty_default0 = [nat_reif ] = nat_list_ty_default0 
*  list_list_ty_default0 = [Rel 0 ; list_reif [Rel 0]
*  nelist_list_ty_default0 = [Rel 0 ; Rel 0 ; nelist_reif [Rel 0] ]
*)

(* \Remark return_ty := eval cbv in (lift 2 0 (mkLam I_app (lift0 1  ty_default)))*)

(* _list_args_len : list (list term * nat )
* nat_list_args_len = [ ( [] , 0) , ([S_reif] ; 1 ]
* list_list_args_len =  [ ( [] , 0) ;   ([ Rel 0; list_reif [Rel 0]] 2)]
* nelist_list_args_len = [ ([Rel 0], 1) ] ; ([Rel 0 ; nelist_reif [Rel 0]], 2) ]
* \Comm: semble être seulement un calcul intermédiaire, on peut l'éliminer ensuite
*)


(* _app : term     I_app := get_indu_app_to_params I_rec_term npars
nat_app = nat_reif
list_app : list_reif [tRel 0]
nelist_app = nelist_reif [Rel 0]
*)

Goal False.
split_info1 list kik.
let x := constr:(rev_list_map list_list_args ) in pose x as list_tycon ; compute in list_tycon. 

let x := constr:(proj_one_ctor_params_default_var [Set_reif] (tApp list_reif [tRel 0]) (tRel 70) list_indu 1 0 2  list_tycon (tRel 49))
in pose x as kik ; compute in kik. 
let x := constr:(proj_one_ctor_params_default_var0 [Set_reif] (tApp list_reif [tRel 0]) (tRel 70) list_indu 1 0 2  list_tycon (tRel 49))
in pose x as koo ; compute in koo. 
Abort. 



Ltac split_info2 I na := (* \TODO supprimer list_args, qui est déjà récupéré par split_info1*)
   let Io := fresh "Io" in get_info2_quote I Io ;
   let I_lpr := fresh I "_list_of_pars_rel" in pose Io.2 as I_lpr ; compute in I_lpr ;
   let I_lcr := fresh I "_list_ctors_reif" in pose Io.1.2 as I_lcr ; compute in I_lcr ;
   let I_nbc := fresh I "_nbconstruct" in pose Io.1.1.2 as I_nbc ; compute in I_nbc ;
   let I_ltd := fresh I "_list_ty_default" in pose Io.1.1.1.2 as I_ltd ; compute in I_ltd ;
   let I_ltd0 := fresh I "_list_ty_default0" in pose Io.1.1.1.1.2 as I_ltd0 ; compute in I_ltd0 ;
   let I_la := fresh I "_list_args" in pose Io.1.1.1.1.1.2 as I_la ; compute in I_la ;
   let I_lal := fresh I "_list_args_len" in pose Io.1.1.1.1.1.1 as I_lal ; compute in I_lal ;
   clear Io.

(*   constr:(((((((list_args_len,list_args),list_ty_default0),list_ty_default),nbconstruct),list_ctors_reif),list_of_pars_rel)) *) 
 

(* Definition mkCase_eliminator_default_var (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) :=  *)

(* pour reprendre le calcul de get_eliminators_st_return, la fonction principale: *)
(* on calcule d'abord list_ty, list_types of each constructors 
   ensuite, calcule compliqué de list_args_len, où on compte le nombre d'arguments
      son type est list (list term * nat)
      mais la partie liste de types, tout ou presque semble ramener à tRel 0: c'est là qu'il y a le unlift
   ensuite, list_args, qui est la liste de listes où on ignore les nc
   ensuite ty_default0 le flattening 
   enfin ty_default qui le rev liftré incrémentalement
   Remarque: _list_ty est une list term et pas lis list term, et préfixe bien avec le binding des paramètres

   Reste à comprendre pourquoi les dB sont mis à zéro pour list_args_len et pourquoi c'est utile pour les proj
   *)
Goal False.


Abort.

(* 
Ltac get_eliminators_st_return I_rec na := 
let I_rec_term := eval compute in (I_rec.2) in
let opt := eval compute in (get_info_params_inductive I_rec_term I_rec.1) in 
match opt with 
| Some (?npars, ?ty_pars) =>
  let list_ty := eval compute in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval compute in (get_args_list_with_length list_ty npars) in 
  let list_args := eval compute in (split list_args_len).1 in 
  let list_ty_default0 := eval compute in (tr_flatten list_args) in
  let list_ty_default := eval compute in (lift_rec_rev list_ty_default0) in 
  let nbconstruct := eval compute in (Datatypes.length list_args) in
  let list_ctors_reif := eval compute in (get_list_ctors_tConstruct_applied I_rec_term nbconstruct npars) in 
  let total_args := eval compute in (total_arg_ctors list_args_len) 
  in
  let list_of_pars_rel := eval compute in ((get_list_of_rel_lifted npars (total_args + 1))) in
  let I_app := eval compute in (get_indu_app_to_params I_rec_term npars) in
  let I_lifted := eval compute in (lift (total_args) 0 I_app) in
        match I_rec_term with
        | tInd ?I_indu _ =>
                      let x := get_eliminators_aux_st nbconstruct na ty_pars I_app I_indu npars list_args_len total_args list_of_pars_rel list_ctors_reif total_args (@nil term) in 

                      let t := eval compute in (mkProd_rec ty_pars (mkProd_rec list_ty_default (tProd {| binder_name := nNamed "x"%string ; binder_relevance := Relevant |} 
    I_lifted (mkOr x)))) in
                      let u := metacoq_get_value (tmUnquote t) in 
                      let u' := eval hnf in (u.(my_projT2)) in let Helim := fresh in let _ := match goal with _ =>
let nb_intros := eval compute in (npars + total_args) in 
 assert (Helim : u') by (prove_by_destruct_varn nb_intros)
 end in Helim
        | _ => fail
| None => fail
end
end.
*)



Goal False. (* PAS ENCORE COMPRIS*)
Print cons_typ_reif.
split_info1 list "blut". clear -list_list_args.
split_info2 list "blut". clear.
split_info1 @nelist "blut". clear. (* clear -list_app nelist_app. *)
split_info1 @biclist "blut". clear  - biclist_app biclist_list_args. clear.
(** branch_default_var *)
let x := constr:( branch_default_var 
[tRel 0; tApp list_reif [tRel 1] ; tRel 8 ; tRel 12 ; tRel 15]
2 5 8)  (* ce qui compte, c'est l'égalité 2ème et 3ème . Ensuite, il y a len - 1er + 1*)
in pose x as kikoo ;
unfold branch_default_var in kikoo ; simpl in kikoo.
let x := constr:( branch_default_var 
[tRel 0; tApp list_reif [tRel 1] ; tRel 8 ; tRel 12 ; tRel 15]
2 5 8)  (* ce qui compte, c'est l'égalité 2ème et 3ème . Ensuite, il y a len - 1er + 1*)
in pose x as blut ;
unfold branch_default_var in blut ; simpl in blut.
clear.  (* DONE *)
let x := constr:( branch_default_var 
[tRel 0; tApp list_reif [tRel 1] ; tRel 8 ; tRel 12 ; tRel 15] 0 1 1) in pose x as iki ; unfold branch_default_var in iki ; simpl in iki.

let x :=  constr:(mkCase_eliminator_default_var list_indu 1 0 2 [ [tRel 1 ; tRel 3 ; tRel 12]; [tRel 2 ; tRel 5; list_reif] ; [nat_reif ; tRel 0 ; tRel 5] ; [nat_reif ; tRel 13 ; tRel 11] ; [nat_reif ; tRel 20 ; tRel 25] ] 
(tProd (mkNamed "a") (tRel 40) (tRel 42))) in pose x as blut ; unfold mkCase_eliminator_default_var in blut ; unfold branch_default_var in blut ; simpl in blut.



let x :=  constr:(mkCase_eliminator_default_var list_indu 1 0 3 [ [tRel 1]; [tRel 2 ; tRel 5; list_reif] ; [nat_reif ; tRel 0]]
(tProd (mkNamed "a") (tRel 40) (tRel 42))) in pose x as kik ; unfold mkCase_eliminator_default_var in kik ; unfold branch_default_var in blut ; simpl in kik.  

(* return_type est le 2ème arg de tCase: donc le type du pm commençant par tLam et pas un type de retour
* nbconstruct: rang du ctor: la fonction va agir sur l'élément de rang nbconstruct dans la liste de listes de termes
* nbproj : 
*)
Print mkCase_eliminator_default_var.
(* 
Definition mkCase_eliminator_default_var (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) := 
let fix aux (I : inductive) (npars: nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) (acc: list (nat × term)) (acc_nat : nat) :=
match ty_arg_constr with 
| [] => tCase (I, npars, Relevant) return_type (tRel 0) (List.rev acc)
| x :: xs => aux I npars nbproj nbconstruct xs return_type 
((acc_nat, branch_default_var x nbproj nbconstruct acc_nat)::acc) (acc_nat + 1)
end
in aux I npars nbproj nbconstruct ty_arg_constr return_type [] 0.
*)



get_eliminators_st list.
pose_quote_term (fun (A : Type) (x x0 : list A) =>
match x0 with
| [] => x
| _ :: x1 => x1
end ) pl1.
pose_quote_term (fun (A : Type) (x : A) (x0 : list A) =>
match x0 with
| [] => x
| x1 :: _ => x1
end ) pl0.
Abort.


(* let x:= mkCase_eliminator_default_var (list_indu ) *)


Goal False.
(* split_info1 list "ki".
split_info2 list "koo".  *)
let x :=  constr:(mkCase_eliminator_default_var list_indu 80 20 40
[[tRel 1] ; [tRel 3 ; tRel 8]] (tProd (mkNamed "x") (tApp nat_reif [tRel 4 ; tRel 5]) (tRel 12)))
in pose x as blut.
unfold mkCase_eliminator_default_var in blut. unfold rev in blut. simpl in blut.
clear blut.
 pose_quote_term
(fun (l : list nat) => match l with
| [] => 0
| x  :: l0 => x end
  ) kik.
  clear kik.
  pose_quote_term
  (fun (l : @biclist nat bool) => match l with
  | bicnil => 0
  | cons1 x l0 => x 
  | cons2 _ _ => 1 end 
    ) kooo.
clear.
pose_quote_term (fun (A : Type)  ( l : @nelist A)  => match l with
| sing a => a 
| necons  x l0 => x 
end
  ) kaaaa.

  (* tCase : (inductive × nat) × relevance ->
            term -> term -> list (nat × term) -> term *)
 (*      tLambda : aname -> term -> term -> term *)
            Abort.

Goal False.
get_eliminators_st list. 
get_eliminators_st nat.  

pose_quote_term (fun (A : Type) (x x0 : list A) => match x0 with
| [] => x
| _ :: x1 => x1
end ) pl1.
pose_quote_term (fun (A : Type) (x : A) (x0 : list A) => match x0 with
| [] => x
| x1 :: _ => x1
end ) pl0.
pose_quote_term (fun x x0 : nat => match x0 with
| 0 => x
| S x1 => x1
end ) pn0.
clear H H0.

split_info1 list "ki".
split_info2 list "koo".
Fail let list_tyd := constr:(tApp list_reif [tRel 1])  (* ty_default, pourrait aussi être list_reif [Rel 0] *) 
in
get_one_eliminator_return list [tRel 3]
(tApp list_reif [tRel 0])   (* I_app *)
list_tyd
list_indu 
1 
 1  (* nbproj *)
 1 (* nbconstruct *)
 list_list_args (* [tRel 0;  tApp list_reif [tRel 0]] *) (*list_args for :: *)
(lift 2 0 (mkLam list_app (lift0 1  list_tyd)))
0 2 .


Ltac get_one_eliminator_return I ty_pars I_app ty_default I_indu npars nbproj nbconstruct list_args return_ty nb_args_previous_construct total_args :=

(* let blut := fresh in get_info_quote list blut. 
let blut2 := fresh in get_info2_quote list blut.
clear. *)
split_info2 nat "blut". (* clear -list_list_args list_list_argskik list_list_args_len. *)
Abort.
(* 
constr:((((((((list_args_len),list_args),list_ty_default0),list_ty_default),nbconstruct),list_ctors_reif),list_of_pars_rel)) 
*)


(* 
Inductive my_type :=
  | A : my_type
  | B : my_type -> my_type
  | C : my_type -> my_type.

MetaCoq Quote Definition mt_reif := my_type.  
MetaCoq Quote Definition A_reif := A. 
MetaCoq Quote Definition B_reif := B.
MetaCoq Quote Definition C_reif := C.
*)



(********************************************)
(* Tests on utilities.v                     *)
(********************************************)

Goal False.
let x := constr:(list_types_of_each_constructor list_env_reif) in pose x as ltoeclist ; compute in ltoeclist.
Abort.

Print get_info_params_inductive.

(* d'après le code, get_info_params_inductive 
renvoie npars et ty_pars*)

Ltac get_info2 I_rec na :=
  let I_rec_term := eval cbv in (I_rec.2) in
  let opt := eval cbv in (get_info_params_inductive I_rec_term I_rec.1) in pose opt as na.


  Ltac get_info2_quote I na := 
   let I_rec := metacoq_get_value (tmQuoteRec I) in
   get_info2 I_rec  na.

Goal False.
Proof.
get_info2_quote list test_list.
Abort.




(********************************************)
(* Tests on eliminators.v                   *)
(********************************************)

(* meaning of the metavariables *)
(* nbproj : rank of a projection e.g. *)
(* exemple: cons est le 2ème constructeur de list 
 - pour elim_{1,0}, nbproj est 0, ty_default est nat et pour elim_{1,1}, c'est 1 et list nat 
- nb_construct 2 ou 1.
- total_arg c'est 2 ou 3 (compte-t-on les paramètres ?)
*)


(* _app : the inductive applied to its possible de Bruijn indices
* nat_app = nat_reif
* list_app = list_reif [Rel 0]
* nelist_app = nelist_reif [Rel0]
*)


(* _total_args or _tot_args is equal to the total number of parameters of the constructors:
   is equal to 1 for nat
   is equal to 2 for list, 
   is equal to 1 for nelist
*)

(* _lpars :
 nat_lpars = []
 list_lpars = [Rel 3]
 nelist_pars = [Rel 4]
*)

(* list_args := (split list_args_len).1 :
* nat_list_args = [ [] ; nat_reif ]
* list_list_args = [ [] ; [Rel 0 ; list_reif [Rel 0]]]
* nelist_list_args =  [ [Rel 0] ; [Rel 0 ; nelist_reif [Rel 0] ] ]
*)

(* list_ty 
* nat_list_ty = [nat_reif ; Prod _ nat_reif nat_reif]
* list_list_ty = [ tProd "A" Set_reif. list_reif [Rel 0] ;
   tProd "A" Set_reif. tProd _ (Rel 0). tProd _ (list_reif [Rel 1]). list_reif Rel 2  ]
* nelist_list_ty = [ tProd "A" Set_reif. tProd _ (Rel 0). nelist_reif [Rel 1] ; 
   tProd "A" Set_reif. tProd _ (Rel 0). tProd _ (nelist_reif [Rel 1]). nelist_reif Rel 2  ]
   *)

(* list_pars 
* nat_list_pars = []
* list_list_pars = [Set_reif]
* nelist_list_pars = [Set_reif].
*)

(* npars
nat_npars = 0
list_npars = 1
nelist_npars =
*)

Goal False.
split_info1 nat "nat". clear.
split_info1 list "list".  (* the second arg seems useless*)
clear. split_info1 @nelist  "nelist".
Abort.


Goal False.
split_info1 list "list". 
Print get_nbproj_nbargprevcons.
let res :=  (get_nbproj_nbargprevcons n I list_ty_pars list_app list_indu list_npars list_list_args list_tot_args list_lpars list_constructors_reif nb (@nil term)) in pose res as blut. Eval compute in blut.


Ltac get_nbproj_nbargprevcons n I ty_pars I_app I_indu npars list_args total_args lpars list_constructors_reif nb list_eq :=
match n with
Abort.


Ltac get_nbproj_nbargprevcons n I ty_pars I_app I_indu npars list_args total_args lpars list_constructors_reif nb list_eq :=


(**** eliminators.v ****)

Goal False.

Print nil_type_reif.
pose (tProd
  (mkNamed "A")
  (tSort
     (Universe.of_levels
        (inr
           (Level.Level
              "Sniper.aux_fun_tests.465"))))
  (tApp
    list_reif [tRel 0]))
as blut0.
pose (tProd
  (mkNamed "A")
  (tSort
     (Universe.of_levels
        (inr
           (Level.Level
              "Sniper.aux_fun_tests.387"))))
  (tProd
     {|
       binder_name := nAnon;
       binder_relevance := Relevant
     |} (tRel 0)
     (tProd
        {|
          binder_name := nAnon;
          binder_relevance := Relevant
        |}
        (tApp
           list_reif [tRel 1])
        (tApp list_reif [tRel 2])))) as blut1.
(* let list_info := fresh "list_info" in get_info_quote list list_info. *)
(* let '(list_indu, list_I_app, list_lpars, list_total_args, list_lists_args, list_list_ty, list_ty_pars, list_npars) := ????? *)



split_info1 list "list".

get_list_args_len_quote list list_lal.
get_ty_arg_constr list list_tarc.

pose ((tApp (* en mettant un idtac dans eliminators.v *)
   (tInd
      {|
        inductive_mind :=
          (MPfile
             ["Datatypes"; "Init";
             "Coq"], "list");
        inductive_ind := 0
      |} []) [tRel 0])) as list_ty_default.
(* on aussi tRel 0 qui doit correspondent à un autre ty_default *)

(* pour ty_default avec un idtac *)



pose (tLambda
   {|
     binder_name := nNamed "x";
     binder_relevance := Relevant
   |}
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 2])
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 3])) as rtyp1. 
pose 
(tLambda
   {|
     binder_name := nNamed "x";
     binder_relevance := Relevant
   |}
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 2]) 
   (tRel 3)) as rtyp0.


(* proj_one_constructor_default_var (i : term) (ty_default : term)
 (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) *) 
clear list_info.
let x := constr:(proj_one_constructor_default_var  (tApp list_reif [tRel 0]) 
 (tApp list_reif [tRel 0])  
list_indu 1 0 1 list_tarc rtyp1)
in pose x as y; compute in y.
Print tCase.
pose_unquote_term_hnf y projtruc.
Abort.
