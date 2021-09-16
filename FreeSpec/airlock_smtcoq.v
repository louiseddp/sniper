Add Rec LoadPath "/home/louise/github.com/louiseddp/sniper" as Sniper.
Require Import Sniper.
From Coq Require Import Arith.
Add Rec LoadPath "/home/louise/github.com/lthms/FreeSpec/master/_build/default/theories/Core" as FreeSpec.Core.
From FreeSpec.Core Require Import Core CoreFacts.
Require Import List.

Section airlock1.

Definition interface := Type -> Type.
Variable ix : interface.
Variable A B : Type.
Variable MayProvide
     : interface -> interface -> Type.
Variable Provide : forall ix i : interface, MayProvide ix i -> Type.
Definition Ω := (bool * bool)%type.
Inductive door : Set :=  left : door | right : door.
Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Print DOORS_ind.

MetaCoq Quote Recursively Definition DOORS_ind_reif := DOORS_ind.


Print DOORS_ind_reif.

MetaCoq Quote Recursively Definition DOORS_reif := DOORS.


Inductive foo : interface := bar1 : foo A | bar2 : foo B.
Definition sel : door -> Ω -> bool := fun d : door => match d with
                      | left => fst
                      | right => snd
                      end
.
Definition co := fun d : door => match d with
                     | left => right
                     | right => left
                     end.
Inductive doors_o_caller : Ω -> forall a : Type, DOORS a -> Prop :=
    req_is_open : forall (d : door) (ω : Ω), doors_o_caller ω bool (IsOpen d)
  | req_toggle : forall (d : door) (ω : Ω),
                 (sel d ω = false -> sel (co d) ω = false) -> doors_o_caller ω unit (Toggle d).

Inductive doors_o_callee : Ω -> forall a : Type, DOORS a -> a -> Prop :=
    doors_o_callee_is_open : forall (d : door) (ω : Ω) (x : bool),
                             sel d ω = x -> doors_o_callee ω bool (IsOpen d) x
  | doors_o_callee_toggle : forall (d : door) (ω : Ω) (x : unit), doors_o_callee ω unit (Toggle d) x.

Definition doors_o_callee2 :  Ω -> forall (a : Type) (D :  DOORS a), (match D with 
| IsOpen _ =>  bool 
| Toggle _ => unit
end) -> bool :=
fun ω a D => match D with
| IsOpen d => fun x => Bool.eqb (sel d ω) x
| Toggle d => fun x => true
end.

Definition doors_o_caller2 : Ω -> forall (a : Type) (D : DOORS a), bool := 
fun ω a D => match D with
| IsOpen _ => true
| Toggle d => implb (negb (sel d ω)) (negb (sel (co d) ω))
end.


Variable H : MayProvide ix DOORS.
Variable H0 : Provide ix DOORS H.
Variable ω : Ω.
Variable d : door.



Goal doors_o_caller2 ω bool (IsOpen d).
Proof. 
snipe. admit. admit. admit. admit. Abort.


(* Variable helper : (sel d ω) = true. *)


Variable o_caller : doors_o_caller2 ω bool (IsOpen d).
Variable x : bool.
Variable eq_cond : x = true.
Variable o_caller0 : doors_o_callee2 ω bool (IsOpen d) x. 
Goal doors_o_caller2 ω unit (Toggle d).
Proof. scope. Fail verit.
rewrite H12 in o_caller0. unfold is_true in o_caller0. rewrite Bool.eqb_true_iff in o_caller0.
subst.
rewrite o_caller0. 
 simpl. constructor. 
Qed.

Print is_true. 


Definition tog (d : door) (ω : Ω) : Ω :=
  match d with
  | left => (negb (fst ω), snd ω)
  | right => (fst ω, negb (snd ω))
  end.

End airlock1.

Section airlock2.

Definition is_open `{Provide ix DOORS} (d : door) : impure ix bool :=
  request (IsOpen d).

Definition toggle `{Provide ix DOORS} (d : door) : impure ix unit :=
  request (Toggle d).

Definition open_door `{Provide ix DOORS} (d : door) : impure ix unit :=
  let* open := is_open d in
  when (negb open) (toggle d).

Definition close_door `{Provide ix DOORS} (d : door) : impure ix unit :=
  let* open := is_open d in
  when open (toggle d).

Definition step (ω : Ω) (a : Type) (e : DOORS a) (x : a) :=
  match e with
  | Toggle d => tog d ω
  | _ => ω
  end.

Definition doors_contract : contract DOORS Ω :=
  make_contract step doors_o_caller doors_o_callee.

Variable ix : interface.
Variable H : MayProvide ix DOORS.
Variable H0 : Provide ix DOORS. 
Variable ω : Ω.
Variable d : door.
Variable safe : sel (co d) ω = false.

Print MayProvide.

Goal doors_o_caller2 ω bool (IsOpen d).
Proof.
scope. (* TODO verit. *) 

constructor.
Qed.

Variable o_caller : doors_o_caller2 ω bool (IsOpen d).
Variable x : bool.
Variable o_caller0 : doors_o_callee2 ω bool (IsOpen d) x.
Variable equ_cond : x = false.



Goal doors_o_caller2 ω unit (Toggle d).
Proof. scope. rewrite H17 in o_caller0. unfold is_true in o_caller0. rewrite Bool.eqb_true_iff in o_caller0.
subst. 
rewrite equ_cond. rewrite safe. constructor. Qed.

End airlock2.



Inductive CONTROLLER : interface :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick `{Provide ix CONTROLLER} : impure ix unit :=
  request Tick.

Definition request_open `{Provide ix CONTROLLER} (d : door) : impure ix unit :=
  request (RequestOpen d).


#[local] Opaque close_door.
#[local] Opaque open_door.
#[local] Opaque Nat.ltb.

Definition controller `{Provide ix DOORS, Provide ix (STORE nat)}
  : component CONTROLLER ix :=
  fun _ op =>
    match op with
    | Tick =>
      let* cpt := get in
      when (15 <? cpt) begin
        close_door left;;
        close_door right;;
        put 0
      end
    | RequestOpen d =>
        close_door (co d);;
        open_door d;;
        put 0
    end.

Lemma controller_correct `{StrictProvide2 ix DOORS (STORE nat)}
  : correct_component controller
                      (no_contract CONTROLLER)
                      doors_contract
                      (fun _ ω => sel left ω = false \/ sel right ω = false).

Proof.
  intros ωc ωd pred a e req.
  assert (hpre : pre (to_hoare doors_contract (controller a e)) ωd)
    by (destruct e; prove impure with airlock).
  split; auto.
  intros x ωj' run.
  cbn.
  split.
  + auto with freespec.
  + apply respectful_run_inv in run; auto.
Qed.

End airlock3. 








