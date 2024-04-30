From Ltac2 Require Import Ltac2 Init.

(** A filter is useful to block the application of a transformation
even if the transformation is triggered *)

Ltac2 Type rec filter := [
  | FConstr (constr list)
  | FConstrList (constr list list)
  | FPred (constr -> bool)
  | FPredList (constr list -> bool) 
  | FConj (filter, filter) 
  | FTrivial ].

Ltac2 Type exn ::= [ WrongArgNumber(string) ].

Ltac2 trivial_filter := FTrivial.

(** [l] is the list of arguments of the tactic (returned by the interpretation
of the trigger 
and f is the filter applied to them *)

Ltac2 rec pass_the_filter 
  (l : constr list)
  (f : filter) : bool :=
    match f with
      | FConstr lc =>
            match l with 
              | [] => true
              | x :: xs => if List.exist (Constr.equal x) lc then false else pass_the_filter xs f
            end
      | FPred p => if List.exist p l then false else true 
      | FConstrList lc => if List.exist (List.equal Constr.equal l) lc then false else true
      | FPredList p => if p l then false else true
      | FConj f1 f2 => Bool.and (pass_the_filter l f1) (pass_the_filter l f2)
      | FTrivial => true
    end.