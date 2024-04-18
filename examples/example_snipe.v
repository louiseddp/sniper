From Sniper Require Import Sniper.

Section Generic.

  Goal forall (A: Type) (HA : CompDec A) (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof.
    snipe.
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