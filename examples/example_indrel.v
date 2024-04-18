From Sniper Require Import Sniper.
Require Import List.

Goal False.
inversion_principle @Add.
inversion_principle Exists.
inversion_principle Forall.
Abort.