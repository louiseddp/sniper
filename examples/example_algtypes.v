From Sniper Require Import interpretation_algebraic_types.

Section example.

Inductive enum : Set :=
| c1 : enum
| c2 : enum
| c3 : enum
| c4 : enum
| c5 : enum.

Goal False.
interp_alg_types list.
interp_alg_types nat.
interp_alg_types enum.
Abort.

End example.