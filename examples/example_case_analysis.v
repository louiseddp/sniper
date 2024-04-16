From Sniper Require Import case_analysis.

Section example.

Inductive enum : Set :=
| c1 : enum
| c2 : enum
| c3 : enum
| c4 : enum
| c5 : enum.

Goal False.
get_projs_st enum.
get_projs_st list.
get_projs_st nat.
get_projs_st bool.
Abort.

End example.