From Sniper Require Import case_analysis_existentials.

Section example.

Inductive enum : Set :=
| c1 : enum
| c2 : enum
| c3 : enum
| c4 : enum
| c5 : enum.

Goal False.
gen_statement_existentials enum H.
gen_statement_existentials list H1.
gen_statement_existentials nat H2.
gen_statement_existentials bool H3.
Abort.

End example.

