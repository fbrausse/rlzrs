Require Import ntrvw_base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section canonical_interviews.
Canonical mf_interview S T := fun_interview (@F2MF S T).

Canonical sub_interview A (P: mf_subset.type A):= fun_interview (@projT1 A P).

Context Q (A : interview Q).

Canonical cmbn_ntrvw (D: interview A) := interview.Pack (combine_interview_mixin D).

Context Q' (A': interview Q').

Canonical canonical_prod_interview := prod_interview.

Canonical canonical_sum_interview := sum_interview.
End canonical_interviews.