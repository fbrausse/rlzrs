From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mf.
Require Import cdic_base ProofIrrelevance.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section interviews.
Lemma id_sur S: (@mf_id S) \is_cototal.
Proof. by rewrite cotot_spec => c; exists c. Qed.

Definition id_interview_mixin S: interview_mixin.type S S.
Proof. exists mf_id; exact/id_sur. Defined.

Definition id_interview S:= interview.Pack (id_interview_mixin S).

Definition sub_conv Q (P: mf_subset.type Q):=
	make_mf (fun (q: Q) (a: {a: Q | P a}) => q = projT1 a).

Lemma sub_conv_sur A P : (@sub_conv A P) \is_cototal.
Proof. by rewrite cotot_spec => [[a Pa]]; exists a. Qed.

Definition sub_interview_mixin A (P: mf_subset.type A): interview_mixin.type A {x: A | P x}.
Proof. exists (sub_conv P); exact/sub_conv_sur. Defined.

Canonical sub_interview A (P: mf_subset.type A):= interview.Pack (sub_interview_mixin P).

Context Q (A : interview Q).

Definition comp_conv (D: interview A):= (conversation D) o_R (conversation A).

Lemma comp_conv_sur (D: interview A): (comp_conv D) \is_cototal.
Proof.
rewrite cotot_spec => d''.
have [d dnd'']:= get_question d''.
have [q qnd]:= get_question d.
by exists q; exists d.
Qed.

Definition combine_interview_mixin (D: interview A): interview_mixin.type Q D.
Proof. exists (comp_conv D); exact/comp_conv_sur. Defined.

Canonical cmbn_ntrvw (D: interview A) := interview.Pack (combine_interview_mixin D).

Context Q' (A': interview Q').
Definition prod_conv := (conversation A) ** (conversation A').

Lemma prod_conv_sur: prod_conv \is_cototal.
Proof. by apply/fprd_cotot/only_respond/only_respond. Qed.

Definition prod_interview_mixin : interview_mixin.type (Q * Q') (A * A').
Proof. by exists prod_conv; exact/prod_conv_sur. Defined.

Canonical prod_interview := interview.Pack prod_interview_mixin.

Definition sum_conv:= (conversation A) +s+ (conversation A').

Lemma sum_conv_sur: sum_conv \is_cototal.
Proof. rewrite cotot_spec => [[a | b]] /=.
	by have [c cna]:= get_question a; exists (inl c).
by have [c cnab]:= get_question b; exists (inr c).
Qed.

Definition sum_interview_mixin: interview_mixin.type (Q + Q') (A + A').
Proof. by exists sum_conv; exact /sum_conv_sur. Defined.

Canonical sum_interview := interview.Pack sum_interview_mixin.
End interviews.