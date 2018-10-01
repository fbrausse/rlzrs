From mathcomp Require Export all_ssreflect.
From mpf Require Export all_mf.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module interview_mixin.
Structure type questions answers := Pack {
conversation: questions ->> answers;
only_respond : conversation \is_cototal;
}.
End interview_mixin.

Module interview.
Structure type (questions: Type):= Pack {
answers:> Type;
mixin: interview_mixin.type questions answers;
}.
End interview.
Coercion interview.answers: interview.type >-> Sortclass.
Coercion interview.mixin : interview.type >-> interview_mixin.type.
Definition conversation Q (C: interview.type Q) :=
	interview_mixin.conversation (interview.mixin C).
Notation "a '\is_response_to' q 'in' C" := (conversation C q a) (at level 2).
Notation "a \is_response_to q" := (a \is_response_to  q in _) (at level 2).
Definition only_respond Q (A: interview.type Q) := (interview_mixin.only_respond A).
Arguments only_respond {Q} {A}.
Notation get_question a := ((cotot_spec _).1 only_respond a).
Notation interview := interview.type.

Section interviews.
Lemma id_sur S: (@mf_id S) \is_cototal.
Proof. by rewrite cotot_spec => c; exists c. Qed.

Definition id_interview_mixin S: interview_mixin.type S S.
Proof. exists mf_id; exact/id_sur. Defined.

Definition id_interview S:= interview.Pack (id_interview_mixin S).

Definition fun_interview_mixin Q A (f: A -> Q): interview_mixin.type Q A.
Proof. exists (F2MF f\^-1); exact /cotot_tot_inv/F2MF_tot. Defined.

Definition fun_interview Q A (f: A -> Q):= interview.Pack (fun_interview_mixin f).

Canonical mf_interview S T := fun_interview (@F2MF S T).

Canonical sub_interview A (P: mf_subset.type A):= fun_interview (@projT1 A P).

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