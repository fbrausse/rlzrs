From mathcomp Require Import ssreflect ssrfun.
Require Import all_mf choice_mf ntrvw dict.
Import Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section mf_rlzr_f.
Context Q (A: interview Q) Q' (A': dictionary Q').

Definition mf_rlzr_f := make_mf (fun F (f: A -> A') => F \realizes (F2MF f)).

Lemma mf_rlzr_f_sing: mf_rlzr_f \is_singlevalued.
Proof.
move => F f g /rlzr_F2MF Frf /rlzr_F2MF Frg.
apply functional_extensionality => a.
have [q qna]:= get_question a.
have [[Fq FqFq] prp]:= Frf q a qna.
specialize (prp Fq FqFq).
have [_ prp']:= Frg q a qna.
specialize (prp' Fq FqFq).
by rewrite (answer_unique Fq (f a) (g a)).
Qed.
End mf_rlzr_f.

Section realizer_functions.
Context Q (A: dictionary Q) Q' (A': dictionary Q').

Lemma mf_rlzr_f_interview_mixin: interview_mixin.type (Q ->> Q') (A -> A').
Proof. exists (@mf_rlzr_f Q A Q' A') => f; exact/rlzr_sur. Defined.

Definition mf_rlzr_f_dictionary_mixin:
	dictionary_mixin.type (interview.Pack mf_rlzr_f_interview_mixin).
Proof. split; exact/mf_rlzr_f_sing. Defined.

Definition frlzr := make_mf (fun F (f: A -> A') => (F2MF F) \realizes (F2MF f)).

Context (q': Q').

Lemma frlzr_sur: frlzr \is_cototal.
Proof.
move => f.
have [F Frf]//:= rlzr_sur (F2MF f).
have [g gcF]:= exists_choice F q'.
by exists g; apply /icf_rlzr/gcF.
Qed.

Definition frlzr_interview_mixin: interview_mixin.type (Q -> Q') (A -> A').
Proof. by exists frlzr; apply/frlzr_sur. Defined.

Canonical frlzrs:= interview.Pack frlzr_interview_mixin.

Lemma frlzr_sing: frlzr \is_singlevalued.
Proof. by move => F f g Frf Frg; exact/(mf_rlzr_f_sing Frf Frg). Qed.

Definition frlzrs_dictionary_mixin: dictionary_mixin.type frlzrs.
Proof. split; exact/frlzr_sing. Defined.

Canonical frlzr_dictionary:= dictionary.Pack frlzrs_dictionary_mixin.

Lemma exte_tot S T: (@mf_exte S T) \is_total.
Proof. by move => f; exists f => /= s t. Qed.

Lemma tight_rlzr: (@mf_tight Q Q') \realizes (@mf_tight A A').
Proof.
move => F f fcF _; split => [ | G tight]; first by exists F.
by exists f; split; first exact/tight_rlzr/tight.
Qed.
End realizer_functions.