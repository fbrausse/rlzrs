From mathcomp Require Import all_ssreflect.
Require Import ntrvw_base ntrvw_rlzr ntrvw_fnct.
Import Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section morphisms.
Context Q Q' (A: interview Q) (A': interview Q').

Definition mf_morphism (f: A ->> A') := exists F, F \realizes f.

Definition mf_morphisms := {f: A ->> A' | mf_morphism f}.

Definition mf_mrph_conv:= make_mf (fun F (f: mf_morphisms) => F \realizes (projT1 f)).

Lemma mf_mrph_conv_sur : mf_mrph_conv \is_cototal.
Proof. by move => [f [F rlzr]]; exists F. Qed.

Definition morphisms_interview_mixin: interview_mixin.type (Q ->> Q') mf_morphisms.
Proof. exists mf_mrph_conv; exact/mf_mrph_conv_sur. Defined.

Canonical morphisms_interview:= interview.Pack morphisms_interview_mixin.

Lemma dict_mrph f: (conversation A) \is_singlevalued -> f \is_singlevalued -> mf_morphism f.
Proof.
move => dict sing.
exists (make_mf (fun q Fq => forall a fa, a \is_response_to q -> f a fa -> fa \is_response_to Fq)).
apply/split_rlzr => q a arq [fa fafa].
	have [Fq farFq]:= get_question fa; exists Fq => /= a' fa' a'rq fa'fa'.
	by rewrite (dict q a' a) in fa'fa' => //; rewrite (sing a fa' fa).
by move => Fq /= FqFq; exists fa; split => //; apply/FqFq/fafa.
Qed.

Definition morphism f := mf_morphism (F2MF f).

Definition morphisms := {f | morphism f}.

Definition mrph_conv:= make_mf (fun F (f: morphisms) => F \realizes (F2MF (projT1 f))).

Lemma mrph_conv_sur: mrph_conv \is_cototal.
Proof. by move => [f [F rlzr]]; exists F. Qed.

Definition mrph_interview_mixin: interview_mixin.type (Q ->> Q') morphisms.
Proof. exists mrph_conv; exact mrph_conv_sur. Defined.
End morphisms.

