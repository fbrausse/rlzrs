From mathcomp Require Import all_ssreflect.
Require Import ntrvw_base ntrvw_rlzr ntrvw_fnct.
Import Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module dictionary_mixin.
Structure type Q (A: interview.type Q):= Pack {
answer_unique: (conversation A) \is_singlevalued;
}.
End dictionary_mixin.

Module dictionary.
Structure type Q:= Pack {
A :> interview Q;
mixin: dictionary_mixin.type A;
}.
End dictionary.
Coercion dictionary.A: dictionary.type >-> interview.type.
Coercion	dictionary.mixin: dictionary.type >-> dictionary_mixin.type.
Notation dictionary := (dictionary.type).
Canonical make_modest_set Q (D: interview Q) (mixin: dictionary_mixin.type D) :=
	dictionary.Pack mixin.
Definition dictates Q (D: dictionary.type Q) :=
	interview_mixin.conversation (interview.mixin D).
Notation "a '\is_answer_to' q 'in' D" := (dictates D q a) (at level 2).
Notation "a \is_answer_to q" := (a \is_answer_to  q in _) (at level 2).
Definition answer_unique Q (A: dictionary Q) :=
	(@dictionary_mixin.answer_unique Q A A).
Arguments answer_unique {Q} {A}.

Section dictionaries.
Context Q (A: dictionary Q).

Definition id_dictionary_mixin S: dictionary_mixin.type (id_interview S).
Proof. split; exact/F2MF_sing. Defined.

Definition id_dictionary S:= @dictionary.Pack S (id_interview S) (id_dictionary_mixin S).

Lemma comp_conv_sing (D: dictionary A): (comp_conv D) \is_singlevalued.
Proof. exact/rcmp_sing/answer_unique/answer_unique. Qed.

Definition combine_dictionaries_mixin (D: dictionary A):
	dictionary_mixin.type (@cmbn_ntrvw Q A D).
Proof. by split; exact/comp_conv_sing. Defined.

Canonical cmbn_dict (D'': dictionary A) :=
	dictionary.Pack (@combine_dictionaries_mixin D'').

Context  Q' (A': dictionary Q').

Lemma prod_conv_sing: (prod_conv A A') \is_singlevalued.
Proof. exact/fprd_sing/answer_unique/answer_unique. Qed.

Definition prod_dictionary_mixin: dictionary_mixin.type (prod_interview A A').
Proof. by split; exact/prod_conv_sing. Defined.

Canonical prod_dictionary := dictionary.Pack prod_dictionary_mixin.

Lemma sum_conv_sing: (sum_conv A A') \is_singlevalued.
Proof. exact/fsum_sing/answer_unique/answer_unique. Qed.

Definition sum_dictionary_mixin: dictionary_mixin.type (sum_interview A A').
Proof. split; exact/sum_conv_sing. Defined.

Canonical dictionary_set := dictionary.Pack sum_dictionary_mixin.

Lemma rlzr_spec (F: Q ->> Q') f:
	F \realizes f <-> ((conversation A') o F) \tightens (f o (conversation A)).
Proof.
split => [Frf | tight].
	apply split_tight => q [a' [[a [aaq faa']] subs]].
		have [[q' Fqq'] prp]:= Frf q a aaq (subs a aaq).
		have [d' [d'aq' fad']]:= prp q' Fqq'.
		exists d'; split => [ | r' Fqr']; first by exists q'.
		by have [e' [e'aq' fae']]:= prp r' Fqr'; exists e'.
	move => d' [[q' [Fqq' d'aq']] subs'].
	split => [ | d daq]; last exact/subs.
	have [d'' [d''aq' fad'']]:= rlzr_val Frf aaq (subs a aaq) Fqq'.
	by exists a; split => //; rewrite (answer_unique q' d' d'').
move => q a aaq [a' faa'].
have qfd: q \from dom (f o (conversation A)).
	exists a'; split => [ | d daq]; first by exists a.
	by exists a'; rewrite (answer_unique q d a).
split => [ | q' Fqq'].
	by have [ | d' [[q' [Fqq' d'aq']] subs]]:= (tight_dom tight) q; last by exists q'.
have [d' [[z' [Fqz' d'az']] subs]]:= (tight_dom tight) q qfd; have [e' e'aq']:= subs q' Fqq'.
have [ | [d [daq fdd']] subs']:= (tight_val tight qfd) e'; first by split; first by exists q'.
by exists e'; rewrite (answer_unique q a d); first split.
Qed.
End dictionaries.

Section mf_realizer.
Context Q (A: dictionary Q) Q' (A': interview Q').

Lemma rlzr_F2MF_eq F (f g: A' -> A):
	F \realizes (F2MF f) -> F \realizes (F2MF g) -> f =1 g.
Proof.
move => rlzr rlzr' a.
have [q arq]:= get_question a.
have [ | Fq FqFq]:= rlzr_dom rlzr arq; first exact/F2MF_dom.
have [ | fa [farFq ->]]:= rlzr_val rlzr arq _ FqFq; first exact/F2MF_dom.
have [ | ga [garFq ->]]:= rlzr_val rlzr' arq _ FqFq; first exact/F2MF_dom.
by rewrite (answer_unique Fq fa ga).
Qed.

Definition mf_rlzr := make_mf (fun F (f: A ->> A') => F \realizes f).

Lemma rlzr_sur: mf_rlzr \is_cototal.
Proof.
move => f.
exists (make_mf (fun q Fq => forall a, a \is_response_to q -> exists fa, fa \is_response_to Fq /\ f a fa)).
move => q a qna [fa fafa]; split => [ | Fq FqFq]; last by have [a' []]:= FqFq a qna; exists a'.
have [Fq Fqnfa]:= get_question fa; exists Fq => a' qna'.
by exists fa; split => //; rewrite (answer_unique q a' a).
Qed.

Definition mf_rlzr_interview_mixin : interview_mixin.type (Q ->> Q') (A ->> A').
Proof. exists mf_rlzr; exact rlzr_sur. Defined.

Canonical rlzr_ntrvw := interview.Pack mf_rlzr_interview_mixin.
End mf_realizer.

Section realizer_functions.
Context Q (A: dictionary Q) Q' (A': dictionary Q').

Definition	ftrnsln (f: A -> A') := trnsln (F2MF f).
Notation "f \is_translation_function" := (ftrnsln f) (at level 2).

Definition mf_frlzr := make_mf (fun F (f: A -> A') => F \realizes (F2MF f)).

Lemma mf_frlzr_sur: mf_frlzr \is_cototal.
Proof. by move => f; have [F Frf]//:= rlzr_sur (F2MF f); exists F. Qed.

Definition mf_frlzr_interview_mixin: interview_mixin.type (Q ->> Q') (A -> A').
Proof. exists mf_frlzr; exact/mf_frlzr_sur. Defined.

Lemma mf_frlzr_sing: mf_frlzr \is_singlevalued.
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

Definition mf_frlzr_dictionary_mixin:
	dictionary_mixin.type (interview.Pack mf_frlzr_interview_mixin).
Proof. split; exact/mf_frlzr_sing. Defined.

Definition frlzr := make_mf (fun F (f: A -> A') => (F2MF F) \realizes (F2MF f)).

From mpf Require Import choice_mf.
Lemma frlzr_sur (q': Q'): frlzr \is_cototal.
Proof.
move => f.
have [F Frf]//:= rlzr_sur (F2MF f).
have [g gcF]:= exists_choice F q'.
by exists g; apply /icf_rlzr/gcF.
Qed.

Definition frlzr_interview_mixin (q': Q'): interview_mixin.type (Q -> Q') (A -> A').
Proof. exists frlzr; exact/(frlzr_sur q'). Defined.

Lemma frlzr_sing: mf_frlzr \is_singlevalued.
Proof. by move => F f g Frf Frg; exact/(mf_frlzr_sing Frf Frg). Qed.
End realizer_functions.
Notation "f '\is_transation'" := (trnsln f) (at level 2).