From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mf.
Require Import rlzr_base rlzr_smbly rlzr_fnct.
Import Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section modest_sets.
Context Q (A: modest_set Q).

Definition id_modest_set_mixin S: modest_set_mixin.type (id_assembly S).
Proof. split; exact/F2MF_sing. Defined.

Definition id_modest_set S:= @modest_set.Pack S (id_assembly S) (id_modest_set_mixin S).

Lemma comp_ref_sing (D: modest_set A): (comp_ref D) \is_singlevalued.
Proof.
move => q a a' [d [qnd dna]] [d' [qnd' d'na]].
rewrite (ref_sing q d d') in dna => //.
by rewrite (ref_sing d' a a').
Qed.

Definition combine_modest_set_mixin (D: modest_set A):
	modest_set_mixin.type (@cmbn_smbly Q A D).
Proof. by split; exact/comp_ref_sing. Defined.

Canonical cmbn_msets (D'': modest_set A) :=
	modest_set.Pack (@combine_modest_set_mixin D'').

Context  Q' (A': modest_set Q').

Lemma prod_ref_sing: (prod_ref A A') \is_singlevalued.
Proof. apply /fprd_sing; split; apply ref_sing. Qed.

Definition prod_modest_set_mixin: modest_set_mixin.type (prod_assembly A A').
Proof. by split; exact/prod_ref_sing. Defined.

Canonical prod_modest_set := modest_set.Pack prod_modest_set_mixin.

Lemma sum_ref_sing: (sum_ref A A') \is_singlevalued.
Proof. exact/fsum_sing/ref_sing/ref_sing. Qed.

Definition sum_modest_set_mixin: modest_set_mixin.type (sum_assembly A A').
Proof. split; exact/sum_ref_sing. Defined.

Canonical sum_modest_set := modest_set.Pack sum_modest_set_mixin.

Lemma rlzr_spec (F: Q ->> Q') f:
	F \realizes f <-> ((ref A') o F) \tightens (f o (ref A)).
Proof.
split => [Frf | [dm val]].
	split => q [a' [[a [aaq faa']] subs]].
		have [[q' Fqq'] prp]:= Frf q a aaq (subs a aaq).
		have [d' [d'aq' fad']]:= prp q' Fqq'.
		exists d'; split => [ | r' Fqr']; first by exists q'.
		by have [e' [e'aq' fae']]:= prp r' Fqr'; exists e'.
	move => d' [[q' [Fqq' d'aq']]subs'].
	split; last 	by move => d daq; apply subs.
	have [_ prp]:= Frf q a aaq (subs a aaq).
	have [d'' [d''aq' fad'']]:= prp q' Fqq'.
	exists a; split => //.
	by rewrite (ref_sing q' d' d'').
move => q a aaq [a' faa'].
split => [ | q' Fqq'].
	have [ | d' [[q' [Fqq' d'aq']] subs]]:= dm q; last by exists q'.
	exists a'; split; first by exists a.
	move => d daq.
	by exists a'; rewrite (ref_sing q d a).
have qfd: q \from_dom (f o (ref A)).
	exists a'; split; first by exists a.
	move => d daq.
	by exists a'; rewrite (ref_sing q d a).
have [d' [[z' [Fqz' d'az']] subs]]:= dm q qfd.
have [e' e'aq']:= subs q' Fqq'.
have [ | [d [daq fdd']]subs']:= val q qfd e'; first by split; first by exists q'.
exists e'; rewrite (ref_sing q a d) => //; split => //.
Qed.
End modest_sets.

Section mf_realizer.
Context Q (A: modest_set Q) Q' (A': assembly Q').
Definition mf_rlzr := make_mf (fun F (f: A ->> A') => F \realizes f).

Lemma rlzr_sur: mf_rlzr \is_cototal.
Proof.
rewrite cotot_spec => f.
exists (make_mf (fun q Fq => forall a, a \is_answer_to q -> exists fa, fa \is_answer_to Fq /\ f a fa)).
move => q a qna [fa fafa]; split.
	have [Fq Fqnfa]:= get_name fa.
	exists Fq => a' qna'.
	exists fa; split => //.
	by rewrite (ref_sing q a' a).
move => q' /=Fqq'.
have [a' [q'na' faa']]:= Fqq' a qna.
by exists a'.
Qed.

Definition mf_rlzr_assembly_mixin : assembly_mixin.type (Q ->> Q') (A ->> A').
Proof. exists mf_rlzr; exact rlzr_sur. Defined.

Canonical rlzr_smbly := assembly.Pack mf_rlzr_assembly_mixin.
End mf_realizer.

Section realizer_functions.
Context Q (A: modest_set Q) Q' (A': modest_set Q').

Definition	ftrnsln (f: A -> A') := trnsln (F2MF f).
Notation "f \is_translation_function" := (ftrnsln f) (at level 2).

Lemma icf_rlzr F (f: A ->> A'):
	F \realizes f -> forall g, g \is_choice_for F -> (F2MF g) \realizes f.
Proof.
rewrite rlzr_spec.
move => rlzr G icf.
rewrite rlzr_spec.
apply/ tight_trans; first by apply rlzr.
exact/ tight_comp_r/icf_F2MF_tight.
Qed.

Definition mf_frlzr := make_mf (fun F (f: A -> A') => F \realizes (F2MF f)).

Lemma mf_frlzr_sur: mf_frlzr \is_cototal.
Proof.
rewrite cotot_spec => [f].
have [ | F [_ Frf]]//:= (rlzr_sur (F2MF f)).2.
by exists F.
Qed.

Definition mf_frlzr_assembly_mixin: assembly_mixin.type (Q ->> Q') (A -> A').
Proof. exists mf_frlzr; exact/mf_frlzr_sur. Defined.

Lemma mf_frlzr_sing: mf_frlzr \is_singlevalued.
Proof.
move => F f g /rlzr_F2MF Frf /rlzr_F2MF Frg.
apply functional_extensionality => a.
have [ | q [_ qna]]//:= (ref_sur a).2.
have [[Fq FqFq] prp]:= Frf q a qna.
specialize (prp Fq FqFq).
have [_ prp']:= Frg q a qna.
specialize (prp' Fq FqFq).
by rewrite (ref_sing Fq (f a) (g a)).
Qed.

Definition mf_frlzr_modest_set_mixin:
	modest_set_mixin.type (assembly.Pack mf_frlzr_assembly_mixin).
Proof. split; exact/mf_frlzr_sing. Defined.

Definition frlzr := make_mf (fun F (f: A -> A') => (F2MF F) \realizes (F2MF f)).

From mpf Require Import choice_mf.
Lemma frlzr_sur (q': Q'): frlzr \is_cototal.
Proof.
rewrite cotot_spec => [f].
have [ | F [_ Frf]]//:= (rlzr_sur (F2MF f)).2.
have [g gcF]:= exists_choice F q'.
by exists g; apply /icf_rlzr/gcF.
Qed.

Definition frlzr_assembly_mixin (q': Q'): assembly_mixin.type (Q -> Q') (A -> A').
Proof. exists frlzr; exact/(frlzr_sur q'). Defined.

Lemma frlzr_sing: mf_frlzr \is_singlevalued.
Proof. by move => F f g Frf Frg; exact/(mf_frlzr_sing Frf Frg). Qed.
End realizer_functions.
Notation "f '\is_transation'" := (trnsln f) (at level 2).