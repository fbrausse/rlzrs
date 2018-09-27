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
Proof. split; exact/F2MF_sing. Qed.

Definition id_modest_set S:= modest_set.Pack (id_modest_set_mixin S).

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

Section realizer_functions.
Context Q (A: modest_set Q) Q' (A': modest_set Q').

Lemma cmbn_mset_rlzr (D: modest_set A) (D': modest_set A') (F: Q ->> Q') G f:
	F \realizes G -> G \realizes (f: D ->> D') -> F \realizes (f: cmbn_msets D ->> cmbn_msets D').
Proof. exact/cmbn_smbly_rlzr. Qed.

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

Lemma tight_rlzr G F (f: A ->> A'):
	G \tightens F -> F \realizes f -> G \realizes f.
Proof.
by rewrite !rlzr_spec => GtF Frf; apply/ tight_trans; [apply Frf | apply/tight_comp_r/ GtF].
Qed.

Definition frlzr := make_mf (fun F (f: A -> A') => F \realizes (F2MF f)).

Lemma frlzr_sing: frlzr \is_singlevalued.
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

Lemma frlzr_cotot (someq': Q'): frlzr \is_cototal.
Proof.
move => f.
pose F := make_mf (fun q Fq => forall a, (ref A) q a -> (ref A') Fq (f a)).
split => // _; exists F; split => //.
rewrite /frlzr /= rlzr_F2MF => q a qaa.
split => [ | Fq FqFq]; last by apply FqFq.
have [  | Fq [_ Fqnfa]] //:= (ref_sur (f a)).2.
by exists Fq => a' qaa'; rewrite (ref_sing q a' a).
Qed.

Lemma frlzr_sur (someq': Q'): frlzr \is_cototal.
Proof. exact: frlzr_cotot. Qed.

Lemma frlzr_sur_par_fun (someq': Q'): frlzr \is_surjective_partial_function.
Proof. split; [exact: frlzr_sing | exact: frlzr_sur]. Qed.

End realizer_functions.
Notation "f '\is_realized_by' F" := (rlzr F f) (at level 2).
Notation "F '\realizes' f" := (rlzr F f) (at level 2).
Notation "f '\is_transation'" := (trnsln f) (at level 2).