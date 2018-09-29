From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mf.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module assembly_mixin.
Structure type Q A := Pack {
refinement: Q ->> A;
refinement_valid : refinement \is_cototal;
}.
End assembly_mixin.

Module assembly.
Structure type (questions: Type):= Pack {
answers:> Type;
mixin: assembly_mixin.type questions answers;
}.
End assembly.
Coercion assembly.answers: assembly.type >-> Sortclass.
Coercion assembly.mixin : assembly.type >-> assembly_mixin.type.
Notation answers := assembly.answers.
Definition ref questions (C: assembly.type questions) :=
	assembly_mixin.refinement (assembly.mixin C).
Notation assembly := assembly.type.
Notation "a \is_answer_to q" := (ref _ q a) (at level 2).
Definition ref_sur questions (D: assembly.type questions) := (assembly_mixin.refinement_valid D).
Arguments ref_sur {questions} {D}.
Notation get_name x := ((cotot_spec _).1 ref_sur x).

Module modest_set_mixin.
Structure type Q (A: assembly.type Q):= Pack {
refinement_singlevalued : (ref A) \is_singlevalued;
}.
End modest_set_mixin.

Module modest_set.
Structure type Q:= Pack {
A :> assembly Q;
mixin: modest_set_mixin.type A;
}.
End modest_set.
Coercion modest_set.A: modest_set.type >-> assembly.
Coercion modest_set.mixin: modest_set.type >-> modest_set_mixin.type.
Notation modest_set := (modest_set.type).
Canonical make_modest_set Q (D: assembly Q) (mixin: modest_set_mixin.type D) :=
	modest_set.Pack mixin.
Definition ref_sing Q (A: modest_set Q) :=
	(@modest_set_mixin.refinement_singlevalued Q A A).
Arguments ref_sing {Q} {A}.

Section realizer.
Context Q (D: assembly Q) Q' (D': assembly Q').

Definition rlzr (F: Q ->> Q') (f: D ->> D') :=
		(forall q a, a \is_answer_to q -> a \from_dom f -> q \from_dom F /\
		forall Fq, F q Fq -> exists fa, fa \is_answer_to Fq /\ f a fa).
Notation "F '\realizes' f" := (rlzr F f) (at level 2).

Global Instance rlzr_prpr:
	Proper (@equiv Q Q' ==> @equiv D D' ==> iff) (@rlzr).
Proof.
move => F G FeG f g feg.
split => rlzr q a aaq afd.
	have afd': a \from_dom f by rewrite feg.
	split => [ | q' Gqq']; first by have [[q' Fqq'] _]:= rlzr q a aaq afd'; exists q'; rewrite -FeG.
	have [_ prp]:= rlzr q a aaq afd'.
	have [ | a' [a'aq' faa']]:= prp q' _; first by rewrite FeG.
	by exists a'; rewrite -feg.
have afd': a \from_dom g by rewrite -feg.
split => [ | q' Gqq']; first by have [[q' Fqq'] _]:= rlzr q a aaq afd'; exists q'; rewrite FeG.
have [_ prp]:= rlzr q a aaq afd'.
have [ | a' [a'aq' faa']]:= prp q' _; first by rewrite -FeG.
by exists a'; rewrite feg.
Qed.

Definition trnsln (f: D ->> D') :=
	exists F,  F \realizes f.
Notation "f \is_translation" := (trnsln f) (at level 2).

Global Instance trnsln_prpr: Proper (@equiv D D' ==> iff) (@trnsln).
Proof.
move => f g eq; rewrite /trnsln.
split; move => [F].
	by exists F; rewrite -eq.
by exists F; rewrite eq.
Qed.
End realizer.
Notation "f '\is_realized_by' F" := (rlzr F f) (at level 2).
Notation "F '\realizes' f" := (rlzr F f) (at level 2).

Section realizers.
Context Q (A: assembly Q) Q' (A': assembly Q').

Lemma rlzr_comp Q'' (A'': assembly Q'') G F (f: A ->> A') (g: A' ->> answers A''):
	G \realizes g -> F \realizes f -> (G o F) \realizes (g o f).
Proof.
move => Grg Frf q a aaq [a'' [[a' [faa' ga'a'']]] subs].
split; last first.
	move => q'' [[q' [Fqq' Gq'q'']] subs'].
	have afd: a \from_dom f by exists a'.
	have [_ prp]:= Frf q a aaq afd.
	have [d' [d'aq' fad']]:= prp q' Fqq'.
	have [_ prp']:= Grg q' d' d'aq' (subs d' fad').
	have [d'' [d''aq'' gd'd'']]:= prp' q'' Gq'q''.
	exists d''; split => //.
	by split; first by exists d'.
have afd: a \from_dom f by exists a'.
have [[q' Fqq'] prp]:= Frf q a aaq afd.
have [d' [d'aq' fad']]:= prp q' Fqq'.
have [[q'' Gq'q''] prp']:= Grg q' d' d'aq' (subs d' fad').
have [d'' [d''aq'' gd'd'']]:= prp' q'' Gq'q''.
exists q''; split; first by exists q'.
move => p' Fqp'.
have [e' [e'ap' fae']]:= prp p' Fqp'.
have [[z' Gpz']]:= Grg p' e' e'ap' (subs e' fae').
by exists z'.
Qed.

Lemma rlzr_tight F f (g: A ->> A'): F \realizes f -> f \tightens g -> F \realizes g.
Proof.
move => Frf [dm val] q a qna afd.
have [qfd prp]:= Frf q a qna (dm a afd).
split => // q' Fqq'.
have [a' []]:= prp q' Fqq'.
by exists a'; split => //; apply val.
Qed.

Lemma tight_rlzr F G (f: A ->> A'): F \realizes f -> G \tightens F -> G \realizes f.
Proof.
move => Frf [dm val] q a qna afd.
have [qfd prp]:= Frf q a qna afd.
split => [ | q' Gqq']; first by apply dm.
by have:= prp q' (val q qfd q' Gqq').
Qed.

Lemma F2MF_rlzr F (f: A ->> A'):
	(F2MF F) \realizes f <->
	(forall q a, a \is_answer_to q -> a \from_dom f ->
		exists a', a' \is_answer_to (F q) /\ f a a').
Proof.
split => rlzr q a aaq [a' faa'].
have [ | [q' Fqq'] prp]:= rlzr q a aaq; first by exists a'.
by have [d' ]:= prp q' Fqq'; exists d'; rewrite Fqq'.
split => [ | q' eq]; first exact /F2MF_tot.
have [ | d' [d'aq' fad']]:= rlzr q a aaq; first by exists a'.
by exists d'; rewrite -eq.
Qed.

Lemma F2MF_rlzr_F2MF F (f: A -> A') :
	(F2MF F) \realizes (F2MF f) <-> forall q a, a \is_answer_to q -> (f a) \is_answer_to (F q).
Proof.
rewrite F2MF_rlzr.
split => ass phi x phinx; last by exists (f x); split => //; apply ass.
by have [ | fx [cd ->]]:= ass phi x phinx; first by apply F2MF_tot.
Qed.

Lemma rlzr_dom (f: A ->> A') F:
	F \realizes f -> forall q a, a \is_answer_to q -> a \from_dom f -> q \from_dom F.
Proof. by move => rlzr q a aaq afd; have [ex prp]:= rlzr q a aaq afd. Qed.

Lemma rlzr_val_sing (f: A ->> A') F: f \is_singlevalued -> F \realizes f ->
	forall q a q' a', a \is_answer_to q -> f a a' -> F q q' -> a' \is_answer_to q'.
Proof.
move => sing rlzr q a q' a' aaq faa' Fqq'.
have [ | _ prp]:= rlzr q a aaq; first by exists a'.
have [d' [d'aq' fad']]:= prp q' Fqq'.
by rewrite (sing a a' d').
Qed.

Lemma sing_rlzr (f: A ->> A') F: F \is_singlevalued -> f \is_singlevalued ->
	F \realizes f
	<->
	(forall q a, a \is_answer_to q -> a \from_dom f -> q \from_dom F)
		/\
	(forall q a q' a', a \is_answer_to q -> f a a' -> F q q' -> a' \is_answer_to q').
Proof.
move => Fsing fsing.
split; first by move => Frf; split; [exact: rlzr_dom | exact: rlzr_val_sing].
move => [prp cnd] q a aaq afd.
split => [ | q' Fqq']; first by apply /prp/afd/aaq.
move: afd => [a' faa'].
by exists a'; split => //; apply /cnd/Fqq'/faa'.
Qed.

Lemma rlzr_F2MF F (f: A -> A'):
	F \realizes (F2MF f)
	<->
	forall q a, a \is_answer_to q -> q \from_dom F
		/\
	forall q', F q q' -> (f a) \is_answer_to q'.
Proof.
split => [ | rlzr q a aaq _].
	split; first by apply/ rlzr_dom; [apply H | apply H0 | apply F2MF_tot ].
	by intros; apply/ rlzr_val_sing; [apply F2MF_sing | apply H | apply H0 | | ].
split => [ | q' Fqq']; first by have []:= rlzr q a aaq.
by exists (f a); split => //; apply (rlzr q a aaq).2.
Qed.
End realizers.
Notation "f '\is_realized_by' F" := (rlzr F f) (at level 2).
Notation "F '\realizes' f" := (rlzr F f) (at level 2).
Notation "f \is_translation" := (trnsln f) (at level 2).
