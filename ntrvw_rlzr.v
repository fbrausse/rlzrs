From mathcomp Require Import all_ssreflect.
Require Import ntrvw_base.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section realizer.
Context Q (A: interview Q) Q' (A': interview Q').

Definition rlzr (F: Q ->> Q') (f: A ->> A') :=
		(forall q a, a \is_response_to q -> a \from dom f -> q \from dom F /\
		forall Fq, F q Fq -> exists fa, fa \is_response_to Fq /\ f a fa).
Notation "F '\realizes' f" := (rlzr F f) (at level 2).

Lemma rlzr_dom (F: Q ->> Q') (f: A ->> A') q a: F \realizes f ->
	a \is_response_to q -> a \from dom f -> q \from dom F.
Proof. by move => Frf arq qfd; have []:= Frf q a arq qfd. Qed.

Lemma rlzr_val (F: Q ->> Q') (f: A ->> A') q a Fq: F \realizes f ->
	a \is_response_to q -> a \from dom f -> F q Fq -> exists fa, fa \is_response_to Fq /\ f a fa.
Proof. by move => Frf arq qfd FqFq; have [_ prp]:= Frf q a arq qfd; apply prp. Qed.

Lemma split_rlzr (F: Q ->> Q') (f: A ->> A'):
		(forall q a, a \is_response_to q -> a \from dom f -> q \from dom F) ->
		(forall q a Fq, a\is_response_to q -> a \from dom f -> F q Fq -> exists fa, fa \is_response_to Fq /\ f a fa) -> F \realizes f.
Proof.
by move => dm val q a arq afd; split => [ | Fq FqFq]; [apply/dm/afd | apply/val/FqFq].
Qed.

Global Instance rlzr_prpr:
	Proper (@equiv Q Q' ==> @equiv A A' ==> iff) (@rlzr).
Proof.
move => F G FeG f g feg.
split => rlzr q a aaq afd.
	have afd': a \from dom f by rewrite feg.
	split => [ | q' Gqq']; first by have [[q' Fqq'] _]:= rlzr q a aaq afd'; exists q'; rewrite -FeG.
	have [_ prp]:= rlzr q a aaq afd'.
	have [ | a' [a'aq' faa']]:= prp q' _; first by rewrite FeG.
	by exists a'; rewrite -feg.
have afd': a \from dom g by rewrite -feg.
split => [ | q' Gqq']; first by have [[q' Fqq'] _]:= rlzr q a aaq afd'; exists q'; rewrite FeG.
have [_ prp]:= rlzr q a aaq afd'.
have [ | a' [a'aq' faa']]:= prp q' _; first by rewrite -FeG.
by exists a'; rewrite feg.
Qed.

Definition trnsln (f: A ->> A') :=
	exists F,  F \realizes f.
Notation "f \is_translation" := (trnsln f) (at level 2).

Global Instance trnsln_prpr: Proper (@equiv A A' ==> iff) (@trnsln).
Proof.
by move => f g eq; rewrite /trnsln; split; move => [F]; exists F; [rewrite -eq | rewrite eq].
Qed.
End realizer.
Notation "f '\is_realized_by' F" := (rlzr F f) (at level 2).
Notation "F '\realizes' f" := (rlzr F f) (at level 2).

Section realizers.
Context Q (A: interview Q) Q' (A': interview Q').

Lemma rlzr_comp Q'' (A'': interview Q'') G F (f: A ->> A') (g: A' ->> A''):
	G \realizes g -> F \realizes f -> (G o F) \realizes (g o f).
Proof.
move => Grg Frf q a arq [gfa [[fa [fafa gfagfa]]] subs].
have afd: a \from dom f by exists fa.
split; last first.
	move => GFq [[Fq [FqFq GFqGFq]] subs'].
	have [d' [d'aq' fad']]:= rlzr_val Frf arq afd FqFq.
	have [d'' [d''aq'' gd'd'']]:= rlzr_val Grg d'aq' (subs d' fad') GFqGFq.
	by exists d''; split => //; split; first by exists d'.
have [[q' Fqq'] prp]:= Frf q a arq afd.
have [d' [d'aq' fad']]:= prp q' Fqq'.
have [[q'' Gq'q''] prp']:= Grg q' d' d'aq' (subs d' fad').
have [d'' [d''aq'' gd'd'']]:= prp' q'' Gq'q''.
exists q''; split => [ | p' Fqp']; first by exists q'.
have [e' [e'ap' fae']]:= prp p' Fqp'.
have [[z' Gpz']]:= Grg p' e' e'ap' (subs e' fae').
by exists z'.
Qed.

Lemma rlzr_tight F f (g: A ->> A'): F \realizes f -> f \tightens g -> F \realizes g.
Proof.
move => Frf tight q a arq afd.
have afd': a \from dom f by apply /tight_dom/afd.
split => [ | Fq FqFq]; first exact/rlzr_dom/afd'.
have [fa [farFq fafa]]:= rlzr_val Frf arq afd' FqFq.
by exists fa; split => //; apply/tight_val/fafa.
Qed.

Lemma tight_rlzr F G (f: A ->> A'): F \realizes f -> G \tightens F -> G \realizes f.
Proof.
move => Frf tight q a qna afd.
have [qfd prp]:= Frf q a qna afd.
split => [ | q' Gqq']; first by apply /tight_dom/qfd.
by have:= prp q' ((tight_val tight) qfd q' Gqq').
Qed.

Lemma icf_rlzr F (f: A ->> A'):
	F \realizes f -> forall g, g \is_choice_for F -> (F2MF g) \realizes f.
Proof. by move => Frf g /icf_F2MF_tight tight; apply/tight_rlzr/tight. Qed.

Lemma F2MF_rlzr F (f: A ->> A'):
	(F2MF F) \realizes f <->
	(forall q a, a \is_response_to q -> a \from dom f ->
		exists a', a' \is_response_to (F q) /\ f a a').
Proof.
split => rlzr q a aaq afd; first by apply/rlzr_val; first apply rlzr; first apply aaq.
by split => [ | Fq <-]; [rewrite F2MF_dom | apply/rlzr].
Qed.

Lemma F2MF_rlzr_F2MF F (f: A -> A') :
	(F2MF F) \realizes (F2MF f) <-> forall q a, a \is_response_to q -> (f a) \is_response_to (F q).
Proof.
rewrite F2MF_rlzr.
split => ass phi x phinx; last by exists (f x); split => //; apply ass.
by have [ | fx [cd ->]]:= ass phi x phinx; first by apply F2MF_tot.
Qed.

Lemma rlzr_val_sing (f: A ->> A') F: f \is_singlevalued -> F \realizes f ->
	forall q a q' a', a \is_response_to q -> f a a' -> F q q' -> a' \is_response_to q'.
Proof.
move => sing rlzr q a q' a' aaq faa' Fqq'.
have [ | _ prp]:= rlzr q a aaq; first by exists a'.
have [d' [d'aq' fad']]:= prp q' Fqq'.
by rewrite (sing a a' d').
Qed.

Lemma sing_rlzr (f: A ->> A') F: F \is_singlevalued -> f \is_singlevalued ->
	F \realizes f
	<->
	(forall q a, a \is_response_to q -> a \from dom f -> q \from dom F)
		/\
	(forall q a q' a', a \is_response_to q -> f a a' -> F q q' -> a' \is_response_to q').
Proof.
move => Fsing fsing.
split; first by move => Frf; split => [q a arq afd |]; [exact/rlzr_dom/afd | exact/rlzr_val_sing].
move => [prp cnd] q a aaq afd.
split => [ | q' Fqq']; first by apply /prp/afd/aaq.
move: afd => [a' faa'].
by exists a'; split => //; apply /cnd/Fqq'/faa'.
Qed.

Lemma rlzr_F2MF F (f: A -> A'):
	F \realizes (F2MF f)
	<->
	forall q a, a \is_response_to q -> q \from dom F
		/\
	forall q', F q q' -> (f a) \is_response_to q'.
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
