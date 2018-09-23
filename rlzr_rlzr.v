From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mf.
Require Import rlzr_smbly.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section realizer.
Context Q (D: assembly Q) Q' (D': assembly Q').

Definition rlzr (F: Q ->> Q') (f: D ->> D') :=
		(forall q a, a \is_answer_to q -> a \from_dom f -> q \from_dom F /\
		forall q', F q q' -> exists a', a' \is_answer_to q' /\ f a a').
Notation "f '\is_realized_by' F" := (rlzr F f) (at level 2).
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

Lemma F2MF_rlzr F (f: D ->> D'):
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

Lemma F2MF_rlzr_F2MF F (f: D -> D') :
	(F2MF F) \realizes (F2MF f) <-> forall q a, a \is_answer_to q -> (f a) \is_answer_to (F q).
Proof.
rewrite F2MF_rlzr.
split => ass phi x phinx; last by exists (f x); split => //; apply ass.
by have [ | fx [cd ->]]:= ass phi x phinx; first by apply F2MF_tot.
Qed.

Lemma rlzr_dom (f: D ->> D') F:
	F \realizes f -> forall q a, a \is_answer_to q -> a \from_dom f -> q \from_dom F.
Proof. by move => rlzr q a aaq afd; have [ex prp]:= rlzr q a aaq afd. Qed.

Lemma rlzr_val_sing (f: D ->> D') F: f \is_singlevalued -> F \realizes f ->
	forall q a q' a', a \is_answer_to q -> f a a' -> F q q' -> a' \is_answer_to q'.
Proof.
move => sing rlzr q a q' a' aaq faa' Fqq'.
have [ | _ prp]:= rlzr q a aaq; first by exists a'.
have [d' [d'aq' fad']]:= prp q' Fqq'.
by rewrite (sing a a' d').
Qed.

Lemma sing_rlzr (f: D ->> D') F: F \is_singlevalued -> f \is_singlevalued ->
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

Lemma rlzr_F2MF F (f: D -> D'):
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

End realizer.
Notation "f '\is_realized_by' F" := (rlzr F f) (at level 2).
Notation "F '\realizes' f" := (rlzr F f) (at level 2).
Notation "f \is_translation" := (trnsln f) (at level 2).

Section realizers.
Context Q (D: assembly Q) Q' (D': assembly Q').

Lemma rlzr_comp Q'' (D'': assembly Q'') G F (f: D ->> D') (g: D' ->> answers D''):
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

Lemma mfpp_rlzr Q'' (D'': assembly Q'') Q''' (D''': assembly Q''')
	F (f: D ->> D') G (g: D'' ->> D'''):
	F \realizes f -> G \realizes g -> (F ** G) \realizes (f ** g).
Proof.
move => Frf Grg [q q''] [a a''] [/=aaq a''aq''] [[a' a''']] [/=faa' ga''a'''].
have afd: a \from_dom f by exists a'.
have afd': a'' \from_dom g by exists a'''.
have [ex prp]:= Frf q a aaq afd.
have [ex' prp']:= Grg q'' a'' a''aq'' afd'.
split => [ | [q' q'''] /= [Fqq' Gq''q''']]; last first.
	 have [d' [d'aq' fad']]:= prp q' Fqq'.
	 have [d''' [d'''aq''' ga''d''']]:= prp' q''' Gq''q'''.
	 by exists (d', d''').
have [q' Fqq']:= ex; have [q''' Gq''q''']:= ex'.
by exists (q', q''').
Qed.

Lemma fst_rlzr:
	(@mf_fst Q Q') \realizes (@mf_fst D D': (prod_assembly D D') ->> D).
Proof.
move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q1.
by move => q' <-; exists a.1.
Qed.

Lemma snd_rlzr:
	(@mf_snd Q Q') \realizes (@mf_snd D D': (prod_assembly D D') ->> D').
Proof.
move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q2.
by move => q' <-; exists a.2.
Qed.

Lemma diag_rlzr: (@mf_diag Q) \realizes (@mf_diag D: D ->> (prod_assembly D D)).
Proof. by move => q a aaq _; split => [ | [_ _] [<- <-]]; [exists (q, q) | exists (a, a)]. Qed.

(*
Lemma rlzr_comp_codom Q'' (D'': assembly Q'') G F (f: A ->> A') (g:  A'->> answers D''):
	G \realizes (g|_(codom f)) -> F \realizes f -> (G o F) \realizes (g o f).
Proof.
move => rlzr rlzr' q a aaq [a'' [[a' [faa' ga'a'']] subs]] q'' [[q' [Fqq' Gq'q'']] subs'].
have afd: a \from_dom f by exists a'.
have [d' [d'aq' fad']]:= rlzr' q a aaq afd q' Fqq'.
have afd': d' \from_dom (g|_(codom f)).
	have [b gbd']:= subs d' fad'.
	by exists b; split; first by exists a.
have [d'' [d''aq'' [d'fd gd'd'']]]:= rlzr q' d' d'aq' afd' q'' Gq'q''.
exists d''; split => //.
by split; first by exists d'.
Qed.
*)
End realizers.
Check fst_rlzr.
Arguments fst_rlzr {Q} D {Q'} D'.
Arguments snd_rlzr {Q} D {Q'} D'.