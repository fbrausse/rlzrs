From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mf.
Require Import cdic_base cdic_ntrvw.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section realizers.

Context Q (D: interview Q).

Lemma id_rlzr: (@mf_id Q) \realizes (@mf_id D).
Proof. by move => q a qna [d /= eq]; split => [ | _ <-]; [exists q | exists a]. Qed.

Context Q' (D': interview Q').

Lemma cmbn_smbly_rlzr (D'': interview D) (D''': interview D') F G f:
	F \realizes G -> G \realizes f -> F \realizes (f: cmbn_ntrvw D'' ->> cmbn_ntrvw D''').
Proof.
move => FrG Grf q a [d [qnd dna]] afd.
have [dfd prp]:= Grf d a dna afd.
have [qfd prp']:= FrG q d qnd dfd.
split => // q' Fqq'.
have [d' [q'nd' Gdd']]:= prp' q' Fqq'.
have [d''' [d'nd''' fd'd''']]:= prp d' Gdd'.
by exists d'''; split => //; exists d'.
Qed.

Lemma fprd_rlzr Q'' (D'': interview Q'') Q''' (D''': interview Q''')
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
	(@mf_fst Q Q') \realizes (@mf_fst D D': (prod_interview D D') ->> D).
Proof.
move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q1.
by move => q' <-; exists a.1.
Qed.

Lemma snd_rlzr:
	(@mf_snd Q Q') \realizes (@mf_snd D D': (prod_interview D D') ->> D').
Proof.
move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q2.
by move => q' <-; exists a.2.
Qed.

Lemma diag_rlzr: (@mf_diag Q) \realizes (@mf_diag D: D ->> (prod_interview D D)).
Proof. by move => q a aaq _; split => [ | [_ _] [<- <-]]; [exists (q, q) | exists (a, a)]. Qed.

Lemma cnst_rlzr (q': Q') (a': D'):
	a' \is_response_to q' -> (@mf_cnst Q Q' q') \realizes (@mf_cnst D D' a').
Proof. by move => a'aq' q a aaq _; split => [ | _ <-]; [exists q' | exists a']. Qed.

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
Arguments fst_rlzr {Q} D {Q'} D'.
Arguments snd_rlzr {Q} D {Q'} D'.