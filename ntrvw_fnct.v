Require Import ntrvw_base ntrvw_rlzr.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section realizers.
Context Q (A: interview Q).

Lemma id_rlzr: (@mf_id Q) \realizes (@mf_id A).
Proof. by move => q a qna [d /= eq]; split => [ | _ <-]; [exists q | exists a]. Qed.

Context Q' (A': interview Q').

Lemma cmbn_smbly_rlzr (A'': interview A) (A''': interview A') F G f:
	F \realizes G -> G \realizes f -> F \realizes (f: cmbn_ntrvw A'' ->> cmbn_ntrvw A''').
Proof.
move => FrG Grf q a [d [qnd dna]] afd.
have [dfd prp]:= Grf d a dna afd.
have [qfd prp']:= FrG q d qnd dfd.
split => // q' Fqq'.
have [d' [q'nd' Gdd']]:= prp' q' Fqq'.
have [d''' [d'nd''' fd'd''']]:= prp d' Gdd'.
by exists d'''; split => //; exists d'.
Qed.

Lemma fprd_rlzr Q'' (A'': interview Q'') Q''' (A''': interview Q''')
	F (f: A ->> A') G (g: A'' ->> A'''):
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
	(@mf_fst Q Q') \realizes (@mf_fst A A': (prod_interview A A') ->> A).
Proof.
move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q1.
by move => q' <-; exists a.1.
Qed.

Lemma snd_rlzr:
	(@mf_snd Q Q') \realizes (@mf_snd A A': (prod_interview A A') ->> A').
Proof.
move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q2.
by move => q' <-; exists a.2.
Qed.

Definition mf_cons Q := F2MF (fun aL => @cons Q aL.1 aL.2).

Lemma cons_rlzr:
	(@mf_cons Q) \realizes (@mf_cons A: (prod_interview A (list_interview A) ->> list_interview A)).
Proof.
move => [q K] [a L] [arq LrK] _ ; split; first exact/F2MF_tot.
by move => _ /= <-; exists (cons a L).
Qed.

Lemma diag_rlzr: (@mf_diag Q) \realizes (@mf_diag A: A ->> (prod_interview A A)).
Proof. by move => q a aaq _; split => [ | [_ _] [<- <-]]; [exists (q, q) | exists (a, a)]. Qed.

Lemma cnst_rlzr (q': Q') (a': A'):
	a' \is_response_to q' -> (@mf_cnst Q Q' q') \realizes (@mf_cnst A A' a').
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
Arguments fst_rlzr {Q} A {Q'} A'.
Arguments snd_rlzr {Q} A {Q'} A'.