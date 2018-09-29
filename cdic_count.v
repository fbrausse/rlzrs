From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mf.
Require Import ClassicalChoice Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).

Section MINIMIZATION.
(* Most code from this section was provided by Vincent *)
Context (p: nat -> bool).

Let Fixpoint searchU m k : nat :=
  match k with
  | 0 => m
  | k'.+1 => let n := m - k in if p n then n else searchU m k'
  end.

Let searchU_correct m k :
  p m -> p (searchU m k).
Proof.
move => hm.
by elim: k => // n ih /=; case: ifP.
Qed.

Let searchU_le m k :
  searchU m k <= m.
Proof.
elim: k => // n ih /=; case: ifP => // _.
rewrite /subn /subn_rec; apply /leP; lia.
Qed.

Let searchU_minimal m k :
  (forall n, p n -> m - k <= n) -> forall n, p n -> searchU m k <= n.
Proof.
elim: k.
- move => h n /=; rewrite -(subn0 m); exact: h.
move => k ih h n /=; case: ifP.
- move => _; exact: h.
move => hk; apply: ih => i hi.
case: (i =P m - k.+1).
move => eq.
rewrite -eq in hk.
by rewrite hk in hi.
move: (h i hi).
rewrite /subn /subn_rec => /leP prp cnd; apply/leP; lia.
Qed.

Definition search n := searchU n n.

Lemma search_correct n:
	p n -> p (search n).
Proof.
exact: searchU_correct.
Qed.

Lemma search_le n:
	search n <= n.
Proof.
exact: searchU_le.
Qed.

Lemma search_min n m:
	p m -> search n <= m.
Proof.
apply searchU_minimal.
move => k pk.
rewrite /subn/subn_rec; apply/leP; lia.
Qed.
End MINIMIZATION.

Section SECTIONS.
Lemma worder_nat (p : nat -> bool):
	(exists n, p n) -> exists n, p n /\ forall m, p m -> n <= m.
Proof.
move => [m pm].
exists (search p m ).
split; first exact: search_correct.
exact: search_min.
Qed.

Lemma well_order_nat (P : nat -> Prop):
	(exists n, P n) -> exists n, P n /\ forall m, P m -> n <= m.
Proof.
set R:= (fun n b => P n <-> is_true b).
have [ | p prop]:= choice R.
	by move => n; case: (classic (P n)) => pn; [exists true|exists false]; split.
move => [m Pm].
have ex: exists n, p n by exists m; apply prop.
have [n [pn min]]:= (worder_nat ex).
by exists n; split => [ | k Pk ]; [ | apply min]; apply prop.
Qed.

Notation "f '\is_surjective'" := (f \is_surjective_function) (at level 2).

Context Q (cnt: nat -> Q) (sur: cnt \is_surjective).

Definition is_min_sec (sec : Q -> nat) :=
  cancel sec cnt /\ forall s,(forall m, cnt m = s -> sec s <= m).

Notation "sec '\is_minimal_section'" := (is_min_sec sec) (at level 2).

Lemma minimal_section:
  exists sec, sec \is_minimal_section.
Proof.
set R := (fun s n => cnt n = s /\ (forall m, cnt m = s -> n <= m)).
have [ | sec]:= (choice R).
	 by move => s; have [n]:= well_order_nat (sur s); exists n.
by exists sec; split => s; have []:= p s.
Qed.
End SECTIONS.
Notation "sec '\is_minimal_section_of' cnt" := (is_min_sec cnt sec) (at level 2).

Local Open Scope coq_nat_scope.
Section COUNTABILITY.
Definition is_count Q :=
	exists cnt: nat -> option Q, cnt \is_surjective_function.
Notation "T '\is_countable'" := (is_count T) (at level 2).

Lemma classic_eqClass Q : exists P : Equality.class_of Q, True.
Proof.
have /choice[eq eqP]: forall q, exists b, (q.1 = q.2 :> Q) <-> (b = true).
  by move=> q; case: (classic (q.1 = q.2)) => ass; [exists true|exists false].
unshelve eexists (@Equality.Mixin _ (fun x y => eq (x, y)) _) => //.
by move=> x y; apply: (iffP idP) => [/eqP//|->]; apply/eqP.
Qed.

Lemma count_countMixin Q : Q \is_countable ->
  exists P : Countable.mixin_of Q, True.
Proof.
move => [cnt sur]; have [sec [issec min]] := minimal_section sur.
unshelve eexists (@Countable.Mixin _ (sec \o some) cnt _) => //.
by move=> x /=; rewrite issec.
Qed.

Lemma count_countClass Q  : Q \is_countable ->
  exists P : Countable.class_of Q, True.
Proof.
move=> /count_countMixin[cmQ _]; have [eqQ _] := classic_eqClass Q.
set QeqType := EqType Q eqQ.
set QchoiceType := ChoiceType QeqType (CountChoiceMixin cmQ).
by exists (Countable.class (CountType QchoiceType cmQ)).
Qed.

Lemma countMixin_count T : Countable.mixin_of T -> T \is_countable.
Proof.
move=> [pickle unpickle pickleK].
exists (fun n => if n isn't n.+1 then None else unpickle n).
move=> [x|]; last by exists 0.
by exists (pickle x).+1; rewrite pickleK.
Qed.

Lemma countType_count (T : countType) : T \is_countable.
Proof. by apply: countMixin_count; case: T => [?[]]. Qed.

Lemma nat_count: nat \is_countable.
Proof. exact: countType_count. Qed.

Lemma option_count T : T \is_countable -> (option T) \is_countable.
Proof.
move=> /count_countClass [cT _]; set T' : Type := Countable.Pack cT T.
by rewrite -[T]/T'; apply: countType_count.
Qed.

Lemma sum_count Q Q': Q \is_countable -> Q' \is_countable ->
  (Q + Q') \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
move=> /count_countClass [cQ' _]; set Q'C : Type := Countable.Pack cQ' Q'.
by rewrite -[Q]/QC -[Q']/Q'C; apply: countType_count.
Qed.

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
move=> /count_countClass [cQ' _]; set Q'C : Type := Countable.Pack cQ' Q'.
by rewrite -[Q]/QC -[Q']/Q'C; apply: countType_count.
Qed.

Lemma list_count Q: Q \is_countable -> (list Q) \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
by rewrite -[Q]/QC; apply: countType_count.
Qed.

Lemma count_sur Q: (exists cnt: nat -> Q, cnt \is_surjective_function) <-> inhabited Q /\ Q \is_countable.
Proof.
split => [ [cnt sur] | [[someq [cnt sur]]]].
	split; first exact (inhabits (cnt 0)).
	exists (fun n => match n with
		| 0 => None
		| S n' => Some (cnt n')
	end).
	move => q.
	case: q; last by exists 0.
	move => q.
	have [n val] := sur (q).
	by exists (S n); rewrite val.
exists (fun n => match cnt n with
	| None => someq
	| Some q => q
end) => q.
have [n val] := sur (some q).
by exists n; rewrite val.
Qed.

End COUNTABILITY.
Notation "T '\is_countable'" := (is_count T) (at level 2).