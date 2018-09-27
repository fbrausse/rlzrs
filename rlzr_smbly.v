From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mf.
Require Import rlzr_base.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section assemblies.
Lemma id_sur S: (@mf_id S) \is_cototal.
Proof. by rewrite cotot_spec => c; exists c. Qed.

Definition id_assembly_mixin S: assembly_mixin.type S S.
Proof. exists mf_id; exact/id_sur. Defined.

Definition id_assembly S:= assembly.Pack (id_assembly_mixin S).

Context Q (A : assembly Q).

Definition comp_ref (D: assembly A):= (ref D) o_R (ref A).

Lemma comp_ref_sur (D: assembly A): (comp_ref D) \is_cototal.
Proof.
rewrite cotot_spec => d''.
have [d dnd'']:= get_name d''.
have [q qnd]:= get_name d.
by exists q; exists d.
Qed.

Definition combine_assembly_mixin (D: assembly A): assembly_mixin.type Q D.
Proof. exists (comp_ref D); exact/comp_ref_sur. Defined.

Canonical cmbn_smbly (D: assembly A) := assembly.Pack (combine_assembly_mixin D).

Context Q' (A': assembly Q').
Definition prod_ref := (ref A) ** (ref A').

Lemma prod_ref_sur: prod_ref \is_cototal.
Proof. by apply/fprd_cotot/ref_sur/ref_sur. Qed.

Definition prod_assembly_mixin : assembly_mixin.type (Q * Q') (A * A').
Proof. by exists prod_ref; exact/prod_ref_sur. Defined.

Canonical prod_assembly := assembly.Pack prod_assembly_mixin.

Definition sum_ref:= (ref A) +s+ (ref A').

Lemma sum_ref_sur: sum_ref \is_cototal.
Proof. rewrite cotot_spec => [[a | b]] /=.
	by have [c cna]:= get_name a; exists (inl c).
by have [c cnab]:= get_name b; exists (inr c).
Qed.

Definition sum_assembly_mixin: assembly_mixin.type (Q + Q') (A + A').
Proof. by exists sum_ref; exact /sum_ref_sur. Defined.

Canonical sum_assembly := assembly.Pack sum_assembly_mixin.
End assemblies.