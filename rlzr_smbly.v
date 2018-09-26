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

Section assemblies.
Lemma id_sur S: (@mf_id S) \is_cototal.
Proof. by rewrite cotot_spec => c; exists c. Qed.

Definition id_assembly_mixin S: assembly_mixin.type S S.
Proof. exists mf_id; exact/id_sur. Defined.

Definition id_assembly S:= assembly.Pack (id_assembly_mixin S).

Context Q (D : assembly Q) Q' (D': assembly Q').
Notation A := (answers D).
Notation A' := (answers D').

Definition prod_ref := (ref D) ** (ref D').

Lemma prod_ref_sur: prod_ref \is_cototal.
Proof. by apply/fprd_cotot/ref_sur/ref_sur. Qed.

Definition prod_assembly_mixin : assembly_mixin.type (Q * Q') (A * A').
Proof. by exists prod_ref; exact/prod_ref_sur. Defined.

Canonical prod_assembly := assembly.Pack prod_assembly_mixin.

Definition sum_ref:= (ref D) +s+ (ref D').

Lemma sum_ref_sur: sum_ref \is_cototal.
Proof. rewrite cotot_spec => [[a | b]] /=.
	by have [c cna]:= get_name a; exists (inl c).
by have [c cnab]:= get_name b; exists (inr c).
Qed.

Definition sum_assembly_mixin: assembly_mixin.type (Q + Q') (A + A').
Proof. by exists sum_ref; exact /sum_ref_sur. Defined.

Canonical sum_assembly := assembly.Pack sum_assembly_mixin.
End assemblies.