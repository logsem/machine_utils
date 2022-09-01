From Coq Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From machine_utils Require Import finz classes.

(* Helper tactics *)

#[export] Hint Extern 0 (@SimplTC _ _ _) => (cbn; reflexivity) : typeclass_instances.
#[export] Hint Extern 0 (@CbvTC _ ?lhs _) => (
  let lhs' := eval vm_compute in lhs in
  change lhs with lhs';
  reflexivity
) : typeclass_instances.

(* Address manipulation *)

#[global] Instance FinZOffsetLe_refl z : FinZOffsetLe z z.
Proof. apply Z.le_refl. Qed.

Lemma FinZOffsetLe_compute z z' : (z <=? z' = true)%Z -> FinZOffsetLe z z'.
Proof. intro. apply Z.leb_le; auto. Qed.
#[export] Hint Extern 1 (FinZOffsetLe _ _) => (apply FinZOffsetLe_compute; reflexivity) : typeclass_instances.

Lemma FinZOffsetLt_compute z z' : (z <? z' = true)%Z -> FinZOffsetLt z z'.
Proof. intro. apply Z.ltb_lt; auto. Qed.
#[export] Hint Extern 1 (FinZOffsetLt _ _) => (apply FinZOffsetLt_compute; reflexivity) : typeclass_instances.

#[global] Instance FinZOffsetLe_of_lt z z' : FinZOffsetLt z z' → FinZOffsetLe z z'.
Proof. unfold FinZOffsetLt, FinZOffsetLe. lia. Qed.

#[global] Instance AsWeakFinZIncr_incr fb (b : finz fb) z:
  AsWeakFinZIncr (b ^+ z)%f b z.
Proof. reflexivity. Qed.

#[global] Instance AsWeakFinZIncr_no_incr fb (b : finz fb):
  AsWeakFinZIncr b b 0 | 50.
Proof. unfold AsWeakFinZIncr. solve_finz. Qed.

#[global] Instance FinZLe_refl fb (a : finz fb) : FinZLe a a.
Proof. unfold FinZLe. solve_finz. Qed.

#[global] Instance FinZLe_of_lt fb (a a' : finz fb) : FinZLt a a' → FinZLe a a'.
Proof. unfold FinZLt, FinZLe. solve_finz. Qed.

#[global] Instance FinZLe_offsets fb (a a' a'' : finz fb) (z z': Z) :
  AsWeakFinZIncr a' a z →
  AsWeakFinZIncr a'' a z' →
  FinZOffsetLe 0%Z z →
  FinZOffsetLe z z' →
  FinZLe a' a''.
Proof. unfold FinZOffsetLe, FinZLe, AsWeakFinZIncr. solve_finz. Qed.

#[global]Instance FinZLt_offsets fb (a a' a'': finz fb) (z z': Z) :
  AsWeakFinZIncr a' a z →
  AsWeakFinZIncr a'' a z' →
  FinZOffsetLe 0 z →
  ContiguousRegion a z' →
  FinZOffsetLt z z' →
  FinZLt a' a''.
Proof.
  unfold AsWeakFinZIncr, FinZOffsetLe, FinZOffsetLt, FinZLt.
  intros ? ? ? [? ?] ?. solve_finz.
Qed.

#[global] Instance FinZEqSame fb (f : finz fb) : FinZEq f f true.
Proof. constructor. Qed.

#[global] Instance FinZEq_offset_cbv fb (b : finz fb) z z' :
  CbvTC z z' →
  FinZEq (b ^+ z)%f (b ^+ z')%f true.
Proof. intros ->. constructor. Qed.

#[global] Instance FinZEq_default_neq fb (a a' : finz fb) : FinZEq a a' false | 100.
Proof. inversion 1. Qed.

#[global] Instance ZToFinZ_z_of fb (a : finz fb) :
  ZToFinZ (finz.to_z a) a.
Proof. apply finz_of_z_to_z. Qed.




(* Tests *)

Goal forall fb (a : finz fb),
  FinZEq (a ^+ 1)%f (a ^+ (Z.of_nat 1))%f true.
Proof. typeclasses eauto. Qed.

Goal forall fb (a : finz fb), exists a' z,
  AsWeakFinZIncr (a ^+ 1)%f a' z ∧ a' = a ∧ z = 1%Z.
Proof. intros. do 2 eexists. repeat apply conj. typeclasses eauto. all: reflexivity. Qed.
