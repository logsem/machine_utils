From Coq Require Import Eqdep_dec ssreflect ZArith.
From stdpp Require Import base numbers countable.

Module finz.
Section finz.

Context {finz_bound: Z}.

Inductive finz : Type :=
  | FinZ (z : Z) (finz_lt : (z <? finz_bound)%Z = true) (finz_nonneg : (0 <=? z)%Z = true).

Definition to_z (f: finz): Z :=
  match f with
  | FinZ f _ _ => f
  end.

Definition of_z (z : Z) : option finz.
Proof.
  destruct (Z_lt_dec z finz_bound),(Z_le_dec 0%Z z).
  - apply (Z.ltb_lt z finz_bound) in l.
    apply (Z.leb_le 0 z) in l0.
    exact (Some (FinZ z l l0)).
  - exact None.
  - exact None.
  - exact None.
Defined.

Definition le_lt : finz → finz → finz → Prop :=
  λ f1 f2 f3, (to_z f1 <= to_z f2 < to_z f3)%Z.
Definition le : finz → finz → Prop :=
  λ f1 f2, (to_z f1 <= to_z f2)%Z.
Definition lt : finz → finz → Prop :=
  λ f1 f2, (to_z f1 < to_z f2)%Z.
Definition leb : finz → finz → bool :=
  λ f1 f2, Z.leb (to_z f1) (to_z f2).
Definition ltb : finz → finz → bool :=
  λ f1 f2, Z.ltb (to_z f1) (to_z f2).
Definition eqb : finz → finz → bool :=
  λ f1 f2, Z.eqb (to_z f1) (to_z f2).

Program Definition incr (f : finz) (off : Z) : option finz :=
  let z := (to_z f + off)%Z in
  match (Z_lt_dec z finz_bound) with
  | left _ =>
    match (Z_le_dec 0%Z z) with
    | left _ => Some (FinZ z _ _)
    | right _ => None
    end
  | right _ => None
  end.
Next Obligation.
  intros. apply Z.ltb_lt; auto.
Defined.
Next Obligation.
  intros. apply Z.leb_le; auto.
Defined.

Definition max (f1 f2 : finz) : finz :=
  if leb f1 f2 then f2 else f1.

Definition min (f1 f2 : finz) : finz :=
  if leb f1 f2 then f1 else f2.

Program Definition largest (ex: finz) : finz :=
  FinZ (finz_bound - 1) _ _.
Next Obligation. lia. Defined.
Next Obligation. inversion 1. lia. Defined.

Definition incr_default (f : finz) (off : Z) : finz :=
  match incr f off with
  | Some f' => f'
  | None => largest f
  end.

End finz.
End finz.

Arguments finz.finz : clear implicits.
Notation finz := finz.finz.

Declare Scope finz_scope.
Delimit Scope finz_scope with f.

Notation "f1 <= f2 < f3" := (finz.le_lt f1 f2 f3) : finz_scope.
Notation "f1 <= f2" := (finz.le f1 f2) : finz_scope.
Notation "f1 <=? f2" := (finz.leb f1 f2) : finz_scope.
Notation "f1 < f2" := (finz.lt f1 f2) : finz_scope.
Notation "f1 <? f2" := (finz.ltb f1 f2) : finz_scope.
Notation "f1 =? f2" := (finz.eqb f1 f2) : finz_scope.
Notation "f1 + z" := (finz.incr f1 z) : finz_scope.
Notation "f ^+ off" := (finz.incr_default f off) (at level 50) : finz_scope.

Coercion finz.to_z : finz.finz >-> Z.


Section finz_lemmas.

Context {finz_bound : Z}.
Implicit Type f : finz finz_bound.

Lemma finz_to_z_eq f1 f2 :
  finz.to_z f1 = finz.to_z f2 →
  f1 = f2.
Proof.
  destruct f1, f2; cbn. intros ->.
  repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

Lemma finz_eq_to_z f1 f2 :
  f1 = f2 →
  finz.to_z f1 = finz.to_z f2.
Proof. destruct f1; destruct f2. congruence. Qed.

Lemma finz_to_z_neq f1 f2 :
  finz.to_z f1 ≠ finz.to_z f2 →
  f1 ≠ f2.
Proof. congruence. Qed.

Lemma finz_neq_to_z a1 f2 :
  a1 ≠ f2 →
  finz.to_z a1 ≠ finz.to_z f2.
Proof. intros. intros Heq%finz_to_z_eq. congruence. Qed.

Lemma finz_unique f f' flt flt' fnn fnn' :
  f = f' →
  @finz.FinZ finz_bound (finz.to_z f) flt fnn =
  @finz.FinZ finz_bound (finz.to_z f') flt' fnn'.
Proof.
  intros ->. repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

Global Instance finz_eq_dec : EqDecision (finz finz_bound).
Proof.
  intros x y. destruct x as [x],y as [y]. destruct (Z_eq_dec x y).
  - left. eapply finz_to_z_eq; eauto.
  - right. inversion 1. simplify_eq.
Defined.

Lemma finz_spec f :
  (finz.to_z f < finz_bound)%Z ∧ (0 <= finz.to_z f)%Z.
Proof.
  destruct f. cbn. rewrite -> Z.ltb_lt in finz_lt.
  rewrite -> Z.leb_le in finz_nonneg. lia.
Qed.

Lemma finz_of_z_to_z f :
  finz.of_z (finz.to_z f) = Some f.
Proof.
  generalize (finz_spec f); intros [? ?].
  set (z := (finz.to_z f)) in *.
  unfold finz.of_z.
  destruct (Z_lt_dec z finz_bound) eqn:?;
  destruct (Z_le_dec 0%Z z) eqn:?.
  { f_equal. apply finz_to_z_eq. cbn. lia. }
  all: lia.
Qed.

Lemma finz_of_z_eq_inv f1 f2 :
  finz.of_z (finz.to_z f1) = Some f2 →
  f1 = f2.
Proof. rewrite finz_of_z_to_z. congruence. Qed.

Lemma finz_incr_eq {f z f'} :
  (f + z)%f = Some f' →
  (f ^+ z)%f = f'.
Proof. rewrite /finz.incr_default. intros ->. done. Qed.

Global Instance finz_countable : Countable (finz finz_bound).
Proof.
  refine {| encode r := encode (finz.to_z r) ;
            decode n := match (decode n) with
                        | Some z => finz.of_z z
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro r. destruct r; auto.
  rewrite decode_encode.
  unfold finz.of_z. simpl.
  destruct (Z_lt_dec z finz_bound),(Z_le_dec 0%Z z).
  - repeat f_equal; apply eq_proofs_unicity; decide equality.
  - exfalso. by apply (Z.leb_le 0 z) in finz_nonneg.
  - exfalso. by apply (Z.ltb_lt z finz_bound) in finz_lt.
  - exfalso. by apply (Z.ltb_lt z finz_bound) in finz_lt.
Defined.


Global Instance finz_le_dec : RelDecision (@finz.le finz_bound).
Proof.
  intros x y. destruct x as [x], y as [y].
  destruct (Z_le_dec x y); [by left|by right].
Defined.

Global Instance finz_lt_dec : RelDecision (@finz.lt finz_bound).
Proof.
  intros x y. destruct x as [x], y as [y].
  destruct (Z_lt_dec x y); [by left|by right].
Defined.

Global Instance finz_le_trans : Transitive (@finz.le finz_bound).
Proof.
  intros x y z Hxy Hyz. unfold finz.le. trans y;
  destruct x as [x], y as [y], z as [z]; auto.
Qed.

Global Instance finz_lt_trans : Transitive (@finz.lt finz_bound).
Proof.
  intros x y z Hxy Hyz. unfold finz.lt. trans y;
  destruct x as [x], y as [y], z as [z]; auto.
Qed.

Lemma finz_largest_eq f1 f2 : finz.largest f1 = finz.largest f2.
Proof. by apply finz_to_z_eq. Qed.

End finz_lemmas.
