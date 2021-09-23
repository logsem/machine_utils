From Coq Require Import ssreflect.
From stdpp Require Import base numbers.
From machine_utils Require Import finz_base solve_finz.

Lemma finz_add_0 fb (a : finz fb) :
  (a + 0)%f = Some a.
Proof. solve_finz. Qed.

Lemma finz_add_0_default fb (a : finz fb) :
  (a ^+ 0)%f = a.
Proof. solve_finz. Qed.

Lemma InBounds_sub fb (b e b' e' a : finz fb) :
  SubBounds b e b' e' →
  InBounds b' e' a →
  InBounds b e a.
Proof. intros (? & ? & ?) [? ?]. unfold InBounds. solve_finz. Qed.

(* -- tests -- promote to lemmas if needed *)

Goal forall fb (a : finz fb),
  (a + 1)%f = None ->
  (a:Z) = (fb - 1)%Z.
Proof. solve_finz. Qed.

Goal forall fb (a : finz fb) (n m : Z),
  (0 <= n)%Z ->
  (0 <= m)%Z ->
  ((a ^+ n) ^+ m)%f = (a ^+ (n + m)%Z)%f.
Proof. solve_finz. Qed.

Goal forall fb (a a' : finz fb),
  (a + 1)%f = Some a' →
  (a < a')%Z.
Proof. solve_finz. Qed.

Goal forall fb (a a' : finz fb) (i : Z),
  (i > 0)%Z →
  (a + i)%f = Some a' → (a < a')%Z.
Proof. solve_finz. Qed.

Goal forall fb (a a' : finz fb) (i : Z),
  (i >= 0)%Z →
  (a + i)%f = Some a' → (a <= a')%Z.
Proof. solve_finz. Qed.

Goal forall fb (a e : finz fb),
  (a < e)%Z → ∃ a', (a + 1)%f = Some a'.
Proof. intros. zify_finz; eauto. exfalso. lia. lia. Qed.

Goal forall fb (a e : finz fb),
  (a < e)%Z -> ∃ a', (a + 1)%f = Some a'.
Proof. intros. zify_finz; eauto. exfalso. lia. lia. Qed.

Goal forall fb (a e a' : finz fb),
  (a < e)%Z → (a + 1)%f = Some a' → (e < a')%Z → False.
Proof. solve_finz. Qed.

Goal forall fb (a e a' : finz fb),
  (a < e)%Z → (a + 1)%f = Some a' → (a' ≤ e)%Z.
Proof. solve_finz. Qed.

Goal forall fb (a e a' : finz fb),
  (a + 1)%f = Some a' → (a < e)%Z → (Z.abs_nat (e - a) - 1) = (Z.abs_nat (e - a')).
Proof. solve_finz. Qed.

Goal forall fb (a1 a2 a3 : finz fb) (z1 z2 : Z),
  (a1 + z1)%f = Some a2 → (a2 + z2)%f = Some a3 →
  (a1 + (z1 + z2))%f = Some a3.
Proof. solve_finz. Qed.

Goal forall fb (a a' : finz fb) (z1 z2 : Z),
  (a + z1)%f = Some a' →
  (a + (z1 + z2))%f = (a' + z2)%f.
Proof. solve_finz. Qed.

Goal forall fb (a1 a2 a3 : finz fb) (z1 z2 : Z),
  (a1 + z1)%f = Some a2 -> (a1 + z2)%f = Some a3 -> (z1 <= z2)%Z ->
  (a2 <= a3)%Z.
Proof. solve_finz. Qed.

Goal forall fb (a : finz fb) i k,
  (k >= 0)%Z -> (i >= 0)%Z ->
  (((a ^+ i) ^+ k)%f) =
  ((a ^+ (i + k)%Z)%f).
Proof. solve_finz. Qed.

Goal forall fb (a a' : finz fb),
  (a + 1)%f = Some a' →
  (a + 1)%Z = a'.
Proof. solve_finz. Qed.

Goal forall fb (a a' : finz fb) i,
  (a + i)%f = Some a' →
  (a + i)%Z = a'.
Proof. solve_finz. Qed.

Goal forall fb (a1 a2: finz fb) (z:Z),
      (a1 + z)%f = Some a2 → (a2 + (- z))%f = Some a1.
Proof. solve_finz. Qed.
