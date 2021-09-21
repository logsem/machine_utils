From Coq Require Import ssreflect.
From stdpp Require Import base numbers list.
From machine_utils Require Import finz_base solve_finz finz_lemmas.

Module finz.

Definition dist {fb} (b e : finz fb) : nat :=
  Z.to_nat (e - b).

Fixpoint seq {fb} (b : finz fb) (n : nat) : list (finz fb) :=
  match n with
  | 0 => nil
  | S n => b :: (seq (b ^+ 1)%f n)
  end.

Definition seq_between {fb} (b e : finz fb) : list (finz fb) :=
  seq b (dist b e).

End finz.


Section lemmas.

Context {finz_bound : Z}.
Implicit Types f : finz finz_bound.

(*------------------------- finz_dist ------------------------------*)

Lemma finz_dist_S f1 f2 :
  (f1 < f2)%f →
  finz.dist f1 f2 = S (finz.dist (f1 ^+ 1)%f f2).
Proof using. rewrite /finz.dist. solve_finz. Qed.

Lemma finz_dist_0 f1 f2 :
  (f2 <= f1)%f →
  finz.dist f1 f2 = 0.
Proof using. rewrite /finz.dist. solve_finz. Qed.

Lemma finz_dist_split (a b e : finz finz_bound) :
  (b ≤ a ≤ e)%Z →
  finz.dist b e = finz.dist b a + finz.dist a e.
Proof using. intros [? ?]. rewrite /finz.dist. solve_finz. Qed.

Lemma finz_dist_incr_default (a b : finz finz_bound) :
  (b ≤ a)%Z →
  (b ^+ (Z.of_nat (finz.dist b a)) = a)%f.
Proof using. intros Hle. rewrite /finz.dist. solve_finz. Qed.

Lemma finz_dist_incr (a b : finz finz_bound) :
  (b <= a)%f →
  (b + (Z.of_nat (finz.dist b a)))%f = Some a.
Proof using. intros. unfold finz.dist. solve_finz. Qed.

Lemma finz_incr_iff_dist (a b : finz finz_bound) (i : nat) :
  (a + (Z.of_nat i))%f = Some b ↔ (a <= b)%f ∧ finz.dist a b = i.
Proof using.
  rewrite /finz.dist. split; [ intros | intros [? ?] ]; solve_finz.
Qed.

(*----------------------------- seq --------------------------------*)

Lemma finz_seq_length f n :
  length (finz.seq f n) = n.
Proof using. revert f. induction n; intros; simpl; auto. Qed.

Lemma finz_seq_singleton f :
  finz.seq f 1 = [f].
Proof using. done. Qed.

Lemma finz_seq_decomposition n f k :
  (k <= n)%nat ->
  finz.seq f n = finz.seq f k ++ (finz.seq ((f ^+ (Z.of_nat k))%f) (n - k)).
Proof using.
  revert f k. induction n.
  - intros. assert ((k = 0)%nat) by lia; subst k. reflexivity.
  - intros * HH. inversion HH; subst.
    + rewrite Nat.sub_diag. simpl. rewrite app_nil_r //.
    + simpl. destruct k; simpl. by rewrite finz_add_0_default.
      rewrite (IHn ((f^+1))%f k); [lia|]. do 3 f_equal. solve_finz.
Qed.

Lemma finz_seq_notin f f' n :
  (f < f')%f →
  f ∉ finz.seq f' n.
Proof using.
  revert f f'. induction n; cbn.
  { intros. inversion 1. }
  { intros. apply not_elem_of_cons. split. by solve_finz.
    eapply IHn. solve_finz. }
Qed.

Lemma finz_seq_NoDup f (n : nat) :
  is_Some (f + (Z.of_nat n))%f →
  NoDup (finz.seq f n).
Proof using.
  revert f. induction n; intros f Hfn.
  { apply NoDup_nil_2. }
  { cbn. apply NoDup_cons_2.
    { apply finz_seq_notin. solve_finz. }
    { eapply IHn. solve_finz. } }
Qed.

Lemma finz_seq_lookup f0 fi (i n : nat) :
  i < n →
  (f0 + (Z.of_nat i))%f = Some fi →
  finz.seq f0 n !! i = Some fi.
Proof using.
  revert i fi f0. induction n.
  { intros. lia. }
  { intros i fi f0 Hi Hfi. cbn.
    destruct i as [|i].
    { cbn. solve_finz. }
    { cbn. apply IHn. lia. solve_finz. } }
Qed.

(*------------------------- seq_between ----------------------------*)

Lemma finz_seq_between_length f1 f2 :
  length (finz.seq_between f1 f2) = finz.dist f1 f2.
Proof using. by rewrite /finz.seq_between finz_seq_length. Qed.

Lemma finz_seq_between_empty f1 f2:
  (f2 <= f1)%f ->
  finz.seq_between f1 f2 = [].
Proof using.
  intros. rewrite /finz.seq_between /finz.dist /=.
  replace (Z.to_nat (f2 - f1)) with 0 by solve_finz.
  reflexivity.
Qed.

Lemma finz_seq_between_decomposition (b a e : finz finz_bound) :
  (b <= a < e)%f ->
  finz.seq_between b e =
  finz.seq_between b a ++ (a :: finz.seq_between (a^+1)%f e).
Proof with try (unfold finz.dist; solve_finz) using.
  intros [? ?]. unfold finz.seq_between at 1.
  rewrite (finz_seq_decomposition _ _ (finz.dist b a))...
  rewrite (_ : finz.dist b e - finz.dist b a = finz.dist a e)...
  rewrite -/(finz.seq_between b a). f_equal.
  rewrite (_ : finz.dist a e = S (finz.dist (a^+1)%f e))...
  cbn. f_equal... rewrite /finz.seq_between. f_equal...
Qed.

Lemma finz_seq_between_split (b a e : finz finz_bound) :
  (b <= a ∧ a <= e)%f →
  finz.seq_between b e = finz.seq_between b a ++ finz.seq_between a e.
Proof with try (unfold finz.dist; solve_finz) using.
  intros [? ?]. unfold finz.seq_between at 1.
  rewrite (finz_seq_decomposition _ _ (finz.dist b a))...
  rewrite (_: finz.dist b e - finz.dist b a = finz.dist a e)...
  rewrite (_: (b ^+ (Z.of_nat (finz.dist b a)))%f = a)...
  rewrite -/(finz.seq_between _ _) //.
Qed.

Lemma finz_seq_between_first f1 f2 :
  (f1 < f2)%f →
  (finz.seq_between f1 f2) !! 0 = Some f1.
Proof using.
  intros. rewrite /finz.seq_between.
  rewrite (_: finz.dist f1 f2 = S (finz.dist f1 f2 - 1)).
  all: by unfold finz.dist; solve_finz.
Qed.

Lemma finz_seq_between_NoDup f1 f2 :
  NoDup (finz.seq_between f1 f2).
Proof using.
  rewrite /finz.seq_between. destruct (Z_le_dec f1 f2).
  { apply finz_seq_NoDup. unfold finz.dist; solve_finz. }
  { rewrite /finz.dist Z_to_nat_nonpos. lia. apply NoDup_nil_2. }
Qed.

Lemma finz_seq_between_cons f1 f2 :
  (f1 < f2)%f →
  finz.seq_between f1 f2 = f1 :: finz.seq_between (f1^+1)%f f2.
Proof using.
  intros. rewrite (finz_seq_between_decomposition f1 f1). solve_finz.
  rewrite /finz.seq_between finz_dist_0 //. solve_finz.
Qed.

Lemma elem_of_finz_seq_between (a b e : finz finz_bound) :
  a ∈ finz.seq_between b e ↔ (b <= a < e)%f.
Proof using.
  rewrite /finz.seq_between /finz.dist.
  set n := Z.to_nat (e - b). have: (n = Z.to_nat (e - b)) by reflexivity.
  clearbody n. revert n a b e. induction n.
  { intros. cbn. rewrite elem_of_nil. solve_finz. }
  { intros. cbn. rewrite elem_of_cons (IHn a _ e). 2: solve_finz.
    split. intros [ -> | ]; solve_finz. intros [Hba ?].
    apply Zle_lt_or_eq in Hba. destruct Hba; [| subst]. solve_finz.
    assert (b = a) by solve_finz. subst. solve_finz. }
Qed.

Lemma not_elem_of_finz_seq_between (a b e : finz finz_bound) :
  a ∉ finz.seq_between b e ↔ (a < b)%f ∨ (e <= a)%f.
Proof using.
  destruct (decide ((a < b)%f ∨ (e <= a)%f)) as [X1|X1];
  destruct (decide (a ∈ finz.seq_between b e)) as [X2|X2].
  - rewrite -> elem_of_finz_seq_between in *. solve_finz.
  - split; auto.
  - rewrite -> elem_of_finz_seq_between in *. solve_finz.
  - split; auto. intros _. exfalso. apply X2, elem_of_finz_seq_between.
    solve_finz.
Qed.

Lemma finz_seq_between_singleton f1 f2 :
  (f1 + 1)%f = Some f2 →
  finz.seq_between f1 f2 = [f1].
Proof using.
  intros. rewrite /finz.seq_between.
  rewrite (_: finz.dist f1 f2 = 1) //= /finz.dist.
  solve_finz.
Qed.

Lemma finz_seq_between_lookup f0 fn (i n : nat) :
  i < n →
  (f0 + (Z.of_nat n))%f = Some fn →
  (finz.seq_between f0 fn) !! i = Some (f0 ^+ (Z.of_nat i))%f.
Proof using.
  intros Hin Hfn.
  rewrite /finz.seq_between.
  rewrite (_: finz.dist f0 fn = n).
  { rewrite /finz.dist. solve_finz. }
  apply finz_seq_lookup; eauto. solve_finz.
Qed.

End lemmas.
