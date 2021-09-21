From Coq Require Import ZArith Lia.
From stdpp Require Import list.
From machine_utils Require Import finz_base.

(* Automation: a [solve_finz] tactic that solves arithmetic involving [finz] *)

(* This is implemented as a zify-like tactic, that sends arithmetic on adresses
   into Z, and then calls lia *)

(* Faster alternative to [set (H := v) in *] *)
(* https://github.com/coq/coq/issues/13788#issuecomment-767217670 *)
Ltac fast_set H v :=
  pose v as H; change v with H;
  repeat match goal with H' : context[v] |- _ => change v with H in H' end.

Lemma finz_incr_spec (fb : Z) (f : finz fb) (z : Z) :
  (∃ (f': finz fb),
   (f + z)%f = Some f' ∧ f + z < fb ∧ 0 ≤ f + z ∧ (f':Z) = f + z)%Z
  ∨
  ((f + z)%f = None ∧ (f + z >= fb ∨ f + z < 0))%Z.
Proof.
  unfold finz.incr.
  destruct (Z_lt_dec (f + z)%Z fb),(Z_le_dec 0%Z (f + z)%Z); [ left | right; split; auto; try lia..].
  eexists. repeat split; lia.
Qed.

Ltac finz_incr_as_spec f x :=
  generalize (finz_incr_spec _ f x); intros [(?&?&?&?&?)|(?&[?|?])];
  let fx := fresh "fx" in
  fast_set fx (finz.incr f x);
  clearbody fx; subst fx.

(* Non-branching lemma for the special case of an assumption [(a + z) = Some a'],
   which is common in practice. *)
Lemma finz_incr_Some_spec fb (f f' : finz fb) (z : Z) :
  (f + z)%f = Some f' →
  (f + z < fb ∧ 0 ≤ f + z ∧ (f':Z) = f + z)%Z.
Proof.
  unfold finz.incr.
  destruct (Z_lt_dec (f + z)%Z fb),(Z_le_dec 0%Z (f + z)%Z); inversion 1.
  repeat split; lia.
Qed.

Lemma finz_incr_is_Some_spec fb (f : finz fb) (z : Z) :
  (f + z < fb ∧ 0 ≤ f + z)%Z →
  is_Some (f + z)%f.
Proof.
  unfold finz.incr.
  destruct (Z_lt_dec (f + z)%Z fb),(Z_le_dec 0%Z (f + z)%Z); eauto; lia.
Qed.

Lemma finz_incr_Some_prove_spec (fb : Z) (f f' : finz fb) (z: Z) :
  (f + z < fb ∧ 0 ≤ f + z ∧ (f':Z) = f + z)%Z →
  (f + z)%f = Some f'.
Proof.
  unfold finz.incr.
  destruct (Z_lt_dec (f + z)%Z fb),(Z_le_dec 0%Z (f + z)%Z); eauto; try lia.
  intros. apply f_equal. apply finz_to_z_eq. cbn. lia.
Qed.

Lemma finz_incr_default_spec (fb : Z) (f : finz fb) z :
  (0%Z ≤ f + z ∧ f + z < fb ∧ ((f ^+ z)%f:Z) = f + z)%Z ∨
  ((f + z < 0%Z ∨ fb <= f + z) ∧ ((f ^+ z)%f:Z) = finz.largest f)%Z.
Proof.
  unfold finz.incr_default, finz.incr, finz.largest.
  destruct (Z_lt_dec (f + z)%Z fb),(Z_le_dec 0%Z (f + z)%Z); cbn; lia.
Qed.

Ltac finz_incr_default_as_spec f x :=
  generalize (finz_incr_default_spec _ f x); intros ?;
  let fx := fresh "fx" in
  fast_set fx (finz.incr_default f x);
  clearbody fx.

Lemma finz_min_spec fb (f1 f2 : finz fb) :
  ∃ f, finz.min f1 f2 = f ∧ (f : Z) = Z.min (f1 : Z) (f2 : Z).
Proof.
  exists (finz.min f1 f2); split; auto.
  unfold finz.min. case_match. all: unfold finz.leb in *; lia.
Qed.

Ltac finz_min_as_spec f1 f2 :=
  generalize (finz_min_spec _ f1 f2); intros [? [? ?]];
  let fx := fresh "fx" in
  fast_set fx (finz.min f1 f2);
  clearbody fx; subst fx.

Lemma finz_max_spec fb (f1 f2 : finz fb) :
  ∃ f, finz.max f1 f2 = f ∧ (f : Z) = Z.max (f1 : Z) (f2 : Z).
Proof.
  exists (finz.max f1 f2); split; auto.
  unfold finz.max. case_match. all: unfold finz.leb in *; lia.
Qed.

Ltac finz_max_as_spec f1 f2 :=
  generalize (finz_max_spec _ f1 f2); intros [? [? ?]];
  let fx := fresh "fx" in
  fast_set fx (finz.max f1 f2);
  clearbody fx; subst fx.

Lemma finz_largest_spec fb (f : finz fb) :
  finz.to_z (finz.largest f) = (fb - 1)%Z.
Proof. reflexivity. Qed.

Ltac finz_largest_as_spec f :=
  generalize (finz_largest_spec _ f); intros ?;
  let fx := fresh "fx" in
  fast_set fx (finz.largest f);
  clearbody fx.

Lemma finz_of_z_spec fb (z : Z) :
  (∃ (f : finz fb),
    finz.of_z z = Some f ∧ finz.to_z f = z) ∨
  (@finz.of_z fb z = None ∧ (z >= fb ∨ z < 0))%Z.
Proof.
  unfold finz.of_z.
  destruct (Z_lt_dec z fb).
  { destruct (Z_le_dec 0%Z z).
    { left. eexists. split; auto. }
    { right; split; auto; lia. } }
  { right. destruct (Z_le_dec 0%Z z); split; auto; lia. }
Qed.

Ltac finz_of_z_as_spec z :=
  generalize (finz_of_z_spec _ z); intros [[? [? ?]] | [? [?|?]]];
  let o := fresh "o" in
  fast_set o (finz.of_z z);
  clearbody o; subst o.

Lemma finz_of_z_is_Some_spec fb z (f : finz fb) :
  finz.of_z z = Some f →
  finz.to_z f = z.
Proof.
  destruct (finz_of_z_spec fb z) as [[? [? ?]]|[? ?]]; congruence.
Qed.

Lemma finz_of_z_Some_spec z fb (f : finz fb) :
  finz.to_z f = z →
  finz.of_z z = Some f.
Proof.
  intros. destruct (finz_of_z_spec fb z) as [[? [? ?]]|[? ?]].
  all: subst; rewrite finz_of_z_to_z in *; auto.
Qed.

Lemma Some_eq_inj A (x y: A) :
  Some x = Some y ->
  x = y.
Proof. congruence. Qed.

(* Hook for extending the tactic *)
Ltac zify_finz_op_nonbranching_step_hook :=
  fail.

Ltac zify_finz_op_nonbranching_step :=
  lazymatch goal with
  | |- @eq (finz _) ?f ?f' =>
    apply finz_to_z_eq
  | H : @eq (finz _) ?f ?f' |- _ =>
    apply finz_eq_to_z in H
  | |- not (@eq (finz _) ?f ?f') =>
    apply finz_to_z_neq
  | H : not (@eq (finz _) ?f ?f') |- _ =>
    apply finz_neq_to_z in H
  | |- @eq (option (finz _)) (Some _) (Some _) =>
    f_equal
  | H : @eq (option (finz _)) (Some _) (Some _) |- _ =>
    apply Some_eq_inj in H
  | |- @eq (option (finz _)) (Some _) None =>
    exfalso
  | |- @eq (option (finz _)) None (Some _) =>
    exfalso

  (* wrapper definitions to unfold (<=, <, etc) *)
  | |- context [ finz.le_lt _ _ _ ] =>
    unfold finz.le_lt
  | H : context [ finz.le_lt _ _ _ ] |- _ =>
    unfold finz.le_lt in H
  | |- context [ finz.le _ _ ] =>
    unfold finz.le
  | H : context [ finz.le _ _ ] |- _ =>
    unfold finz.le in H
  | |- context [ finz.leb _ _ ] =>
    unfold finz.leb
  | H : context [ finz.leb _ _ ] |- _ =>
    unfold finz.leb in H
  | |- context [ finz.lt _ _ ] =>
    unfold finz.lt
  | H : context [ finz.lt _ _ ] |- _ =>
    unfold finz.lt in H
  | |- context [ finz.ltb _ _ ] =>
    unfold finz.ltb
  | H : context [ finz.ltb _ _ ] |- _ =>
    unfold finz.ltb in H
  | |- context [ finz.eqb _ _ ] =>
    unfold finz.eqb
  | H : context [ finz.eqb _ _ ] |- _ =>
    unfold finz.eqb in H

  | H : context [ finz.min ?f1 ?f2 ] |- _ =>
    finz_min_as_spec f1 f2
  | |- context [ finz.min ?f1 ?f2 ] =>
    finz_min_as_spec f1 f2
  | H : context [ finz.max ?f1 ?f2 ] |- _ =>
    finz_max_as_spec f1 f2
  | |- context [ finz.max ?f1 ?f2 ] =>
    finz_max_as_spec f1 f2

  | H : context [ finz.largest ?f ] |- _ =>
    finz_largest_as_spec f
  | |- context [ finz.largest ?f ] =>
    finz_largest_as_spec f

  | H : context [ finz.incr_default ?f ?x ] |- _ =>
    finz_incr_default_as_spec f x
  | |- context [ finz.incr_default ?f ?x ] =>
    finz_incr_default_as_spec f x

  | H : is_Some (finz.incr _ _) |- _ =>
    destruct H
  | H : finz.incr _ _ = Some _ |- _ =>
    apply finz_incr_Some_spec in H;
    destruct H as (? & ? & ?)
  | |- is_Some (finz.incr _ _) =>
    apply finz_incr_is_Some_spec
  | |- finz.incr _ _ = Some _ =>
    apply finz_incr_Some_prove_spec

  | H : finz.of_z _ = Some _ |- _ =>
    apply finz_of_z_is_Some_spec in H
  | |- finz.of_z _ = Some _ =>
    apply finz_of_z_Some_spec
  end || zify_finz_op_nonbranching_step_hook.

(* We need some reduction, but naively calling "cbn in *" causes performance
   problems down the road. So here we try to:
   - give a "good enough" allow-list
   - reduce all occurences of [length foo], because in practice [foo] often
     unfolds to a concrete list of instructions and we want its length to compute.
*)
Ltac solve_finz_cbn :=
  cbn [finz.to_z finz.incr_default fst snd length];
  simpl length.

Ltac solve_finz_cbn_in_all :=
  cbn [finz.to_z finz.incr_default fst snd length] in *;
  simpl length in *.

Ltac zify_finz_nonbranching_step :=
  first [ progress solve_finz_cbn_in_all
        | zify_finz_op_nonbranching_step ].

Ltac zify_finz_op_branching_goal_step :=
  lazymatch goal with
  | |- context [ finz.incr ?f ?x ] =>
    finz_incr_as_spec f x
  | |- context [ finz.of_z ?x ] =>
    finz_of_z_as_spec x
  end.

Ltac zify_finz_op_branching_hyps_step :=
  lazymatch goal with
  | _ : context [ finz.incr ?f ?x ] |- _ =>
    finz_incr_as_spec f x
  | _ : context [ finz.of_z ?x ] |- _ =>
    finz_of_z_as_spec x
  end.

Ltac zify_finz_ty_step_on f :=
  generalize (finz_spec f); intros [? ?];
  let z := fresh "z" in
  fast_set z (finz.to_z f);
  clearbody z;
  first [ clear f | revert dependent f ].

Ltac zify_finz_ty_step_var :=
  lazymatch goal with
  | f : finz _ |- _ => zify_finz_ty_step_on f
  end.

Ltac zify_finz_ty_step_subterm :=
  match goal with
  | H : context [ ?x ] |- _ =>
    lazymatch type of x with finz _ =>
      let X := fresh in
      set (X := x) in *;
      zify_finz_ty_step_on X
    end
  end.

Ltac zify_finz_ty_step :=
  first [ zify_finz_ty_step_var | zify_finz_ty_step_subterm ].

(** zify_finz **)
(* This greedily translates all the address-related terms in the goal and in the
   context. Because each (_ + _) introduces a disjunction, the number of goals
   quickly explodes if there are many (_ + _) in the context.

   The solve_addr tactic below is more clever and tries to limit the
   combinatorial explosion, but zify_addr does not. *)

Ltac zify_finz :=
  intros; solve_finz_cbn;
  repeat (first [ zify_finz_nonbranching_step
                | zify_finz_op_branching_goal_step
                | zify_finz_op_branching_hyps_step ]);
  repeat zify_finz_ty_step; intros.


(** solve_finz *)
(* From a high-level perspective, [solve_finz] is equivalent to [zify_finz]
   followed by [lia].

   However, this gets very slow when there are many (_ + _) in the context (and
   some of those may not be relevant to prove the goal at hand), so the
   implementation is a bit more clever. Instead, we try to call [lia] as soon as
   possible to quickly terminate sub-goals than can be proved before the whole
   context gets translated. *)

Ltac zify_finz_op_goal_step :=
  first [ zify_finz_nonbranching_step
        | zify_finz_op_branching_goal_step ].

Ltac zify_finz_op_deepen :=
  zify_finz_op_branching_hyps_step;
  repeat zify_finz_nonbranching_step;
  try (
    zify_finz_op_branching_hyps_step;
    repeat zify_finz_nonbranching_step
  ).

Ltac solve_finz_close_proof :=
  repeat zify_finz_ty_step; intros;
  solve [ auto | lia | congruence ].

Ltac solve_finz :=
  intros; solve_finz_cbn;
  repeat zify_finz_op_goal_step;
  try solve_finz_close_proof;
  repeat (
    zify_finz_op_deepen;
    try solve_finz_close_proof
  );
  solve_finz_close_proof.

Tactic Notation "solve_finz" := solve_finz.
Tactic Notation "solve_finz" "-" hyp_list(Hs) := clear Hs; solve_finz.
Tactic Notation "solve_finz" "+" hyp_list(Hs) := clear -Hs; solve_finz.

(* --------------------------- TESTS --------------------------------- *)

Goal forall fb (f : finz fb),
    (f + -(f + 3))%f = None.
Proof.
  intros. solve_finz.
Qed.

Goal forall fb (a a' b b' : finz fb),
  (a + 1)%f = Some a' ->
  (b + 1)%f = Some b' ->
  (a + 0)%f = Some a.
Proof.
  intros.
  repeat zify_finz_op_goal_step; [].
  solve_finz_close_proof.
Qed.

Goal forall (word_size : Z) (T : Type) (pid : T) (finz_of : T -> finz word_size),
    (((finz_of pid) ^+ 1) ^+ 1)%f = ((finz_of pid) ^+ 2)%f.
Proof. solve_finz. Qed.

Goal forall fb (f f' : finz fb),
  (f + 15)%f = Some f' →
  finz.of_z (f + 4) = Some (f ^+ 4)%f.
Proof. solve_finz. Qed.

Goal forall (fb : Z) (f : finz fb) (n m : Z),
  (0 <= n)%Z →
  (0 <= m)%Z →
  ((f ^+ n) ^+ m)%f = (f ^+ (n + m)%Z)%f.
Proof. zify_finz;[]. (* only one goal! *) lia. Qed.
