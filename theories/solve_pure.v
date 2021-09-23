From Coq Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From machine_utils Require Import finz classes class_instances.

From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

(* The [solve_pure] tactic performs proof search to solve pure side-goals. By
   default, it provides some support for finz-related goals, in a way that is
   more restricted that [solve_finz], but is intended to have more predictible
   performance.

   The idea is that [solve_pure] should be fast, both when succeeding and when
   failing.

   The tactic is extensible; it can be extended by adding hints to the
   [solve_pure] hint base.

   Below are hints that handle goals involving:
   - ContiguousRegion
   - SubBounds
   - InBounds
   - (a + z)%a = Some ?
   - finz.of_z (finz.to_z x) = ?

   It also leverages the classes and instances defined in [classes.v] and
   [class_instances.v], but those are not supposed to be used directly in proof
   scripts: it is only expected that [solve_pure] internally generates
   subgoals of these classes during proof search.

   To extend [solve_pure]:
   - only add lemmas in this file if they do not make sense in other files
     (e.g. [finz_lemmas.v], or other files from the development), e.g. they
     involve some internal classes from [classes.v].
   - do register an appropriate [Hint Mode] in the [solve_pure] hint base for
     any new notion you are adding support to.
   - add hints to the [solve_pure] hint base for the relevant lemmas; be mindful
     of proof search performance; do not register hints that could lead to a
     blow up (including cases where the search fails). A typical example would
     be adding a transitivity lemma as a hint.
   - the hints do not necessarily have to live in this file; in particular, it
     is fine to add hints later in the dependency tree in files that *depend*
     on solve_pure.v
   - do add tests (see end of this file for examples) for the kind of goals
     you are adding support to. The tests should generally live in the same file
     where the instances are defined

   Generally speaking, it is important that the tactic is both fast when
   succeeding and when failing.

   /!\ Gotchas /!\:
   - see the "Local context management" section below, regarding handling of
     hypotheses from the local context; add [InCtx] hints if needed.
   - do not add a [Hint Resolve] in [solve_pure] whose conclusion is a class from
     [classes.v]. Register it as an instance instead, otherwise the Hint Modes
     won't work as expected.
*)

(* Local context management

   By default, [typeclasses eauto] will happily use any hypothesis from the
   context to prove the goal, possibly wrongly instantiating evars.

   To prevent that from happening, we first "freeze" the local context by
   wrapping all hypotheses in [InCtx] before calling [typeclasses eauto].
   Then, we have to register explicit hints to use hypotheses from the
   local context, requiring a [InCtx ...].
*)

Class InCtx (P: Prop) := MkInCtx: P.

Ltac freeze_hyps :=
  repeat (match goal with
  | h : ?P |- _ =>
    lazymatch type of P with
    | Prop => idtac
    | _ => fail
    end;
    lazymatch P with
    | InCtx _ => fail
    | _ => idtac
    end;
    change P with (InCtx P) in h
  end).

Ltac unfreeze_hyps :=
  unfold InCtx in *.

(* Proof search features *)

Create HintDb solve_pure discriminated.

(* ContiguousRegion *)
#[export] Hint Mode ContiguousRegion + + - : solve_pure.

Lemma ContiguousRegion_InCtx fb (f : finz fb) z :
  InCtx (ContiguousRegion f z) → ContiguousRegion f z.
Proof. auto. Qed.
#[export] Hint Resolve ContiguousRegion_InCtx : solve_pure.

Instance IncrFinZ_of_ContiguousRegion fb (f : finz fb) z :
  ContiguousRegion f z →
  IncrFinZ f z (f ^+ z)%f.
Proof. intros [? ?]. unfold IncrFinZ. solve_finz. Qed.

Instance IncrFinZ_in_ContiguousRegion fb (a a' : finz fb) (z o z' z'': Z) :
  AsWeakFinZIncr a' a z →
  ContiguousRegion a z'' →
  CbvTC (z + o)%Z z' →
  FinZOffsetLe 0 z →
  FinZOffsetLe 0 o →
  FinZOffsetLe z' z'' →
  IncrFinZ a' o (a ^+ z')%f.
Proof.
  unfold AsWeakFinZIncr, ContiguousRegion, CbvTC, FinZOffsetLe, IncrFinZ.
  intros -> [? ?] <- ? ?. solve_finz.
Qed.

(* SubBounds *)
#[export] Hint Mode SubBounds + + + - - : solve_pure.

Lemma SubBounds_InCtx fb (b e b' e' : finz fb) :
  InCtx (SubBounds b e b' e') → SubBounds b e b' e'.
Proof. auto. Qed.

#[export] Hint Extern 2 (SubBounds _ _ ?b' ?e') =>
  (is_evar b'; is_evar e'; apply SubBounds_InCtx) : solve_pure.

#[export] Hint Extern 0 (SubBounds _ _ ?b' ?e') =>
  (without_evars b'; without_evars e';
   apply SubBounds_InCtx) : solve_pure.

(* Consequences of SubBounds in terms of FinZLe/FinZLt *)

(* TODO: figure out if these hints are actually exercised *)
(* TODO: change these hints to lookup a SubBounds in the local context only *)

Instance SubBounds_le_b_b' fb (b e b' e' : finz fb) :
  SubBounds b e b' e' →
  FinZLe b b'.
Proof. unfold SubBounds, FinZLe. solve_finz. Qed.

Instance SubBounds_le_b'_e' fb (b e b' e' : finz fb) :
  SubBounds b e b' e' →
  FinZLe b' e'.
Proof. unfold SubBounds, FinZLe. solve_finz. Qed.

Instance SubBounds_le_e_e' fb (b e b' e' : finz fb) :
  SubBounds b e b' e' →
  FinZLe e' e.
Proof. unfold SubBounds, FinZLe. solve_finz. Qed.


(* Manually insert the transitive consequences from above, as we don't want to
   have general transitivity instances for FinZLe/FinZLt *)

Instance SubBounds_le_b_e' fb (b e b' e' : finz fb) :
  SubBounds b e b' e' →
  FinZLe b e'.
Proof. unfold SubBounds, FinZLe. solve_finz. Qed.

Instance SubBounds_le_b_e fb (b e b' e' : finz fb) :
  SubBounds b e b' e' →
  FinZLe b e.
Proof. unfold SubBounds, FinZLe. solve_finz. Qed.

Instance SubBounds_le_b'_e fb (b e b' e' : finz fb) :
  SubBounds b e b' e' →
  FinZLe b' e.
Proof. unfold SubBounds, FinZLe. solve_finz. Qed.

(* transitivity to deduce lt of the outer bounds from lt of the inner bounds *)

Instance SubBounds_lt_of_inner fb (b e b' e' : finz fb):
  SubBounds b e b' e' →
  FinZLt b' e' →
  FinZLt b e.
Proof. unfold SubBounds, FinZLt. solve_finz. Qed.

(* InBounds *)

#[export] Hint Mode InBounds + + + + : solve_pure.

#[export] Hint Resolve InBounds_sub : solve_pure.

Lemma InBounds_compare fb (b a e : finz fb) :
  FinZLe b a →
  FinZLt a e →
  InBounds b e a.
Proof. unfold FinZLe, FinZLt, InBounds. auto. Qed.
#[export] Hint Resolve InBounds_compare : solve_pure.

(* IncrFinZ *)

(* This is just a proxy lemma, to then use the Hint Mode of IncrFinZ. The
   intention is that [a] and [z] are known, and that we want to infer [a']. *)
Lemma IncrFinZ_prove fb (a : finz fb) z a' :
  IncrFinZ a z a' →
  (a + z)%f = Some a'.
Proof.
  intros ->. reflexivity.
Qed.
#[export] Hint Resolve IncrFinZ_prove : solve_pure.

Instance IncrFinZ_InCtx fb (a : finz fb) z a' :
  InCtx ((a + z)%f = Some a') → IncrFinZ a z a'.
Proof. auto. Qed.

(* z_to_addr *)

(* Again, we go through a proxy lemma to be able to specify a Hint Mode on z/a
   (see classes.v) *)

Lemma finz_of_z_ZToFinZ fb z (a : finz fb) :
  ZToFinZ z a →
  finz.of_z z = Some a.
Proof. auto. Qed.

#[export] Hint Resolve finz_of_z_ZToFinZ : solve_pure.

(* *)

Ltac2 solve_pure () :=
  first [ assumption
    | discriminate
    | ltac1:(freeze_hyps);
      typeclasses_eauto with solve_pure typeclass_instances;
      ltac1:(unfreeze_hyps) ].

Ltac solve_pure :=
  ltac2:(solve_pure ()).

(* [solve_pure_finz]: solve_pure + hints to call [solve_finz]. Usually slow to
   fail, should only be invoked manually. *)

Create HintDb solve_pure_finz.

Local Ltac hint_solve_finz := unfreeze_hyps; solve_finz.

#[export] Hint Mode SubBounds + + + + + : solve_pure_finz.
#[export] Hint Extern 100 (SubBounds _ _ _ _) => hint_solve_finz : solve_pure_finz.

#[export] Hint Mode InBounds + + + + : solve_pure_finz.
#[export] Hint Extern 100 (InBounds _ _ _) => hint_solve_finz : solve_pure_finz.

#[export] Hint Mode IncrFinZ + + + + : solve_pure_finz.
#[export] Hint Extern 100 (IncrFinZ _ _ _) => hint_solve_finz : solve_pure_finz.

Ltac solve_pure_finz :=
  first [ assumption
    | discriminate
    | freeze_hyps;
      typeclasses eauto with solve_pure solve_pure_finz typeclass_instances;
      unfreeze_hyps ].

(* Tests *)

Goal forall fb (b: finz fb) a (z z': Z),
  ContiguousRegion b z' →
  AsWeakFinZIncr a b z →
  FinZOffsetLt z z' →
  FinZOffsetLe 0 z →
  InBounds b (b ^+ z')%f a.
Proof. intros. typeclasses eauto with solve_pure typeclass_instances. Qed.

Goal forall fb (a: finz fb),
  ContiguousRegion a 5 →
  exists a', IncrFinZ a 1 a' ∧ a' = (a ^+ 1)%f.
Proof. intros. eexists. split. solve_pure. reflexivity. Qed.

Goal forall fb (a: finz fb),
  ContiguousRegion a 5 →
  exists a', IncrFinZ (a ^+ 1)%f 1 a' ∧ a' = (a ^+ 2)%f.
Proof. intros. eexists. split. solve_pure. reflexivity. Qed.

Goal forall fb (a : finz fb), exists a',
  ContiguousRegion a 2 →
  ((a ^+ 1)%f + 1)%f = Some a' ∧ a' = (a ^+ 2)%f.
Proof. intros. eexists. split. solve_pure. reflexivity. Qed.

Goal forall fb (a b c: finz fb),
  (a + b)%f = Some c →
  exists (a b c: finz fb),
  (a + b)%f = Some c.
Proof. intros. do 3 eexists. Fail solve_pure. Abort.

Goal forall fb (a b: finz fb), exists c,
  ContiguousRegion a 5 →
  (a + (b - a))%f = Some c.
Proof. intros. eexists. Fail solve_pure. Abort.

Goal forall fb (a: finz fb) z, exists z' a',
  ContiguousRegion a z →
  IncrFinZ a z' a'.
Proof. intros. do 2 eexists. intros. Fail solve_pure. Abort.

(* Check that the hint corresponding to finz_of_z_to_z does not apply too
   eagerly *)
Goal forall fb, exists a (b : finz fb), finz.of_z a = Some b.
Proof. intros. do 2 eexists. Fail solve_pure. Abort.
