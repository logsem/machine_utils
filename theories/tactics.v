From iris.proofmode Require Import tactics spec_patterns coq_tactics ltac_tactics reduction.
From iris.base_logic.lib Require Import iprop.
From machine_utils Require Import solve_pure.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option Bool Constr.
Set Default Proof Mode "Classic".

(******************************************************************************)
(* iFrameAuto: configurable auto framing *)

(* Users need to define instances of this class, e.g. for points-to resources. *)
Class FramableMachineResource {Σ: gFunctors} (P: iProp Σ) := {}.
#[export] Hint Mode FramableMachineResource + ! : typeclass_instances.


(* internal classes and instances *)
Class EnvsLookupSpatial {PROP: bi} (Δ: envs PROP) (P: PROP) (i: ident) := {}.
#[export] Hint Mode EnvsLookupSpatial + ! ! - : typeclass_instances.

Instance EnvsLookupSpatial_here (PROP: bi) (Γp Γs: env PROP) P c i :
  EnvsLookupSpatial (Envs Γp (Esnoc Γs i P) c) P i.
Qed.

Instance EnvsLookupSpatial_next (PROP: bi) (Γp Γs: env PROP) P Q c i j :
  EnvsLookupSpatial (Envs Γp Γs c) Q j →
  EnvsLookupSpatial (Envs Γp (Esnoc Γs i P) c) Q j.
Qed.

Class LookupFramableMachineResource {Σ: gFunctors} (G: iProp Σ) (P: iProp Σ) := {}.
#[export] Hint Mode LookupFramableMachineResource + ! - : typeclass_instances.

Instance LookupFramableMachineResource_framable Σ (P: iProp Σ) :
  FramableMachineResource P →
  LookupFramableMachineResource P P.
Qed.

(* TODO: use [TCOr] instead of the two instances below? *)
Instance LookupFramableMachineResource_sep_l Σ (G1 G2 P: iProp Σ) :
  LookupFramableMachineResource G1 P →
  LookupFramableMachineResource (G1 ∗ G2)%I P
| 5.
Qed.

Instance LookupFramableMachineResource_sep_r Σ (G1 G2 P: iProp Σ) :
  LookupFramableMachineResource G2 P →
  LookupFramableMachineResource (G1 ∗ G2)%I P
| 6. (* start looking left *)
Qed.

Instance LookupFramableMachineResource_later Σ (G P: iProp Σ) :
  LookupFramableMachineResource G P →
  LookupFramableMachineResource (▷ G)%I P.
Qed.

Class FramableMachineHyp {Σ} (Δ: envs (uPredI (iResUR Σ))) (G: iProp Σ) (i: ident) := {}.
#[export] Hint Mode FramableMachineHyp + ! ! - : typeclass_instances.
Instance FramableMachineHyp_default Σ (Δ: envs (uPredI (iResUR Σ))) G P i:
  LookupFramableMachineResource G P →
  EnvsLookupSpatial Δ P i →
  FramableMachineHyp Δ G i.
Qed.

Definition framable_machine_hyp `{@FramableMachineHyp Σ Δ P i} := i.

(* the tactic *)
Ltac2 assert_constr_eq (c1: constr) (c2: constr) :=
  match Constr.equal c1 c2 with
  | false => Control.zero Match_failure (* backtrack *)
  | true => ()
  end.

(* Returns the name of the framed assumption (of type [ident]), and the framed
   assumption (of type [iProp Σ]). *)
Ltac2 iFrameAuto () (* : constr * constr *) :=
  lazy_match! goal with
  [ |- envs_entails ?Δ ?p ] =>
    let h := eval unfold framable_machine_hyp in (@framable_machine_hyp _ $Δ $p _ _) in
    let (hname, hh) :=
      match! Δ with context [ Esnoc _ ?h' ?hh ] =>
        assert_constr_eq h h';
        let hname :=
          lazy_match! h with
          | INamed ?s => s
          | IAnon _ => '("?")
          end
        in
        (hname, hh)
      end
    in
    ltac1:(h |- iFrame h) (Ltac1.of_constr h);
    (hname, hh)
  end.

Ltac2 iFrameAuto' () :=
  let _ := iFrameAuto () in ().

Ltac iFrameAuto := ltac2:(iFrameAuto' ()).


(******************************************************************************)
(* iFrameAutoSolve: multi-goal [iFrameAuto || solve_pure] *)

Ltac2 rec grepeat (t: unit -> unit) :=
  ifcatch (fun _ => Control.progress t)
    (fun _ => Control.check_interrupt (); grepeat t) (fun _ => ()).

Ltac2 iFrameAutoSolve () :=
  grepeat (fun _ =>
    try (Control.plus iFrameAuto' (fun _ => Control.once solve_pure))).
Ltac iFrameAutoSolve := ltac2:(iFrameAutoSolve ()).
