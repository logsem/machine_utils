From Coq Require Import ZArith.
From stdpp Require Import base option.
From machine_utils Require Import finz.

(* Helper classes. These are used to support proofsearch for automation (of in
   particular the [solve_pure] tactic). They are not intended to be used
   directly in program specifications or manual proof scripts. *)

(* Reduction helpers *)

Class SimplTC {A} (x x': A) :=
  MkSimplTc: x = x'.

Class CbvTC {A} (x x': A) :=
  MkCbvTc: x = x'.

(* Address arithmetic *)

Class FinZOffsetLt (z z' : Z) := MkFinZOffsetLt: (z < z')%Z.
#[global] Hint Mode FinZOffsetLt + + : typeclass_instances.
Class FinZOffsetLe (z z' : Z) := MkFinZOffsetLe: (z <= z')%Z.
#[global] Hint Mode FinZOffsetLe + + : typeclass_instances.

Class AsWeakFinZIncr {fb} (f f' : finz fb) (z: Z) :=
  MkAsWeakFinZIncr: f = (f' ^+ z)%f.
#[global] Hint Mode AsWeakFinZIncr + ! - - : typeclass_instances.

Class IncrFinZ {fb} (f : finz fb) (z : Z) (f' : finz fb) :=
  MkIncrFinZ: (f + z)%f = Some f'.
#[global] Hint Mode IncrFinZ + + + - : typeclass_instances.

Class FinZLe {fb} (f f' : finz fb) := MkFinZLe: (f <= f')%f.
#[global] Hint Mode FinZLe + + + : typeclass_instances.
Class FinZLt {fb} (f f' : finz fb) := MkFinZLt: (f < f')%f.
#[global] Hint Mode FinZLt + + + : typeclass_instances.

Class FinZEq {fb} (f f' : finz fb) (res : bool) :=
  MkFinZEq: res = true → f = f'.
#[global] Hint Mode FinZEq + + + - : typeclass_instances.

Class ZToFinZ {fb} (z : Z) (f : finz fb) :=
  MkZToFinZ: finz.of_z z = Some f.
#[global] Hint Mode ZToFinZ + ! - : typeclass_instances.
