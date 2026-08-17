/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCert.ForallB
import PrimeCert.Meta.QuickRfl

/-! # Benchmark workload for the two `forallB` shapes

Three shapes folding the same predicate over the same progression, so the `[Kernel]` times the
`forallb-ab` workflow reports differ only in the shape. `forallBPair` carries the running element
beside the accumulated `Bool`, adding `step` once per iteration. `forallBFlat` carries the `Bool`
alone, rebuilding the element as `n * step + start`. `forallBSingle` carries the same one value
with a function-valued motive.
-/

namespace PrimeCert.Bench

/-- The fold carrying the running element beside the accumulator. -/
@[expose] public noncomputable def forallBPair (f : Nat → Bool) (start len step : Nat) : Bool :=
  (Nat.rec (motive := fun _ ↦ Nat × Bool) (start, true)
    (fun _ ih ↦ ih.rec fun i b ↦ (i.add step, f i && b)) len).2

/-- The fold carrying the accumulator alone, rebuilding the element from the index. -/
@[expose] public noncomputable def forallBSingle (f : Nat → Bool) (start len step : Nat) : Bool :=
  Nat.rec (motive := fun _ ↦ Bool → Bool) (fun b ↦ b)
    (fun n r b ↦ r (f ((n.mul step).add start) && b)) len true

/-- The fold carrying the accumulator alone as a plain `Bool`, rebuilding the element from the
recursion index. -/
@[expose] public noncomputable def forallBFlat (f : Nat → Bool) (start len step : Nat) : Bool :=
  Nat.rec (motive := fun _ ↦ Bool) true
    (fun n b ↦ f ((n.mul step).add start) && b) len

set_option maxRecDepth 1000000 in
theorem pair_50000 : forallBPair (fun i ↦ (i.mul 2).ble 700000) 1 50000 6 := by quickRfl

set_option maxRecDepth 1000000 in
theorem flat_50000 : forallBFlat (fun i ↦ (i.mul 2).ble 700000) 1 50000 6 := by quickRfl

set_option maxRecDepth 1000000 in
theorem single_50000 : forallBSingle (fun i ↦ (i.mul 2).ble 700000) 1 50000 6 := by quickRfl

/-! Which end each shape gives up at. The progression runs `1, 7, …, 299995`, and each predicate
below is false at exactly one end of it, so the four times say where the fold stops. -/

set_option maxRecDepth 1000000 in
theorem flat_small_false : (forallBFlat (fun i ↦ (i.beq 1).not) 1 50000 6).not := by quickRfl

set_option maxRecDepth 1000000 in
theorem flat_large_false : (forallBFlat (fun i ↦ (i.beq 299995).not) 1 50000 6).not := by quickRfl

set_option maxRecDepth 1000000 in
theorem single_small_false : (forallBSingle (fun i ↦ (i.beq 1).not) 1 50000 6).not := by quickRfl

set_option maxRecDepth 1000000 in
theorem single_large_false :
    (forallBSingle (fun i ↦ (i.beq 299995).not) 1 50000 6).not := by quickRfl

end PrimeCert.Bench
