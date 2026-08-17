/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCert.ForallB
import PrimeCert.Meta.QuickRfl

/-! # Benchmark workload for the two `forallB` shapes

`forallBPair` carries the running element beside the accumulated `Bool`, adding `step` once per
iteration. `forallBSingle` carries the accumulator alone and rebuilds the element as
`n * step + start`. Both fold the same predicate over the same progression, so the pair of
`[Kernel]` times reported by the `forallb-ab` workflow differ only in that choice.
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

set_option maxRecDepth 1000000 in
theorem pair_50000 : forallBPair (fun i ↦ (i.mul 2).ble 700000) 1 50000 6 := by quickRfl

set_option maxRecDepth 1000000 in
theorem single_50000 : forallBSingle (fun i ↦ (i.mul 2).ble 700000) 1 50000 6 := by quickRfl

end PrimeCert.Bench
