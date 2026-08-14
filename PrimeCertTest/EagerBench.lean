/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCert
import PrimeCert.Meta.QuickRfl

/-! # Benchmark workload for the eager-reduction comparison

A 50000-step `forallB`, which drives the fold's index increment hard enough for the `eager-ab`
workflow to resolve a per-run difference in kernel time.
-/

open PrimeCert

set_option maxRecDepth 1000000 in
example : forallB (fun n ↦ (n.mul 2).ble 400000) 0 50000 := by quickRfl
