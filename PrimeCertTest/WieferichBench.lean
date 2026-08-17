/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCert.ForallB
import PrimeCert.Wieferich
meta import PrimeCert.Meta.QuickRfl

/-! # Benchmark workload for the Wieferich range check

Each theorem below runs the same 100000-term check over `n ≡ 1 mod 6`. The plain check and the
one skipping multiples of 5 appear twice each, ordered plain, skipping, skipping, plain, so that
the average of each pair sits at the same mean position in the file. The `wieferich-ab` workflow
reports a `[Kernel]` time per declaration.
-/

namespace PrimeCert.Bench

noncomputable def wieferichB (p : Nat) : Bool :=
  powModK 2 (p.sub 1) (Nat.pow p 2) |>.beq 1

noncomputable def mirimanoffB (p : Nat) : Bool :=
  powModK 3 (p.sub 1) (Nat.pow p 2) |>.beq 1

set_option maxRecDepth 4000000
set_option Elab.async false

theorem base_1 : ∀ n < 600000, n % 6 = 1 →
    (wieferichB n).not'.or' (mirimanoffB n).not' :=
  forallB_of_mod _ (start := 1) (len := 100000) (step := 6) (by quickRfl)

theorem filter5_1 : ∀ n < 600000, n % 6 = 1 →
    ((n.mod 5).beq 0).or' ((wieferichB n).not'.or' (mirimanoffB n).not') :=
  forallB_of_mod _ (start := 1) (len := 100000) (step := 6) (by quickRfl)

theorem filter5_2 : ∀ n < 600000, n % 6 = 1 →
    ((n.mod 5).beq 0).or' ((wieferichB n).not'.or' (mirimanoffB n).not') :=
  forallB_of_mod _ (start := 1) (len := 100000) (step := 6) (by quickRfl)

theorem base_2 : ∀ n < 600000, n % 6 = 1 →
    (wieferichB n).not'.or' (mirimanoffB n).not' :=
  forallB_of_mod _ (start := 1) (len := 100000) (step := 6) (by quickRfl)

/-! `n.mod 1` is `0` at every term, so `skip_always` takes the left branch throughout, and
`n.mod 5` is below 5, so `skip_never` takes the right branch throughout. Their two times bound
what the disjunction can save and what the added test costs. -/

theorem skip_always : ∀ n < 600000, n % 6 = 1 →
    ((n.mod 1).beq 0).or' ((wieferichB n).not'.or' (mirimanoffB n).not') :=
  forallB_of_mod _ (start := 1) (len := 100000) (step := 6) (by quickRfl)

theorem skip_never : ∀ n < 600000, n % 6 = 1 →
    ((n.mod 5).beq 7).or' ((wieferichB n).not'.or' (mirimanoffB n).not') :=
  forallB_of_mod _ (start := 1) (len := 100000) (step := 6) (by quickRfl)

end PrimeCert.Bench
