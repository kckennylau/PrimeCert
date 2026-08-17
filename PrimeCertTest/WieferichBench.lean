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

Each theorem below runs the same 100000-term check over `n ≡ 1 mod 6`, varying one thing at a
time, so the per-declaration `[Kernel]` times the `wieferich-ab` workflow reports isolate that
one thing.
-/

namespace PrimeCert.Bench

noncomputable def wieferichB (p : Nat) : Bool :=
  powModK 2 (p.sub 1) (Nat.pow p 2) |>.beq 1

/-- The predicate checking modulo `p` before modulo `p ^ 2`. The second conjunct implies the
first, so this agrees with `wieferichB` everywhere. -/
noncomputable def wieferichTwoStage (p : Nat) : Bool :=
  ((powModK 2 (p.sub 1) p).beq 1).and' ((powModK 2 (p.sub 1) (Nat.pow p 2)).beq 1)

noncomputable def mirimanoffB (p : Nat) : Bool :=
  powModK 3 (p.sub 1) (Nat.pow p 2) |>.beq 1

set_option maxRecDepth 4000000

theorem base : ∀ n < 600000, n % 6 = 1 →
    (wieferichB n).not'.or' (mirimanoffB n).not' :=
  forallB_of_mod _ (start := 1) (len := 100000) (step := 6) (by quickRfl)

theorem two_stage : ∀ n < 600000, n % 6 = 1 →
    (wieferichTwoStage n).not'.or' (mirimanoffB n).not' :=
  forallB_of_mod _ (start := 1) (len := 100000) (step := 6) (by quickRfl)

theorem filter5 : ∀ n < 600000, n % 6 = 1 →
    ((n.mod 5).beq 0).or' ((wieferichB n).not'.or' (mirimanoffB n).not') :=
  forallB_of_mod _ (start := 1) (len := 100000) (step := 6) (by quickRfl)

end PrimeCert.Bench
