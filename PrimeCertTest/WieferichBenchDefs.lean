/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import PrimeCert.ForallB
public import PrimeCert.Wieferich

/-! # Shared definitions for the Wieferich range-check benchmark

One theorem per file sits alongside this one, so each is timed in its own `lean` process and
carries no position within a file. The `wieferich-ab` workflow runs them in a rotated order.
-/

namespace PrimeCert.Bench

@[expose] public noncomputable def wieferichB (p : Nat) : Bool :=
  powModK 2 (p.sub 1) (Nat.pow p 2) |>.beq 1

@[expose] public noncomputable def mirimanoffB (p : Nat) : Bool :=
  powModK 3 (p.sub 1) (Nat.pow p 2) |>.beq 1

/-- The check testing modulo `p` before modulo `p ^ 2`. The second conjunct implies the first,
so this agrees with `wieferichB` everywhere. -/
@[expose] public noncomputable def wieferichTwoStage (p : Nat) : Bool :=
  ((powModK 2 (p.sub 1) p).beq 1).and' ((powModK 2 (p.sub 1) (Nat.pow p 2)).beq 1)

end PrimeCert.Bench
