/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Tactic.NormNum.Prime
import PrimeCert.Pocklington

/-! # List of primes below 1000 -/

namespace PrimeCert

local elab "make%" a:num b:num : command => do
  for i in Array.range' a.getNat b.getNat do
    if Nat.Prime i then
      have iStx := Lean.Syntax.mkNatLit i
      have name := Lean.mkIdent <| Lean.Name.mkSimple s!"prime_{i}"
      Lean.Elab.Command.elabCommand =<< `(command| theorem $name : Nat.Prime $iStx := by norm_num)

set_option trace.profiler true in
set_option trace.profiler.threshold 0 in
make% 2 2000

/-- info: PrimeCert.prime_997 : Nat.Prime 997 -/
#guard_msgs in
#check prime_997

end PrimeCert
