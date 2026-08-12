/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public meta import Lean.Elab.Tactic.Basic

/-! # Closing a `Bool` goal by kernel evaluation

`quickRfl` closes a goal of the form `b = true` by assigning `Lean.reflBoolTrue`, so the kernel
evaluates `b`.
-/

open Lean Elab Tactic

/-- Close a goal `b = true` by assigning `Lean.reflBoolTrue`. -/
elab "quickRfl" : tactic => liftMetaFinishingTactic fun g => g.assign reflBoolTrue
