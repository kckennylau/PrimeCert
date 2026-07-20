/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-! # Lemmas destined for Lean core

Definitional `@[simp]` normalisations rewriting the raw `Nat` functions `.mod` and `.div` to
their `%` and `/` notation. Collected as candidates for upstreaming to Lean core.
-/

@[simp] public theorem Nat.mod_eq_mod {a b : Nat} : a.mod b = a % b := rfl
@[simp] public theorem Nat.div_eq_div {a b : Nat} : a.div b = a / b := rfl
