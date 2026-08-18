/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCert.Meta.Wieferich

/-! Emits the class theorems for the mod-2310 wheel over the cached sieve range, and the single
statement quantified over the list of classes. -/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
wieferich_check 2310 1000000
