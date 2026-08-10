import PrimeCert.Meta.Polya

/-! The computation at the smallest counterexample to Pólya's conjecture, taking the prime powers as
given, as the arm to compare the checked run against. -/

set_option maxRecDepth 4000000
set_option Elab.async false

run_polya_unchecked 906150257
