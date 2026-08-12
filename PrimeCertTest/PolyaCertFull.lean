import PrimeCert.Meta.Polya

/-! The computation at the smallest counterexample to Pólya's conjecture, with the prime powers
checked against the certified sieve. -/

set_option maxRecDepth 4000000
set_option Elab.async false

run_sieve 936411
run_polya 906150257
