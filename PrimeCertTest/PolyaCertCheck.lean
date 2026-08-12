import PrimeCert.Meta.Polya

/-! Runs the whole computation at small arguments, with the prime powers checked against the
certified sieve. -/

set_option maxRecDepth 4000000
set_option Elab.async false

run_sieve 10000
run_polya 1000000 10000
