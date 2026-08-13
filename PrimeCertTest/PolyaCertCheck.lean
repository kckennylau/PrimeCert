import Polya.Meta

/-! Runs the whole computation at small arguments, with the prime powers checked against the
certified sieve, and reads the published value off the emitted theorem. -/

set_option maxRecDepth 4000000
set_option Elab.async false

run_sieve 10000
run_polya 1000000 10000

open PrimeCert.Polya in
/-- The running total of the Liouville values at a million. -/
theorem L_million : L 1000000 = -530 := by
  rw [polyaValue]
  norm_num

/-- info: 'L_million' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms L_million
