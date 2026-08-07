import PrimeCert.Meta.PolyaCert

/-! Times the check of each packed prime against its sieve bit and the gap to the next. -/

set_option maxRecDepth 4000000
set_option Elab.async false

run_cert_gap 936411
