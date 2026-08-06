import PrimeCert.Meta.PolyaCert

/-! Times the check of each packed prime's sieve bit, plus the count of the sieve's set bits. -/

set_option maxRecDepth 4000000
set_option Elab.async false

run_cert_count 100000
