module

import MillerRabin.MetaSpliced

open MillerRabin

set_option maxRecDepth 4000000 in
set_option Elab.async false in
wieferich_cover 2310 1000000
