module

import MillerRabin.MetaSpliced

open MillerRabin

set_option maxRecDepth 40000 in
set_option Elab.async false in
wieferich_cover 30 10000
