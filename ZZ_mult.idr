module ZZ_mult

import ZZ

%access public export

ZZ_mult : ZZ -> ZZ -> ZZ
ZZ_mult (a, b) (c, d) = (a*c + b*d, a*d + b*c)

