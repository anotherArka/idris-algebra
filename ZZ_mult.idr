module ZZ_mult

import ZZ

ZZ_mult : ZZ -> ZZ -> ZZ
ZZ_mult (a, b) (c, d) = (a*c + b*d, a*d + b*c)

