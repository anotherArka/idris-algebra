module ZZ_mult

import ZZ

%access public export

ZZ_mult : ZZ -> ZZ -> ZZ
ZZ_mult (a, b) (c, d) = (a*c + b*d, a*d + b*c)

ZZ_mult_unit_pf : (x : ZZ) -> (ZZ_Rel (ZZ_mult x ZZ.one) x)
ZZ_mult_unit_pf (a, b) = rewrite (multCommutative a 0) in 
  (rewrite (multCommutative b 1) in 
  (rewrite (multCommutative b 0) in 
  (rewrite (multCommutative a 1) in 
  (rewrite (plusCommutative a 0) in 
  (rewrite (plusCommutative a 0) in 
  (rewrite (plusCommutative b 0) in (plusCommutative a b)))))))

