module ZZ_mult

import ZZ

%access public export

ZZ_mult : ZZ -> ZZ -> ZZ
ZZ_mult (a, b) (c, d) = (a*c + b*d, a*d + b*c)

ZZ_mult_unit_pf : (x : ZZ) -> ((ZZ_mult x ZZ.one) = x)
ZZ_mult_unit_pf (a, b) = rewrite (multCommutative a 0) in 
  (rewrite (multCommutative b 1) in 
  (rewrite (multCommutative b 0) in 
  (rewrite (multCommutative a 1) in 
  (rewrite (plusCommutative a 0) in 
  (rewrite (plusCommutative a 0) in 
  (rewrite (plusCommutative b 0) in Refl))))))

ZZ_mult_commutative : (x, y : ZZ) -> (ZZ_mult x y = ZZ_mult y x)  
ZZ_mult_commutative (a, b) (c, d) = rewrite (multCommutative a c) in 
  (rewrite (multCommutative b d) in 
  (rewrite (multCommutative a d) in
  (rewrite (multCommutative b c) in 
  (rewrite (plusCommutative (c * b) (d * a)) in Refl)))) 
