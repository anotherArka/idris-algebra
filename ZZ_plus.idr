module ZZ_plus

import ZZ

(+) : ZZ -> ZZ -> ZZ
(a, b) + (c, d) = (a + c, b + d)

ZZ_plusCommutative : (a, b : ZZ) -> ((a + b) = (b + a))
ZZ_plusCommutative (a, b) (c, d) = 
  rewrite (plusCommutative a c) in (rewrite (plusCommutative b d) in Refl)

ZZ_plusAssociative : (a, b, c : ZZ) -> (a + (b + c) = (a + b) + c)
ZZ_plusAssociative (a, b) (c, d) (m, n) = 
  rewrite (plusAssociative a c m) in 
    (rewrite (plusAssociative b d n) in Refl)