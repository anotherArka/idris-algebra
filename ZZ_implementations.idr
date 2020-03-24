module ZZ_implementations

import ZZ
import ZZ_plus
import ZZ_inv

Eq ZZ where
  (==) (a, b) (c, d) = ((a + d) == (b + c))
  