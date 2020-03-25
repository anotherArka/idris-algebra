module ZZ_implementations

import ZZ
import ZZ_plus
import ZZ_inv
import ZZ_mult
import ZZ_minus
import ZZ_ord
import ZZ_abs

%access public export
%access total

Num ZZ where
  (+) = ZZ_plus
  (*) = ZZ_mult  
  fromInteger = ZZ_from_Integer

Neg ZZ where
  negate = ZZ_inv
  (-) = ZZ_minus

Abs ZZ where
  abs = ZZ_abs