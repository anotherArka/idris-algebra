module Rational_implementations

import Rational
import Rational_plus
import Rational_inv
import Rational_mult
import Rational_minus
-- import ZZ_ord
import Rational_abs
import Rational_fromInteger

%access public export
%access total

Num Rational where
  (+) = Rational_plus
  (*) = Rational_mult  
  fromInteger = Rational_fromInteger

Neg Rational where
  negate = Rational_inv
  (-) = Rational_minus

Abs Rational where
  abs = Rational_abs