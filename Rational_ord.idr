module Rational_ord

import ZZ
import ZZ_ord
import Rational
import Rational_minus

%access public export
%access total

Rational_greater_than_zero : Rational -> Bool
Rational_greater_than_zero (a, b) = ZZ_greater_than_zero a

Rational_strict_order : Rational -> Rational -> Bool
Rational_strict_order a b = Rational_greater_than_zero (Rational_minus a b)

LTZero : Rational -> Type
LTZero (a, b) = LTZero a

LT : Rational -> Rational -> Type
LT a b = LTZero (Rational_minus a b)