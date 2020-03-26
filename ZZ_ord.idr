module ZZ_ord

import ZZ
import ZZ_minus

%access public export
%access total

ZZ_greater_than_zero_helper : Nat -> Nat -> Bool
ZZ_greater_than_zero_helper Z n = False
ZZ_greater_than_zero_helper (S m) Z = True
ZZ_greater_than_zero_helper (S m) (S n) = ZZ_greater_than_zero_helper m n

LTZero : ZZ -> Type
LTZero (a, b) = LT a b

ZZ_greater_than_zero : ZZ -> Bool
ZZ_greater_than_zero (a, b) = ZZ_greater_than_zero_helper a b

ZZ_strict_order : ZZ -> ZZ -> Bool
ZZ_strict_order a b = ZZ_greater_than_zero (ZZ_minus a b)

LT : ZZ -> ZZ -> Type
LT a b = LTZero (ZZ_minus a b)
