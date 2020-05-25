module ZZ_abs

import ZZ
import ZZ_ord

%access public export
%access total

ZZ_abs_helper : Nat -> Nat -> ZZ
ZZ_abs_helper n Z = (n, Z)
ZZ_abs_helper Z (S m) = ((S m), Z)
ZZ_abs_helper (S m) (S n) = ZZ_abs_helper m n

ZZ_abs : ZZ -> ZZ
ZZ_abs (a, b) = ZZ_abs_helper a b

ZZ_abs_property_1_helper : (a, b : Nat) -> (LTE ZZ.zero (ZZ_abs (a, b)))
ZZ_abs_property_1_helper n Z = LTEZero
ZZ_abs_property_1_helper Z (S m) = LTEZero
ZZ_abs_property_1_helper (S m) (S n) = ZZ_abs_property_1_helper m n

ZZ_abs_property_1 : (a : ZZ) -> (LTE ZZ.zero (ZZ_abs a))
ZZ_abs_property_1 (a, b) = ZZ_abs_property_1_helper a b