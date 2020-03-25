module ZZ_abs

import ZZ

%access public export
%access total

ZZ_abs_helper : Nat -> Nat -> ZZ
ZZ_abs_helper n Z = (n, Z)
ZZ_abs_helper Z (S m) = ((S m), Z)
ZZ_abs_helper (S m) (S n) = ZZ_abs_helper m n

ZZ_abs : ZZ -> ZZ
ZZ_abs (a, b) = ZZ_abs_helper a b