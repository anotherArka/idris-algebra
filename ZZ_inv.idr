module ZZ_inv

import ZZ
import ZZ_plus

%access public export

ZZ_inverse : ZZ -> ZZ
ZZ_inverse (a, b) = (b, a)

proof_of_ZZ_inverse : (a : ZZ) -> (ZZ_Rel ZZ_zero (ZZ_plus a (ZZ_inverse a)))
proof_of_ZZ_inverse (a, b) = plusCommutative b a