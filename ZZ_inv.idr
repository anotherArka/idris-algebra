module ZZ_inv

import ZZ
import ZZ_plus

%access public export
%access total

ZZ_inv : ZZ -> ZZ
ZZ_inv (a, b) = (b, a)

proof_of_ZZ_inv : (a : ZZ) -> (ZZ_Rel ZZ_zero (ZZ_plus a (ZZ_inv a)))
proof_of_ZZ_inv (a, b) = plusCommutative b a