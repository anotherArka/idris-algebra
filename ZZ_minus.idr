module ZZ_minus

import ZZ
import ZZ_plus
import ZZ_inv

%access public export
%access total

ZZ_minus : ZZ -> ZZ -> ZZ
ZZ_minus a b = ZZ_plus a (ZZ_inv b)