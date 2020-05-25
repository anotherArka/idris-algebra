module Real_eq

import ZZ
import Useful_functions
import Rational
import Rational_plus
import Rational_abs
import Rational_ord
import Rational_inv
import Rational_implementations
import Cauchy_Real

Eq : Cauchy_Real -> Cauchy_Real -> Type
Eq ps qs = (n : Nat) -> 
  (m : Nat ** 
  ((k : Nat) -> (LTE m k) -> 
  (Rational_ord.LTE (abs ((pick k (fst ps)) - (pick k (fst qs)))) (one, n))))

Eq_is_refl : (ps : Cauchy_Real) -> (Eq ps ps)
Eq_is_refl ps n = (Z ** (\k, pfLTE => let
  pf1 = Rational_inv_pf (pick k (fst ps))
  in
  ?rhs))