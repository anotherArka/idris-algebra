module Rational_inv

import ZZ_implementations
import Rational
import Rational_plus 

%access public export
%access total

Rational_inv : Rational -> Rational
Rational_inv (a, b) = (-a, b)

Rational_inv_pf : (rat : Rational) -> (Rational_Rel (Rational_plus rat (Rational_inv rat)) Rational.zero)
Rational_inv_pf (p, q) = ?rhs1 