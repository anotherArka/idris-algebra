module Rational_mult

import ZZ_implementations
import Rational
import Rational_plus
import Rational_inv

%access public export
%access total

Rational_mult : Rational -> Rational -> Rational
Rational_mult (n1, d1) (n2, d2) = (n1 * n2, d1*d2 + d1 + d2)