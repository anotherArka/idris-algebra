module Rational_abs

import ZZ_implementations
import Rational
import Rational_plus
import Rational_inv

%access public export
%access total

Rational_abs : Rational -> Rational
Rational_abs (a, b) = (abs a, b)