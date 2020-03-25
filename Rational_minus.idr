module Rational_minus

import ZZ_implementations
import Rational
import Rational_plus
import Rational_inv

%access public export
%access total

Rational_minus : Rational -> Rational -> Rational
Rational_minus a b = Rational_plus a (Rational_inv b) 