module Rational_inv

import ZZ_implementations
import Rational 

%access public export
%access total

Rational_inv : Rational -> Rational
Rational_inv (a, b) = (-a, b)