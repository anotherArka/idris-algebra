module Rational_fromInteger

import ZZ_implementations
import Rational

%access public export
%access total

Rational_fromInteger : Integer -> Rational
Rational_fromInteger n = (fromInteger n, Z)