module Rational_plus

import ZZ
import ZZ_implementations
import Rational

%access public export
%access total

Rational_plus : Rational -> Rational -> Rational
Rational_plus (n1, d1) (n2, d2) = (
  ((n1 * ((S d1), 0)) + (n2 * ((S d2), 0))),
  (pred ((S d1) * (S d2))))