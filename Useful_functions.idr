module Useful_functions

%access public export
%access total

if_then_else : {ty : Type} -> Bool -> ty -> ty -> ty
if_then_else True a b = a
if_then_else False a b = b

Nat_from_Integer : Integer -> Nat
Nat_from_Integer n = assert_total (if_then_else (n == 0) Z
  (if_then_else (n > 0) (S (Nat_from_Integer (n - 1)))
    (Nat_from_Integer (-n))))

pick : {ty : Type} -> (n : Nat) -> (Stream ty) -> ty
pick Z (x :: xs) = x
pick (S n) (x :: xs) = pick n xs    