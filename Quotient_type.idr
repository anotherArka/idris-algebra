module Quotient_type

%access public export
%access total

relation_type : (ty : Type) -> Type
relation_type ty = ty -> ty -> Type

interface Quotient_type (ty : Type) (eq : (relation_type ty)) where
    proof_of_refl : (a : ty) -> (eq a a)
    proof_of_sym : (a, b : ty) -> (eq a b) -> (eq b a)
    proof_of_trans : (a, b, c : ty) -> (eq a b) -> (eq b c) -> (eq a c)

interface (Quotient_type ty1 eq1, Quotient_type ty2 eq2) => 
  Quotient_type_function (ty1 : Type) (eq1 : ty1 -> ty1 -> Type)
                           (ty2 : Type) (eq2 : ty2 -> ty2 -> Type)
                           (f : ty1 -> ty2) where
  proof_of_passing_through : (a, b : ty1) -> (eq1 a b) -> (eq2 (f a) (f b))    
