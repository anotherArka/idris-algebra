module Monoid

public export
interface Is_monoid (ty : Type) (op : ty -> ty -> ty) where
    id_elem : ty
    proof_of_right_id : (a : ty) -> ((op a id_elem) = a)
    proof_of_left_id : (a : ty) -> ((op id_elem a) = a)
    proof_of_associativity : (a, b, c : ty) -> ((op a (op b c)) = (op (op a b) c)) 
    
||| b = c => a*b = a*c 
public export   
monoid_property_1 : (Is_monoid ty op) => (a, b, c : ty) -> (b = c) -> ((op a b) = (op a c))
monoid_property_1 a b c pf_eq = cong pf_eq 

||| b = c => b*a = c*a 
public export   
monoid_property_2 : (Is_monoid ty op) => (a, b, c : ty) -> (b = c) -> ((op b a) = (op c a))
monoid_property_2 {op = op} a b c pf_eq = cong {f = \x => (op x a)} pf_eq 
