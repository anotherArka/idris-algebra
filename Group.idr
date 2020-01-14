module Group

import Monoid

interface (Is_monoid ty op) => Is_group (ty : Type) (op : ty -> ty -> ty) where
    inverse : ty -> ty
    proof_of_left_inverse : (a : ty) -> ((op a (inverse a)) = (id_elem {ty = ty} {op = op} ))     
    proof_of_right_inverse : (a : ty) -> ((op (inverse a) a) = (id_elem {ty = ty} {op = op} ))
    
left_cancellation : (Is_group ty op) => (a, b, c : ty) -> ((op a b) = (op a c)) -> (b = c)
left_cancellation {ty} {op} a b c pf_eq = let
    e = id_elem {ty} {op} -- for shortness of writing
    a_inv = inverse {ty} {op} a
    pf_a = proof_of_right_inverse {ty} {op} a -- a_inv * a = id
    pf_1 = proof_of_associativity {ty} {op} a_inv a b -- a_inv * (a * b) = (a_inv * a) * b
    pf_2 = monoid_property_2 {ty} {op} b (op a_inv a) e pf_a -- (a_inv * a) * b = e * b
    pf_3 = proof_of_left_id {ty} {op} b -- e * b = b
    pf_4 = trans pf_1 (trans pf_2 pf_3) -- a_inv * (a * b) = b
    
    pf_5 = proof_of_associativity {ty} {op} a_inv a c -- a_inv * (a * c) = (a_inv * a) * c
    pf_6 = monoid_property_2 {ty} {op} c (op a_inv a) e pf_a -- (a_inv * a) * c = e * c
    pf_7 = proof_of_left_id {ty} {op} c -- e * c = c
    pf_8 = trans pf_5 (trans pf_6 pf_7) -- a_inv * (a * c) = c
    
    pf_9 = monoid_property_1 {ty} {op} a_inv (op a b) (op a c) pf_eq -- a_inv * (a * b) = a_inv * (a * c)
    pf_10 = trans (sym pf_4) (trans pf_9 pf_8) -- b = c 
    in
    pf_10    

