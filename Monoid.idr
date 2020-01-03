module Monoid

interface Monoid (ty : Type) (op : ty -> ty -> ty) where
    id_elem : ty
    proof_of_left_id : (a : ty) -> ((op a id_elem) = a)
    proof_of_right_id : (a : ty) -> ((op id_elem a) = a)
    proof_of_associativity : (a b c : ty) -> ((op a (op b c)) = (op (op a b) c)) 
