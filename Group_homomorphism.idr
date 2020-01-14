module Group_homomorphism

import Monoid
import Group

%access public export

interface (Is_group dom op, Is_group cod oq) => 
    Is_group_hom (dom : Type) (op : dom -> dom -> dom) 
                 (cod : Type) (oq : cod -> cod -> cod) 
                 (f : dom -> cod) where
                 
    proof_of_group_hom : (a, b : dom) -> (f(op a b) = (oq (f a) (f b)))
    proof_of_id_transport : ((f (id_elem {ty = dom} {op}) = (id_elem {ty = cod} {op = oq})))
    
||| If f : dom -> cod is a group homomorphism then (f (inv a)) = inv (f a)
group_hom_maps_inverse_to_inverse : (Is_group_hom dom op cod oq f) => (a : dom) 
    -> (f (inverse {ty = dom} {op = op} a) = (inverse {ty = cod} {op = oq} (f a)))
group_hom_maps_inverse_to_inverse {dom} {op} {cod} {oq} {f} a = let
    e_dom = id_elem {ty = dom} {op = op}
    e_cod = id_elem {ty = cod} {op = oq}
    a_inv = inverse {ty = dom} {op = op} a
    f_a_inv = f a_inv
    f_a = f a
    inv_f_a = inverse {ty = cod} {op = oq} (f_a)
    
    pf_1 = proof_of_left_inverse {ty = cod} {op = oq} f_a -- inv_(f a) * (fa) = e_dom
    pf_2 = proof_of_left_inverse {ty = dom} {op = op} a -- a_inv * a = e_dom
    pf_3 = proof_of_group_hom {dom} {op} {cod} {oq} {f} a_inv a -- f (a_inv * a) = (f a_inv) * (f a)
    pf_4 = cong {f = f} pf_2 -- f (a_inv * a) = f (e_dom)
    pf_5 = trans pf_4 (proof_of_id_transport {dom} {op} {cod} {oq} {f}) -- f (a_inv * a) = e_cod
    pf_6 = trans (sym pf_3) pf_5 -- (f a_inv) (f a) = e_cod
    pf_7 = trans pf_1 (sym pf_6) -- inv_(f a) * f_a = (f a_inv) * (f a)  
    pf_8 = right_cancellation {ty = cod} {op = oq} f_a inv_f_a f_a_inv pf_7 -- inv_(f a) = (f a_inv)
      
    in
    (sym pf_8)
