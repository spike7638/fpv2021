-- import .love05_inductive_predicates_demo


/-! # LoVe Demo 12 copy -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Type Classes over a Single Binary Operator

Mathematically, a __group__ is a set `G` with a binary operator `• : G × G → G`
with the following properties, called __group axioms__: ...

In Lean, a type class for groups can be defined as follows: -/

namespace monolithic_group

@[class] structure group (α : Type) :=
(mul          : α → α → α)
(one          : α)
(inv          : α → α)
(mul_assoc    : ∀a b c, mul (mul a b) c = mul a (mul b c))
(one_mul      : ∀a, mul one a = a)
(mul_left_inv : ∀a, mul (inv a) a = one)

#print group

-- I'd like to say "for the next page or so, G denotes agroup." That seems to be 
-- what the next two lines do.

universe u
variables {G : Type } [group G]
-- The [group G] would SEEM to suggest that G is a group, but I can't find anywhere in the manual that explains 
-- this syntax

-- Now I'd like to show that multiplication in a group is associative, presumably using the "mul_assoc" part 
-- of the definintion of a group. 

-- I copied this lemma from mathlib/src/algebra/group/defs.lean, where it's written using an infix "*"
-- instead of "mul", so I swapped in the "mul" form. Unfortunately, "mul" seems to be an unknown identifier, 
-- even though a,b,c are of type G, where G is (I thought) a group. 

-- lemma mul_assoc : ∀ a b c:G , mul (mul a b) c = mul a (mul b c)) := sorry

lemma mul_assoc : ∀ a b c : G, group.mul (group.mul a b) c = group.mul a (group.mul b c) := group.mul_assoc

end monolithic_group

end LoVe
