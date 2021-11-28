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
universe u
variables {G : Type } [group G]

lemma mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)) := sorry

end monolithic_group
