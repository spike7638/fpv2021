import tactic
import data.real.basic
import data.matrix.notation

local attribute classical.prop_decidable
-- set_option pp.all true

open classical

lemma not_def (a : Prop) :
  ¬ a ↔ a → false :=
by refl

namespace geom
universe u

section affine_geometry
/- 
Page 1: Instead of saying that a line is a set of points, we'll just say that a point is some kind of thing, 
and a line is another kind of thing, and that there's a notion of "P meets n" that tells us that the point
P lies on the line n. If we had lines as "sets of points", then "meets" would just be "element-of", or ∈ . 

It's really helpful to make this abstraction because later, when we've got projective planes, we'll discover
that if we call each line a PPoint, and each point an LLine, and define a new "meets" function, meets2, by saying 
that the PPoint n "meets2" the LLine Q if and only if Q meets n, then PPoints, Llines, and meet2 will turn out 
to be the component parts of a new geometry, called the "dual" of the geometry defined by (Points, Lines, meets).add_key_equivalence

A1 says there's a unique line between distinct points, but because we're going to often want to 
use the line between two points, I'm going to restate that as a requirement that there be a function, 
"join" that consumes a pair of points P and Q and returns a line, k, such that P and Q are both in k. 
That takes care of existence. The thing called join_contains asserts the relevant property. 

For uniqueness ...well, the line through P and Q is unique only in the case where P and Q are distinct. 
So join_unique says that in that case, if P and Q both meet k, then k MUST be "join P Q." So Axiom 1
has turned into the existence of a function satisfying two properties. 

The definition of parallel between A1 and A2 turns into a function that, given two lines, tells whether they're
parallel or not. Actually, "parallel" (the function) is first asserted to exist [or, if you like, required 
to exist if you want to build an affine-geometry structure on some points and lines]. The next three conditions 
say that (1) lines are parallel to themselves, and (2) that if k and n are distinct and parallel, 
then any point on k is NOT a point on n and (3) vice-versa: if k and n have no points in common, then k and n
are parallel. 

Axiom 2 asserts the existence of a unique parallel under certain conditions. Once again, we'll want
to not only know that such a parallel exists, but to be able to name it and work with it, so we 
insist that there's a "find_parallel" function which (see "a2") says that if P lies on a line n parallel to 
k, and if n and k are parallel, then n is exactly "find_parallel P k". (In fact, that's an if-and-only-if.)

Axiom 3 is (thank heavens!) actually almost exactly the same in Hartshorne and in Lean. 

NB: Hartshorne uses the letter "l" to denote lines. I'll almost always avoid this, and use m,n, and k. The 
letter l looks too much like 1 for my comfort. 
 -/

-- out-param is used to simplify 
@[class] structure affine_geom (α : out_param (Type u)) (β  : Type u) :=
(meets           : α → β  → Prop) -- a point P:α is on a line k:β  
(join            : α → α → β)     -- join P Q is the unique line joining P and Q (at least when they're distinct)
(join_contains   : ∀ P Q, (meets P (join P Q))∧ (meets Q (join P Q)))
(join_unique     : ∀ P Q k, ((P ≠ Q) ∧ (meets P k) ∧ (meets Q k)) →  (k = (join P Q)))
(parallel        : β → β → Prop)
(parallel_prop_1 :  ∀ k, parallel k k) 
-- distinct lines that are parallel have no shared points
--(parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (((meets P k) →  ¬ (meets P n)))))
(parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (¬ ((meets P k) ∧ (meets P n)))))
-- lines that have no shared points are parallel. 
(parallel_prop_3 : ∀ k n, (∀ P:α , ((meets P k) →  ¬ (meets P n)) ) → (parallel k n)  ) 
(find_parallel   : α → β → β)     -- given P, k, there a unique line n parallel to k and containing P. that's 'find_parallel P k'
(a2a              : ∀ P k n, ((meets P n ) ∧ (parallel n k)) →  (n = find_parallel P k))
(a2b              : ∀ P k n, (n = find_parallel P k) → ((meets P n ) ∧ (parallel n k)))
(a3              : ∃ P Q R, (((P ≠ Q) ∧ (Q ≠ R) ∧ (P ≠ R)) ∧ (¬ meets P (join Q R)))) -- there are 3 noncollinear pts.

-- I'd like to say "for the next page or so, A denotes an affine geometry." The following line fails to do so
-- I got it by trying to imitate   .../algebra/group/defs, line 72ff
-- variables {A : Type u} [affine_geom A] 

-- #check A
-- -- @[simp, to_additive]
-- -- lemma mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
-- -- group.mul_left_invs

-- lemma parallel_equiv:  setoid A :=
-- { r := parallel,
--   iseqv := sorry
-- }

-- This seems to be what's wanted: I want a geometry to be "the whole structure" rather than just 
-- a set of points...so alpha and beta are types for points and lines, but G is the geometry built atop 
-- those.

variables {α β : Type} [affine_geom α β]
-- That used to say [G: affine_geom α β], but it turns out that NAMING the geometry does something weird 
-- in Lean's lookup for class-instances as Rob explained on 2/4/22. Leaving it unnamed asserts somehow that 
-- there IS an instance of an affine_geom based on types α and β . 
-- When we see something like "meets P k", and P has type α and k has type β,  Lean looks for 
-- an affine_geom structure based on types "α and β " in some table-of-instances, finds this one,
-- and says "Ah...meets must have all the properties specified in the class description." 
-- What about when it sees "parallel n k"? That's trickier -- from n and k it knows only the type
-- β, and that's not enough to use in looking for things in a table indexed by α - β pairs. So
-- under normal circumstances, if we wrote
--      @[class] structure affine_geom (α β  : Type u) :=
-- we'd find that "parallel" had a third, implicit, argument, and to get the particular 
-- "parallel" that we wanted, we'd have to write "parallel α n k". That's a bit ugly, so
-- we used a different set-up:
--     @[class] structure affine_geom (α : out_param (Type u)) (β  : Type u) :=
-- which says "don't bother finding out what α is; just look through the table for something
-- whose second argument is β, and take the first one you find as the "intended" geometry."


include α  --- needed to be sure that lookup on an affine geom can proceed with only β 
-- Again, this requires some explanation; it's best for me to defer to the recording with 
-- Rob from 2/4/22. 
-- But it's also important to "omit α " at times (i.e., to undo this requirement that α be present)

#check affine_geom.parallel_prop_2 
open affine_geom
#check parallel_prop_3 
#check parallel 
#check meets

infix `||` := parallel
precedence `⊸` : 20
infix `⊸` := meets --- tentative icon for "meets"; type \-o to get this icon.


lemma parallel_symmetric:
  symmetric (parallel : β → β → Prop) := 
  begin
    rw [symmetric],
    intro k,
    intro n,
    by_cases k=n,
    {
      intro hp,
      rw h,
      apply parallel_prop_1, 
    },
    intro hpkn,
    have kNEn: k ≠ n := h,
    have ha : (k ≠ n) ∧ (parallel k n) :=  
    begin 
        exact ⟨h, hpkn⟩,
    end,
    have hr: (∀ P : α, (¬ ((affine_geom.meets P k) ∧ (affine_geom.meets P n)))) :=
    begin
      refine affine_geom.parallel_prop_2 k n ha, 
    end,

    have: (parallel  n k) := 
    begin
      refine affine_geom.parallel_prop_3 n k _,
      intro P,
      specialize hr P,
      cc,
    end,
    exact this,
  end
.

lemma parallel_equivalence:
--   equivalence (G.parallel α β)    :=
equivalence (parallel : β → β → Prop)     := 
begin
  repeat { apply and.intro },
  {
    apply parallel_prop_1,
  },
  {
    exact parallel_symmetric,
  },
  {
-- Paraphrasing Hartshorne: "If k = n, there is nothing to prove. If k ≠ n, and there is 
-- a point P on both k and n, then both k and n are parallel to m and pass through P,
-- which is impossible by axiom A2." 
-- (a2              : ∀ P k n, ((meets P n ) ∧ (parallel n k)) ↔ (n = find_parallel P k))
    rw [transitive],
    intros q r s hp1 hp2,
-- If k = n, there is nothing to prove
    by_cases hqs: q = s,
    {
      rw [hqs],
      apply parallel_prop_1,
    },
-- If k ≠ n, 
    {
      apply classical.by_contradiction,
      intro hh,
      have hw := (mt (parallel_prop_3 q s)) hh,
      simp at hw, 
      cases hw with P,
      
      have e1: q = find_parallel P r := 
      begin
        apply (a2a P r q), 
        exact ⟨ hw_h.1, hp1⟩, 
      end,
      have e2: s = find_parallel P r := 
      begin
        apply (a2a P r s),
        exact ⟨ hw_h.2, parallel_symmetric hp2⟩, 
      end,
      have e3: q = s :=
      begin
        rw [e1, e2],
      end,
      exact hqs e3,
    }
  }
end

lemma exists_intersection (n k : β) (hnp : ¬ n || k) : ∃ P : α , meets P n ∧ meets P k
:= begin 
  apply classical.by_contradiction, simp, intro h,
  have hp : n || k := begin apply parallel_prop_3, exact h, end,
  exact hnp hp,
end

-- I do not understand why this is needed...
lemma exists_line (α β : Type) [G : affine_geom α β] : ∃ k : β, k = k :=
begin 
  cases G.a3 with P h, cases h with Q h_2,
  apply exists.intro (join P Q), refl, apply_instance,
end
.


section A2
-- Example. The ordinary plane, known to us from Euclidean geometry, satisfies the axioms A1–A3, and therefore is an affine plane.
-- Recall that an affine plane looks like this:
-- @[class] structure affine_geom (α : out_param (Type u)) (β  : Type u) :=
-- (meets           : α → β  → Prop) -- a point P:α is on a line k:β  
-- (join            : α → α → β)     -- join P Q is the unique line joining P and Q (at least when they're distinct)
-- (join_contains   : ∀ P Q, (meets P (join P Q))∧ (meets Q (join P Q)))
-- (join_unique     : ∀ P Q k, ((P ≠ Q) ∧ (meets P k) ∧ (meets Q k)) →  (k = (join P Q)))
-- (parallel        : β → β → Prop)
-- (parallel_prop_1 :  ∀ k, parallel k k) 
-- --(parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (((meets P k) →  ¬ (meets P n)))))
-- (parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (¬ ((meets P k) ∧ (meets P n)))))
-- (parallel_prop_3 : ∀ k n, (∀ P:α , ((meets P k) →  ¬ (meets P n)) ) → (parallel k n)  ) 
-- (find_parallel   : α → β → β)     -- given P, k, there a unique line n parallel to k and containing P. that's 'find_parallel P k'
-- (a2a              : ∀ P k n, ((meets P n ) ∧ (parallel n k)) →  (n = find_parallel P k))
-- (a2b              : ∀ P k n, (n = find_parallel P k) → ((meets P n ) ∧ (parallel n k)))
-- (a3              : ∃ P Q R, (((P ≠ Q) ∧ (Q ≠ R) ∧ (P ≠ R)) ∧ (¬ meets P (join Q R)))) -- there are 3 noncollinear pts.
--
-- We need to pick α, β, and define the meets, join, and parallel functions, and show
-- that they have the stated properties. The problem here is β: If we think of lines as 
-- solutions to equations of the form Ax + By + C = 0, then the line (A,B,C) is "the same"
-- as the line (3A, 3B, 3C). So there's an equivalence relation hidden in here. Also, there's a 
-- constraint: A and B cannot both be zero (i.e., our "type" is not all of R^3, but instead is R^3 except
-- for the z-axis). So we've got some proving to do even in setting up β. 
--
-- First step: define the type for line-coefficients (whose quotient will be β)
omit α 


def Y := { v : fin 3 → ℝ // (v 0 ≠ 0) ∨  (v 1 ≠ 0) }
#check Y


lemma one_over (x : ℝ ): x ≠ 0 → (1/x * x) = 1 :=
div_mul_cancel 1

lemma assoc (a b c : ℝ) : (a * b) *c = a * (b * c) := mul_assoc a b c

@[instance] def a2.rel : setoid(Y) := 
{r := λ k n : Y, ∃ t: ℝ, (t ≠ 0) ∧ (k.val 0) = t* (n.val 0) ∧ 
(k.val  1) = t* (n.val 1) ∧ (k.val 2) = t*(n.val 2),
iseqv := 
  begin
    repeat { apply and.intro },
    {
      intro h,
      have hinst: ( (1:ℝ)  ≠ (0:ℝ)) ∧ (h.val 0) = 1* (h.val 0) ∧ 
(h.val  1) = 1* (h.val 1) ∧ (h.val 2) = 1*(h.val 2) := by simp,
     exact exists.intro 1 hinst,
    },
    {
      intro h,
      intro y,
      intro p,
      cases p with s ps,
      have hs0: (s:ℝ)  ≠ (0:ℝ) := by exact ps.1,
      have h00: ((1:ℝ) /s) ≠ (0:ℝ) := by exact one_div_ne_zero hs0,
      have h0: ((1:ℝ)/s) * h.val 0 = y.val 0 := 
      begin
        rw  [ps.2.1],
        rw tactic.ring.mul_assoc_rev (1/s) s (y.val 0),
        have hi: (1/s * s = 1) := one_over s hs0,
        rw [hi],
        simp,
      end,
      have h1: ((1:ℝ)/s) * h.val 1 = y.val 1 := 
      begin
        rw  [ps.2.2.1],
        rw tactic.ring.mul_assoc_rev (1/s) s (y.val 1),
        have hi: (1/s * s = 1) := one_over s hs0,
        rw [hi],
        simp,
      end,
      have h2: ((1:ℝ)/s) * h.val 2 = y.val 2 := 
      begin
        rw  [ps.2.2.2],
        rw tactic.ring.mul_assoc_rev (1/s) s (y.val 2),
        have hi: (1/s * s = 1) := one_over s hs0,
        rw [hi],
        simp,
      end,
      have h0r: y.val 0 = ((1:ℝ)/s) * h.val 0 := eq.symm h0,
      have h1r: y.val 1 = ((1:ℝ)/s) * h.val 1 := eq.symm h1,
      have h2r: y.val 2 = ((1:ℝ)/s) * h.val 2 := eq.symm h2,
      have hB: ((1:ℝ)/s) ≠ 0 ∧ y.val 0 = ((1:ℝ)/s) * h.val 0 ∧ y.val 1 = ((1:ℝ)/s) * h.val 1 ∧ y.val 2 = ((1:ℝ)/s) * h.val 2 :=
      begin
        by tauto,
      end,
      exact exists.intro ((1:ℝ)/s) hB,
    },
    {
      intros x y z,
      intros h1 h2,
      cases h1 with s ps,
      cases h2 with r pr,
      have hs0: s ≠ 0 := ps.1,
      have hr0: r ≠ 0 := pr.1,
      have ht: s*r ≠ (0:ℝ) := mul_ne_zero hs0 hr0,
      have hz0: x.val 0 = (s*r) * z.val 0 := begin 
        have u: x.val 0 = s * y.val 0 := ps.right.left,
        have v: y.val 0 = r * z.val 0 := pr.right.left,
        rw [v] at u,
        have w: s * r * z.val 0 = s * (r * z.val 0) :=  assoc s r (z.val 0),
        exact (rfl.congr (eq.symm w)).mp u,
      end,
      have hz1: x.val 1 = (s*r) * z.val 1 := begin 
        have u: x.val 1 = s * y.val 1 := ps.2.2.1,
        have v: y.val 1 = r * z.val 1 := pr.2.2.1,
        rw [v] at u,
        have w: s * r * z.val 1 = s * (r * z.val 1) :=  assoc s r (z.val 1),
        exact (rfl.congr (eq.symm w)).mp u,
      end,
      have hz2: x.val 2 = (s*r) * z.val 2 := begin 
        have u: x.val 2 = s * y.val 2 := ps.2.2.2,
        have v: y.val 2 = r * z.val 2 := pr.2.2.2,
        rw [v] at u,
        have w: s * r * z.val 2 = s * (r * z.val 2) :=  assoc s r (z.val 2),
        exact (rfl.congr (eq.symm w)).mp u,
      end,
      have hC: (s*r) ≠ 0 ∧ x.val 0 = (s*r) * z.val 0 ∧ x.val 1 = (s*r) * z.val 1 ∧ x.val 2 = (s*r) * z.val 2 :=
      begin
        tauto,
      end,
      exact exists.intro (s*r) hC,
    }
  end
}

-- To do: meets, join, parallel, find-parallel

-- code from defining Z as a quotient of N x N to use as an example
-- @[instance] def int.rel : setoid (ℕ × ℕ) :=
-- { r     :=
--     λpn₁ pn₂ : ℕ × ℕ,
--       prod.fst pn₁ + prod.snd pn₂ = prod.fst pn₂ + prod.snd pn₁,
--   iseqv :=
--     begin
--       repeat { apply and.intro },
--       { intro pn,
--         refl },
--       { intros pn₁ pn₂ h,
--         rw h },
--       { intros pn₁ pn₂ pn₃ h₁₂ h₂₃,
--         linarith }
--     end }


-- lemma int.rel_iff (pn₁ pn₂ : ℕ × ℕ) :
--   pn₁ ≈ pn₂ ↔
--   prod.fst pn₁ + prod.snd pn₂ = prod.fst pn₂ + prod.snd pn₁ :=
-- by refl

-- def int : Type :=
-- quotient int.rel

-- def int.zero : int :=
-- ⟦(0, 0)⟧

-- lemma int.zero_eq (m : ℕ) :
--   int.zero = ⟦(m, m)⟧ :=
-- begin
--   rw int.zero,
--   apply quotient.sound,
--   rw int.rel_iff,
--   simp
-- end

-- def int.add : int → int → int :=
-- quotient.lift₂
--   (λpn₁ pn₂ : ℕ × ℕ,
--      ⟦(prod.fst pn₁ + prod.fst pn₂,
--        prod.snd pn₁ + prod.snd pn₂)⟧)
--   begin
--     intros pn₁ pn₂ pn₁' pn₂' h₁ h₂,
--     apply quotient.sound,
--     rw int.rel_iff at *,
--     linarith
--   end

-- lemma int.add_eq (p₁ n₁ p₂ n₂ : ℕ) :
--   int.add ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ = ⟦(p₁ + p₂, n₁ + n₂)⟧ :=
-- by refl

-- lemma int.add_zero (i : int) :
--   int.add int.zero i = i :=
-- begin
--   apply quotient.induction_on i,
--   intro pn,
--   rw int.zero,
--   cases' pn with p n,
--   rw int.add_eq,
--   apply quotient.sound,
--   simp
-- end



end A2

-- Proposition 1.2 Two distinct lines have at most one point in common.
-- For if l, m both pass through two distinct points P, Q, then by axiom A1,
-- l = m.

lemma one_shared_point (r s: β) (P Q: α ) [G: (affine_geom α β) ]: 
r ≠ s ∧ 
 (P ⊸ r) ∧ affine_geom.meets P s ∧ 
affine_geom.meets Q r ∧ affine_geom.meets Q s → 
P = Q :=
begin
  intro h1,
  apply classical.by_contradiction,
  intro hPneQa,
  have hPneQ: P ≠ Q := begin exact hPneQa, end,
  have hrs: r ≠ s := h1.1,
  have hPr: affine_geom.meets P r := (h1.2).1,
  have hPs: affine_geom.meets P s := (h1.2).2.1,
  have hQr: affine_geom.meets Q r := (h1.2).2.2.1,
  have hQs: affine_geom.meets Q s := (h1.2).2.2.2,
  -- (join_unique     : ∀ P Q k, ((P ≠ Q) ∧ (meets P k) ∧ (meets Q k)) →  (k = (join P Q)))
  have hru:  ((P ≠ Q) ∧ (affine_geom.meets P r) ∧ (affine_geom.meets Q r)) := by tauto,    
  have hrru:  r = affine_geom.join P Q := by apply (affine_geom.join_unique P Q r hru),
  have hsu:  ((P ≠ Q) ∧ (affine_geom.meets P s) ∧ (affine_geom.meets Q s)) := by tauto,
  have hssu:  s = affine_geom.join P Q := by apply (affine_geom.join_unique P Q s hsu),
  have hreqs: r = s :=by rw [hrru, hssu],
  exact hrs hreqs,
end
.

lemma one_shared_line (r s: β) (P Q: α ) [affine_geom α β]: 
P ≠ Q ∧ 
affine_geom.meets P r ∧ affine_geom.meets P s ∧ 
affine_geom.meets Q r ∧ affine_geom.meets Q s → 
r = s :=
begin
  intro h1,
  apply classical.by_contradiction,
  intro hrnesa,
  have hrnes: r ≠ s := begin exact hrnesa, end,
  have hPQ: P ≠ Q := h1.1,
  have hPr: affine_geom.meets P r := (h1.2).1,
  have hPs: affine_geom.meets P s := (h1.2).2.1,
  have hQr: affine_geom.meets Q r := (h1.2).2.2.1,
  have hQs: affine_geom.meets Q s := (h1.2).2.2.2,
  -- (join_unique     : ∀ P Q k, ((P ≠ Q) ∧ (meets P k) ∧ (meets Q k)) →  (k = (join P Q)))
  have hru:  ((P ≠ Q) ∧ (affine_geom.meets P r) ∧ (affine_geom.meets Q r)) := begin 
    cc,    
  end,
  have hrru:  r = affine_geom.join P Q :=
  begin
    apply (affine_geom.join_unique P Q r hru),
  end, 
  have hsu:  ((P ≠ Q) ∧ (affine_geom.meets P s) ∧ (affine_geom.meets Q s)) := begin 
    cc,    
  end,
  have hssu:  s = affine_geom.join P Q :=
  begin
    apply (affine_geom.join_unique P Q s hsu),
  end, 
  have hreqs: r = s :=
  begin
    rw [hrru, hssu],
  end,
  exact hrnes hreqs,
end
.
lemma join_contains_left (P Q:α): meets P ((join P Q):β) := (join_contains P Q).left
lemma join_contains_right (P Q:α): meets Q ((join P Q):β) := (join_contains P Q).right

lemma equal_joins (P Q R S:α) (hPQ : P ≠ Q) (hRS : R ≠ S) [affine_geom α β]: meets R ((join P Q):β) ∧ meets S ((join P Q):β) → join R S = ((join P Q):β)  :=
begin
  have h1: R ≠ S ∧ 
meets R ((join P Q):β)  ∧ meets R ((join R S):β)  ∧ 
meets S ((join P Q):β) ∧ meets S ((join R S):β) → 
((join P Q):β)  = ((join R S):β) := begin
  apply (one_shared_line ((join P Q):β) ((join R S):β) R S),
end,
  simp [hRS] at h1,
  have h2: meets R ((join R S):β) ∧ meets S ((join R S):β) := (join_contains R S),
  intro hm,
  apply (one_shared_line (join R S) (join P Q) R S),
  simp [hRS],
  exact ⟨ h2.1, hm.1, h2.2, hm.2⟩ ,
  exact _inst_1, -- this feels really disgusting...not sure why I should have to do this.
end

lemma same_joins [G : (affine_geom α β)]:
∀ P  Q  R:α ,∀ m:β , (P ≠ Q ∧  P ≠ R ∧  Q ≠ R ∧ (m = affine_geom.join P Q) ∧ (affine_geom.meets R m)) → (affine_geom.join Q R = m) :=
begin
intros P Q R m h,
have hPQ: P ≠ Q := h.1,
have hPR: P ≠ R := h.2.1,
have hQR: Q ≠ R := h.2.2.1,
have hm: m = affine_geom.join P Q := h.2.2.2.1,
have hmeets: affine_geom.meets R m := h.2.2.2.2,
clear h,
-- line PQ contains P, R, so it's join P R
-- line PQ is just m, so m is join P R. 
let PQ : β := affine_geom.join P Q,
have hPQ : PQ = affine_geom.join P Q := rfl,
have RPQ: affine_geom.meets R PQ := by cc,
have QPQa: affine_geom.meets P PQ ∧ affine_geom.meets Q PQ := 
begin
  apply affine_geom.join_contains P Q,
end,
have QPQ: affine_geom.meets Q PQ := QPQa.2,

let QR : β := affine_geom.join Q R,
have hQR : QR = affine_geom.join Q R := rfl,
have hz : affine_geom.meets Q QR ∧ affine_geom.meets R QR :=
begin
  apply affine_geom.join_contains,
end,
have QQR: affine_geom.meets Q QR := hz.1,
have RQR: affine_geom.meets R QR := hz.2,
apply eq.symm,
rw hm,
apply (affine_geom.join_unique Q R PQ),
tauto,
end
.
#check same_joins

lemma join_symm [G : (affine_geom α β)]: ∀ A B:α,  ((affine_geom.join A B):β)   = (affine_geom.join B A) := 
begin
  intros A B,
  by_cases A = B,
  {
    rw [h],
  },
  {
    have hAB: (affine_geom.meets A (affine_geom.join A B)) ∧ (affine_geom.meets B (affine_geom.join A B)) := (affine_geom.join_contains A B),
    have hBA: (affine_geom.meets B (affine_geom.join B A)) ∧ (affine_geom.meets A (affine_geom.join B A)) := (affine_geom.join_contains B A),
    have AAB: (affine_geom.meets A ((affine_geom.join A B):β )) := hAB.1,
    have BAB: (affine_geom.meets B ((affine_geom.join A B):β) ) := hAB.2,
    have ABA: (affine_geom.meets A (affine_geom.join B A)) := hBA.2,
    have BBA: (affine_geom.meets B (affine_geom.join B A)) := hBA.1,
    have qA:  (affine_geom.meets A ((affine_geom.join A B):β)) ∧ (affine_geom.meets A ((affine_geom.join B A):β ))  :=
    begin
      apply and.intro AAB ABA,
    end,
    have qB:  (affine_geom.meets B ((affine_geom.join A B):β)) ∧ (affine_geom.meets B ((affine_geom.join B A):β ))  :=
    begin
      apply and.intro BAB BBA,
    end,
    have q: (A ≠ B) ∧ (affine_geom.meets A ((affine_geom.join A B):β )) ∧ (affine_geom.meets A ((affine_geom.join B A):β )) ∧ 
                   (affine_geom.meets B ((affine_geom.join A B):β )) ∧ (affine_geom.meets B ((affine_geom.join B A):β )) :=
    begin
      simp [h],
      simp [qA, qB],
    end,
    apply (one_shared_line ((affine_geom.join A B):β ) ((affine_geom.join B A):β ) A B),
    exact q,
  }
end

.
-- Four points, as done by Dhruv (and finished up by Spike)
lemma four_points_dhruv [G : (affine_geom α β)]:
∃ P Q R S : α,  P ≠ Q ∧  P ≠ R ∧  P ≠ S ∧  Q ≠ R ∧ Q ≠ S ∧ R ≠ S :=
begin
  cases G.a3 with P h3_1, cases h3_1 with Q h3_2, cases h3_2 with R h3_3,
  have hPnotQR: ¬affine_geom.meets P (affine_geom.join Q R) := h3_3.2,
  let QR : β := affine_geom.join Q R,
  let l : β := affine_geom.find_parallel P QR,
  have hQR : QR = affine_geom.join Q R := rfl, 
  have hl : l = affine_geom.find_parallel P QR := rfl,
  rw ← hQR at *,

  let PQ : β := affine_geom.join P Q,
  let m : β := affine_geom.find_parallel R PQ,
  have hPQ : PQ = affine_geom.join P Q := rfl,
  have hm : m = affine_geom.find_parallel R PQ := rfl,
  rw ← hPQ at *,

  have hmnl : ¬ affine_geom.parallel α m l :=
  begin 
    intro hml,
    have hPQpQR : affine_geom.parallel α PQ QR :=
    begin 
      apply parallel_equivalence.2.2, -- transitivity
      {exact parallel_equivalence.2.1 (affine_geom.a2b R PQ m hm).2,},
      {apply parallel_equivalence.2.2,
      {exact hml,},
      {exact (affine_geom.a2b P QR l hl).2}},
    end,
    have hPQnQR : PQ ≠ QR :=
    begin 
      intro h, have := (affine_geom.join_contains P Q).1, rw ← hPQ at *, rw h at this,
      exact h3_3.2 this,
    end,
    have hQmeet : ((affine_geom.meets Q PQ) ∧ (affine_geom.meets Q QR)) :=
    begin
      split,
      {rw hPQ, exact (affine_geom.join_contains P Q).2,},
      {rw hQR, exact (affine_geom.join_contains Q R).1,},
    end,
    exact (affine_geom.parallel_prop_2 PQ QR ⟨hPQnQR, hPQpQR⟩ Q) hQmeet,
  end,
  
  have heS : ∃ S : α , affine_geom.meets S m ∧ affine_geom.meets S l :=
  begin 
    apply classical.by_contradiction, simp, intro h,
    exact hmnl (affine_geom.parallel_prop_3 m l h),
  end,
  cases heS with S hS,

  apply exists.intro P, apply exists.intro Q, apply exists.intro R, apply exists.intro S,
  repeat {split}, exact h3_3.1.1, 
  exact h3_3.1.2.2,
  {  
-- Since S lies on m, which is parallel to P Q, and different from P Q, S does not lie on
-- P Q, so S != P...
    begin
      have hs1: affine_geom.meets S m := hS.1,
      have hmpq1: (affine_geom.meets R m)∧ (affine_geom.parallel α m PQ) := begin
        apply (affine_geom.a2b R PQ m hm),
      end,
      have hmpqr: (affine_geom.parallel α m PQ) := hmpq1.2,

-- show R is on m
      have hmPQ: ¬ (m = PQ) := 
      have hRma: affine_geom.meets R m  ∧ affine_geom.parallel α m PQ:=
      begin
        apply (affine_geom.a2b R PQ m),
        exact hm,
      end,
      have hRm: affine_geom.meets R m := by exact(hRma.1),
-- Show R is not on PQ (else they'd be collinear)
      have hRnPQ: ¬ affine_geom.meets R PQ :=
        assume hhRPQ: affine_geom.meets R PQ,
        show false, from
        begin
          have PQQR: affine_geom.join Q R = PQ := 
          begin
            apply (same_joins P Q R PQ),
            simp [h3_3.1],
            exact hhRPQ,
          end,
          have hQPQa: affine_geom.meets (P:α) ((affine_geom.join P (Q:α )):β)  ∧ affine_geom.meets Q ((affine_geom.join P Q):β) :=
          begin
            apply (affine_geom.join_contains P Q),
          end,
          have hPPQa: affine_geom.meets P ((affine_geom.join P Q):β) := hQPQa.1,
          have hPQa:  affine_geom.join P Q = PQ := by simp, 
          have hPPQ: affine_geom.meets P (PQ:β) := hQPQa.1,
          have hPPQ: affine_geom.meets P (QR:β) := by cc,
          have hnPPq: ¬ affine_geom.meets P (QR:β) := h3_3.2,
          cc,
        end,
--         same_joins [G : (affine_geom α β)]:
-- ∀ P  Q  R:α ,∀ m:β , (P ≠ Q ∧  P ≠ R ∧  Q ≠ R ∧ (m = affine_geom.join P Q) ∧ (affine_geom.meets R m)) → (affine_geom.join Q R = m) :=

-- if m = PQ, we've get R is on PQ. contradition
-- hence m <> PQ, and m || PQ, so they share no points
-- S is on m, and P is on PQ
-- suppose S = P; then m and PQ share a point. Contradiction.
-- hence S <> P. Whew!

      assume hh: m = PQ, --contradiction hyp
      show false, from
      begin
        -- R is on m
        have hRmz: (affine_geom.meets R m) ∧ (affine_geom.parallel α m PQ):=
        begin
          apply (affine_geom.a2b R PQ m),
          exact hm,
        end,
        have hRm: (affine_geom.meets R m) := hRmz.1,
        -- R is not on PQ [done" hPnotQR]
        have hRm: (affine_geom.meets R PQ) := 
        begin
          rw hh at hRm,
          exact hRm,
        end,
        tauto,
      end,
-- hence m <> PQ (above) and m || PQ, 
-- so they share no points
-- S is on m, and P is on PQ
-- suppose S = P; then m and PQ share a point. Contradiction.
-- hence S <> P. Whew!
      have hmPQz: affine_geom.meets R m ∧ affine_geom.parallel α m PQ :=
      begin
        apply (affine_geom.a2b R PQ m),
        exact hm,
        -- (a2b              : ∀ P k n, (n = find_parallel P k) → ((meets P n ) ∧ (parallel n k)))
      end,
      have hmPQy: affine_geom.parallel α m PQ := hmPQz.2,
-- hence m <> PQ and m || PQ (above)
-- so they share no points
      have hh: (m ≠ PQ ∧ affine_geom.parallel α  m PQ) :=
      begin
        simp [hmPQ, hmPQy],
      end, 
      have hnosharemPQ: ∀ X:α, ¬ ((affine_geom.meets X m) ∧ (affine_geom.meets X PQ)) := 
      begin
        apply (affine_geom.parallel_prop_2 m PQ hh),
      end,
-- S is on m, and P is on PQ
      have h1: ¬ ((affine_geom.meets S m) ∧ (affine_geom.meets S PQ)) := (hnosharemPQ S),
      simp [hs1] at h1,
      have h2z: (affine_geom.meets P PQ) ∧ (affine_geom.meets Q PQ) := (affine_geom.join_contains P Q),
      have h2: (affine_geom.meets P PQ) := h2z.1,
-- suppose S = P; then m and PQ share a point. Contradiction.
      assume hC: P = S,
      show false, from
      begin
        simp [hC] at h2,
        tauto,
      end,
-- hence S <> P. Whew!
    end
  },
  exact h3_3.1.2.1,
  {  
-- Since S lies on m, which is parallel to P Q, and different from P Q, S does not lie on
-- P Q, so S != P...
    begin
      have hs1: affine_geom.meets S m := hS.1,
      have hmpq1: (affine_geom.meets R m)∧ (affine_geom.parallel α m PQ) := begin
        apply (affine_geom.a2b R PQ m hm),
      end,
      have hmpqr: (affine_geom.parallel α m PQ) := hmpq1.2,
      --==========================================================
      have hmPQ: ¬ (m = PQ) := 
      have hRma: affine_geom.meets R m  ∧ affine_geom.parallel α m PQ:=
      begin
        apply (affine_geom.a2b R PQ m),
        exact hm,
      end,
      have hRm: affine_geom.meets R m := by exact(hRma.1),
-- Show R is not on PQ (else they'd be collinear)
      have hRnPQ: ¬ affine_geom.meets R PQ :=
        assume hhRPQ: affine_geom.meets R PQ,
        show false, from
        begin
          have PQQR: affine_geom.join Q R = PQ := 
          begin
            apply (same_joins P Q R PQ),
            simp [h3_3.1],
            exact hhRPQ,
          end,
          have hQPQa: affine_geom.meets (P:α) ((affine_geom.join P (Q:α )):β)  ∧ affine_geom.meets Q ((affine_geom.join P Q):β) :=
          begin
            apply (affine_geom.join_contains P Q),
          end,
          have hPPQa: affine_geom.meets P ((affine_geom.join P Q):β) := hQPQa.1,
          have hPQa:  affine_geom.join P Q = PQ := by simp, 
          have hPPQ: affine_geom.meets P (PQ:β) := hQPQa.1,
          have hPPQ: affine_geom.meets P (QR:β) := by cc,
          have hnPPq: ¬ affine_geom.meets P (QR:β) := h3_3.2,
          cc,
        end,
--         same_joins [G : (affine_geom α β)]:
-- ∀ P  Q  R:α ,∀ m:β , (P ≠ Q ∧  P ≠ R ∧  Q ≠ R ∧ (m = affine_geom.join P Q) ∧ (affine_geom.meets R m)) → (affine_geom.join Q R = m) :=

-- if m = PQ, we've get R is on PQ. contradition
-- hence m <> PQ, and m || PQ, so they share no points
-- S is on m, and P is on PQ
-- suppose S = P; then m and PQ share a point. Contradiction.
-- hence S <> P. Whew!

      assume hh: m = PQ, --contradiction hyp
      show false, from
      begin
        -- R is on m
        have hRmz: (affine_geom.meets R m) ∧ (affine_geom.parallel α m PQ):=
        begin
          apply (affine_geom.a2b R PQ m),
          exact hm,
        end,
        have hRm: (affine_geom.meets R m) := hRmz.1,
        -- R is not on PQ [done" hPnotQR]
        have hRm: (affine_geom.meets R PQ) := 
        begin
          rw hh at hRm,
          exact hRm,
        end,
        tauto,
      end,
      --==========================================================
      -- (parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (¬ ((meets P k) ∧ (meets P n)))))
      have hsnotPQa: ¬ (affine_geom.meets S m ∧ affine_geom.meets S PQ) := 
      begin
        apply (affine_geom.parallel_prop_2 m PQ),
        tauto,
      end,
      have hsnotPQ: ¬ affine_geom.meets S PQ := by cc,
      have hPPQa: (affine_geom.meets P PQ) ∧ (affine_geom.meets Q PQ) := begin
        apply affine_geom.join_contains P Q,
      end,
      have hPPq: (affine_geom.meets Q PQ) := by exact hPPQa.2,
      show (¬ Q = S),
      assume hh: Q = S,
      show false, from
      begin
        rw hh at hPPq,
        cc,
      end,
  end,  
  },
  {  
-- Since S lies on l, which is parallel to Q R, and different from QR, S does not lie on QR
-- But R DOES lie in QR, so S != R...
    begin
      have hs1: affine_geom.meets S l := hS.2,
      have hlqr1: (affine_geom.meets P l) ∧ (affine_geom.parallel α l QR) := begin
        apply (affine_geom.a2b P QR l hl), 
      end,

      have hlqrZ: (affine_geom.parallel α l QR) := hlqr1.2,
      have hlQR: ¬ (l = QR) := 
        have hPla: affine_geom.meets P l  ∧ affine_geom.parallel α l QR:=
        begin
          apply (affine_geom.a2b P QR l),
          exact hl,
        end,
        have hPl: affine_geom.meets P l := by exact(hPla.1),
-- Show P is not on QR (else they'd be collinear)
        have hPnQR: ¬ affine_geom.meets P QR :=
          assume hhPQR: affine_geom.meets P QR,
          show false, from
          begin
            have PQQR: affine_geom.join Q P = QR := 
            begin
              apply (same_joins R Q P QR),
            -- ∀ R  P  Q:α ,∀ m:β , (R ≠ P ∧  R ≠ Q ∧  P ≠ Q ∧ (m = affine_geom.join R P) ∧ (affine_geom.meets Q m)) → (affine_geom.join P Q = m) :=
              have k1: ¬ R = P := begin
                exact id (λ (ᾰ : R = P), false.rec false (hPnotQR hhPQR)),
              end,
              have k2: ¬ R = Q := begin
                exact id (λ (ᾰ : R = Q), false.rec false (hPnotQR hhPQR)),
              end,
              have k3: ¬ Q = P:= 
              begin
                exact id (λ (ᾰ : Q = P), false.rec false (hPnotQR hhPQR)),
              end,
              simp [k1, k2, k3],
              simp [hhPQR],
              have hQRRQ: affine_geom.join Q R = affine_geom.join R Q :=
              begin
                have h1: (affine_geom.meets Q ((affine_geom.join Q R):β) )∧ (affine_geom.meets R ((affine_geom.join Q R):β)) := begin
                  apply (affine_geom.join_contains Q R),
                end,
                have h2: (affine_geom.meets R ((affine_geom.join R Q):β) )∧ (affine_geom.meets Q ((affine_geom.join R Q):β)) := begin
                  apply (affine_geom.join_contains R Q),
                end,
                have j1: (affine_geom.meets R ((affine_geom.join R Q):β) ) := h2.1; 
                have j2: (affine_geom.meets Q ((affine_geom.join R Q):β) ) := h2.2; 
                have j3: (affine_geom.meets Q ((affine_geom.join R Q):β) ) ∧ (affine_geom.meets R ((affine_geom.join R Q):β) ) := 
                begin
                  exact false.rec (affine_geom.meets Q (affine_geom.join R Q) ∧ affine_geom.meets R (affine_geom.join R Q)) (hPnotQR hhPQR),
                end,
                have h2a: (affine_geom.meets Q ((affine_geom.join R Q):β) )∧ (affine_geom.meets R ((affine_geom.join R Q):β)) := begin
                  apply j3,
                end,
              
                have h3:((Q ≠ R) ∧ (affine_geom.meets Q ((affine_geom.join R Q):β) ) ∧ (affine_geom.meets R ((affine_geom.join R Q):β))) :=
                begin
                  simp [h2a],
                  tauto,
                end,
                apply eq.symm,
                apply (affine_geom.join_unique Q R ((affine_geom.join R Q):β )),
                exact h3,
-- (join_contains   : ∀ P Q, (meets P (join P Q))∧ (meets Q (join P Q)))
-- (join_unique     : ∀ P Q k, ((P ≠ Q) ∧ (meets P k) ∧ (meets Q k)) →  (k = (join P Q)))
              end,
              apply hQRRQ,
            end,
            have hQPQa: affine_geom.meets (P:α) ((affine_geom.join P (Q:α )):β)  ∧ affine_geom.meets Q ((affine_geom.join P Q):β) :=
            begin
              apply (affine_geom.join_contains P Q),
            end,
            have hPPQa: affine_geom.meets P ((affine_geom.join P Q):β) := hQPQa.1,
            have hPQa:  affine_geom.join P Q = QR := 
            begin
              rw hQR,
              have u0: affine_geom.join Q R = ((affine_geom.join R Q):β ) := 
              begin
                 apply (join_symm Q R),
              end,
              -- lemma join_symm [G : (affine_geom α β)]: ∀ A B:α,  ((affine_geom.join A B):β)   = (affine_geom.join B A) := 
              have u1: affine_geom.join P Q = ((affine_geom.join R Q):β ) := 
              begin
                rw ← u0,
                rw ← hQR,
                rw ← PQQR,
                apply (join_symm P Q),

              end, 
              have u2: affine_geom.join R Q = ((affine_geom.join Q R):β ) := 
              begin
                apply (join_symm R Q),
              end,
              begin
                rw [u1],
                rw [u2],
              end,

            end,
            have hPQRz: affine_geom.meets P (QR:β) := 
            begin
              rw hPQa at hPPQa,
              exact hPPQa,
            end,
            have hPPQ: affine_geom.meets P (PQ:β) := by cc,
            begin
              cc,
            end,
          end,
--         same_joins [G : (affine_geom α β)]:
-- ∀ P  Q  R:α ,∀ m:β , (P ≠ Q ∧  P ≠ R ∧  Q ≠ R ∧ (m = affine_geom.join P Q) ∧ (affine_geom.meets R m)) → (affine_geom.join Q R = m) :=

-- if l = QR, we've get P is on QR. contradition
-- hence l <> QR, and l || QR, so they share no points
-- S is on l, and R is on QR
-- suppose S = R; then l and QR share a point. Contradiction.
-- hence S <> R. Whew!

      assume hh: l = QR, --contradiction hyp
      show false, from
      begin
        -- P is on l
        have hPlz: (affine_geom.meets P l) ∧ (affine_geom.parallel α l QR):=
        begin
          apply (affine_geom.a2b P QR l),
          exact hl,
        end,
        have hPl: (affine_geom.meets P l) := hPlz.1,
        -- P is not on QR [done: hPnQR]
        rw hh at hPl,
        tauto,
      end,
      --====================================================
      -- (parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (¬ ((meets P k) ∧ (meets P n)))))
      have hsnotQRa: ¬ (affine_geom.meets S l ∧ affine_geom.meets S QR) := 
      begin
        apply (affine_geom.parallel_prop_2 l QR),
        tauto,
      end,
      have hsnotQR: ¬ affine_geom.meets S QR := by cc,
      have hRQRa: (affine_geom.meets Q QR) ∧ (affine_geom.meets R QR) := begin
        apply affine_geom.join_contains Q R,
      end,
      have hRQR: (affine_geom.meets R QR) := by exact hRQRa.2,
      show (¬ R = S),
      assume hh: R = S,
      show false, from
      begin
        rw hh at hRQR,
        cc,
      end,
    end,  
  }, -- end of S ≠ R
end 

-- Now consider the lines P R and QS. It
-- may happen that they meet (for example in
-- the real projective plane they will (proof?)). On the other hand, it is consistent
-- with the axioms to assume that they do not meet.
-- In that case we have an affine plane consisting of four points P, Q, R, S and
-- six lines P Q, P R, P S, QR, QS, RS, and one can verify easily that the axioms
-- A1–A3 are satisfied. This is the smallest affine plane.
-- Definition. A pencil of lines is either a) the set of all lines passing through
-- some point P, or b) the set of all lines parallel to some line l. In the second case
-- we speak of a pencil of parallel lines.
-- Definition. A one-to-one correspondence between two sets X and Y is
-- a mapping T : X → Y (i.e. a rule T, which associates to each element x of the
-- set X an element T(x) = y ∈ Y ) such that x1 6= x2 ⇒ T x1 6= T x2, and ∀y ∈ Y ,
-- ∃x ∈ X such that T(x) = y.

-- Some exercises from the back of the book:
-- 1. Show that any two pencils of parallel lines in an affine plane have the
-- same cardinality (i.e. that one can establish a one-to-one correspondence
-- between them). Show that this is also the cardinality of the set of points
-- on any line.
-- 2. If there is a line with exactly n points, show that the number of points in
-- the whole affine plane is n^2
.

-- TO FILL IN HERE: the quotient of lines by parallelism, call it type γ
-- type Ppoint(α β ) contining Ordinary(α) | Extended(γ)
-- type Pline(β) containing Extended(β,γ) | Infinity

@[instance] def geom.rel (α β : Type) [affine_geom α β]: setoid (β) :=
{r := parallel, iseqv := begin 
  exact parallel_equivalence,
end }

def pencil (α β : Type) [affine_geom α β] := quotient (geom.rel α β)

inductive ppoint (α β : Type) [affine_geom α β] : Type
| ordinary : α → ppoint 
| infinite : (pencil α β) → ppoint

inductive pline (α β : Type) [affine_geom α β] : Type
| extended : β → pline
| infinity : pline

@[simp] def z_parallel : (pencil α β) → β → Prop
:= quotient.lift (parallel) begin 
  intros a b hab, apply funext, intro k, simp, split,
    {intro ha, apply parallel_equivalence.2.2,
    apply parallel_equivalence.2.1 hab, exact ha,},
    {intro hb, apply parallel_equivalence.2.2,
    exact hab, exact hb,},
end

@[simp] def join_point_pencil : α → pencil α β → pline α β 
|P := quotient.lift (λ x : β, pline.extended (find_parallel P x)) begin 
  intros k n hkn, simp,

  let m := find_parallel P n,
  have hm : m = find_parallel P n := rfl,
  rw ← hm, apply eq.symm,

  have hmpm : meets P m := begin apply (a2b P n m hm).1, end,
  have hpmk : parallel m k := begin apply parallel_equivalence.2.2,
  apply (a2b P n m hm).2, apply parallel_equivalence.2.1 hkn, end,

  exact a2a P k m ⟨hmpm, hpmk⟩, 
end

--(a2a: ∀ P k n, ((meets P n ) ∧ (parallel n k)) →  (n = find_parallel P k))

#check quotient.lift
example (a b : Prop) (hab : a = b) : a ↔ b := iff_of_eq hab

@[simp] def pmeets {α β : Type} [affine_geom α β] : ppoint α β → pline α β → Prop
| (ppoint.ordinary P) (pline.extended k) := meets P k
| (ppoint.ordinary P) (pline.infinity) := false
| (ppoint.infinite k_pencil) (pline.extended (n : β)) := z_parallel k_pencil n
| (ppoint.infinite k_pencil) (pline.infinity) := true

@[simp] def pjoin {α β : Type} [affine_geom α β] : ppoint α β → ppoint α β → pline α β
| (ppoint.ordinary P) (ppoint.ordinary Q) := pline.extended (join P Q)
| (ppoint.ordinary P) (ppoint.infinite k_pencil) := join_point_pencil P k_pencil
| (ppoint.infinite k_pencil) (ppoint.ordinary P) := join_point_pencil P k_pencil
| (ppoint.infinite k_pencil) (ppoint.infinite n_pencil) := pline.infinity

end affine_geometry 
.

@[class] structure projective_geom (α β  : Type u) :=
(pmeets           : α → β  → Prop) -- a point P:α is on a line k:β  
(pjoin            : α → α → β)     -- join P Q is the unique line joining P and Q (at least when they're distinct)
(join_contains   : ∀ P Q, (pmeets P (pjoin P Q)) ∧ (pmeets Q (pjoin P Q)))
(join_unique     : ∀ P Q k, ((P ≠ Q) ∧ (pmeets P k) ∧ (pmeets Q k)) →  (k = (pjoin P Q)))
(p2              : ∀ k n:β, ∃ P:α, ((pmeets P k) ∧ (pmeets P n))) -- any two lines meet in at least one point
(p3              : ∃ P Q R, (((P ≠ Q) ∧ (Q ≠ R) ∧ (P ≠ R)) ∧ (¬ pmeets P (pjoin Q R)))) -- there are 3 noncollinear pts.
(p4              : ∀ k:β, ∃ P Q R:α , (P ≠ Q) ∧ (Q ≠ R) ∧ (P ≠ R) ∧ (pmeets P k) ∧ (pmeets Q k) ∧ (pmeets R k)) -- there are 3 points on any line

variables {α β : Type} [projective_geom α β]

variables {α' β' : Type} [affine_geom α' β']

#check projective_geom.p2 
section projective_geom

-- projectivization of an affine geometry
def projectivize (α' β' : Type) [affine_geom α' β'] : projective_geom (ppoint α' β') (pline α' β') :=
{pmeets := pmeets, pjoin := pjoin, join_contains := begin 
  intros P Q, cases P, cases Q,
    { simp, apply affine_geom.join_contains,},
    { simp, split, apply quotient.induction_on Q, intro a, simp,
      apply (affine_geom.a2b P a (affine_geom.find_parallel P a) begin refl end).1,
      apply quotient.induction_on Q, intro a, simp,
      apply parallel_equivalence.2.1 (affine_geom.a2b P a (affine_geom.find_parallel P a) begin refl end).2,},
    {split, 
      {apply quotient.induction_on P, intro a, cases Q,
        {simp, apply parallel_equivalence.2.1 (affine_geom.a2b Q a (affine_geom.find_parallel Q a) begin refl end).2,},
        {simp, },},
      {cases Q,
        {simp, apply quotient.induction_on P, intro a, simp,
          apply (affine_geom.a2b Q a (affine_geom.find_parallel Q a) begin refl end).1,},
        {apply quotient.induction_on P, apply quotient.induction_on Q, simp,},},},
end, join_unique := begin 
  intros P Q k, cases P; cases Q; cases k,
    {intro h, simp at *, apply affine_geom.join_unique, exact h,},
    {intro h, simp at *, assumption,},
    {simp at *, apply quotient.induction_on Q, intros a h₁ h₂, simp at *,
    apply affine_geom.a2a, exact ⟨h₁, parallel_equivalence.2.1 h₂⟩, },
    {simp at *,},
    {simp at *,apply quotient.induction_on P, intros a h₁ h₂, simp at *,
    apply affine_geom.a2a, exact ⟨h₂, parallel_equivalence.2.1 h₁⟩,},
    {simp at *,},
    {simp at *, apply quotient.induction_on P, apply quotient.induction_on Q,
    intros a b h₁ h₂ h₃, simp at *, 
    have : b || a := begin apply parallel_equivalence.2.2, exact h₂, exact parallel_equivalence.2.1 h₃, end,
    exact h₁ this,},
    {simp at *,},
end, p2 := begin 
  intros k n, cases k; cases n,
    {cases classical.em (k || n),
      {apply exists.intro (ppoint.infinite ⟦k⟧), simp, split,
        exact parallel_equivalence.1 k, exact h,},
      {cases exists_intersection k n h with P hP, 
      let pP : ppoint α' β' := ppoint.ordinary P,
      have hpP : pP = ppoint.ordinary P := rfl,
      apply exists.intro pP, simp,exact hP,},},
    {let pP : ppoint α' β' := ppoint.infinite ⟦k⟧,
    have hpP : pP = ppoint.infinite ⟦k⟧ := rfl,
    apply exists.intro pP, simp, apply parallel_equivalence.1,},
    {let pP : ppoint α' β' := ppoint.infinite ⟦n⟧,
    have hpP : pP = ppoint.infinite ⟦n⟧ := rfl,
    apply exists.intro pP, simp, apply parallel_equivalence.1,},
    {cases exists_line α' β', 
    let pw : ppoint α' β' := ppoint.infinite ⟦w⟧,
    have hpw : pw = ppoint.infinite ⟦w⟧ := rfl,
    apply exists.intro pw, rw hpw, simp,},
end, p3:= begin 
  cases _inst_3.a3 with P h, cases h with Q h_2, cases h_2 with R h_3,

  let pP : ppoint α' β' := ppoint.ordinary P,
  have hpP : pP = ppoint.ordinary P := rfl,
  let pQ : ppoint α' β' := ppoint.ordinary Q,
  have hpQ : pQ = ppoint.ordinary Q := rfl,
  let pR : ppoint α' β' := ppoint.ordinary R,
  have hpR : pR = ppoint.ordinary R := rfl,

  apply exists.intro pP, apply exists.intro pQ, apply exists.intro pR,
  rw hpP, rw hpQ, rw hpR, repeat {split},
    {simp, exact h_3.1.1,},
    {simp, exact h_3.1.2.1,},
    {simp, exact h_3.1.2.2,},
    {simp, exact h_3.2},
end, p4 := begin 
  intro k, cases k,
end,}

end projective_geom
end geom



-- Notes from Dhruv
-- cc often slow; best to try to do things directly if you can. 
-- 
-- use "." to split sections and update locally only. 

-- To figure out how to do a proof...write an example that has the "shape" of the thing you 
-- want to do, like "I wanna do a contrapositive proof", and then do a library_search:

-- example cp: ∀ p q:Prop, (p -> q) -> (~q -> ~p) := by library_search
-- get back: exact mt

-- Sounds great! ... but if you try 
-- example cpp:  ∀ p q:Prop,(p -> q) -> (¬ q ->  ¬ p) := 
-- begin
--   exact mt,
-- end-- 
-- it doesn't work, because of the forall; so try instead, moving the "forall" to a parameter:

-- example (p q:Prop):  (p -> q) -> (¬ q ->  ¬ p) := 
-- begin
--   exact mt,
-- end
-- and that works fine. 
