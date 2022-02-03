import tactic
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
then any point on kis NOT a point on n and (3) vice-versa: if k and n have no points in common, then k and n
are parallel. 

Axiom 2 asserts the existence of a unique parallel under certain conditions. Once again, we'll want
to not only know that such a parallel exists, but to be able to name it and work with it, so we 
insist that there's a "find_parallel" function which (see "a2") says that if P lies on a line n parallel to 
k, and if n and k are parallel, then n is exactly "find_parallel P k". (In fact, that's an if-and-only-if.)

Axiom 3 is (thank heavens!) actually almost exactly the same in Hartshorne and in Lean. 

NB: Hartshorne uses the letter "l" to denote lines. I'll almost always avoid this, and use m,n, and k. The 
letter l looks too much like 1 for my comfort. 
 -/

@[class] structure affine_geom (α β  : Type u) :=
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

variables {α β : Type} [G: (affine_geom α β) ]
#check G.parallel_prop_2 
#check G.parallel_prop_3 
#check G.parallel 
#check G.meets

example (p q:Prop):  (p -> q) -> (¬ q ->  ¬ p) := 
begin
  -- suggest,
  exact mt,
end

lemma parallel_symmetric:
  symmetric (G.parallel) := 
  begin
    rw [symmetric],
    intro k,
    intro n,
    by_cases k=n,
    {
      intro hp,
      rw h,
      apply G.parallel_prop_1, -- NOTE use of "G.parallel_prop_1" here, 
    },
    intro hpkn,
    have kNEn: k ≠ n := h,
    have ha : (k ≠ n) ∧ (affine_geom.parallel α k n) := -- I cannot replace "affine_geom.parallel" here with G.parallel. Why??
    begin 
        exact ⟨h, hpkn⟩,
    end,
    have hr: (∀ P : α, (¬ ((affine_geom.meets P k) ∧ (affine_geom.meets P n)))) :=
    begin
      refine affine_geom.parallel_prop_2 k n ha, 
    end,

    have: (affine_geom.parallel α n k) := 
    begin
      refine affine_geom.parallel_prop_3 n k _,
      intro P,
      specialize hr P,
      cc,
    end,
    exact this,
  end

-- Is there a way to say "every mention of "meets" and "parallel" mean affine_geom.meets or affine_geom.parallel from now on? 



lemma parallel_equivalence:
--   equivalence (G.parallel α β)    :=
equivalence (G.parallel )     := 
begin
  repeat { apply and.intro },
  {
    apply G.parallel_prop_1,
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
    intro q,
    intro r,
    intro s,
    intro hp1,
    intro hp2,
    -- have hAnd: ((affine_geom.parallel α q r) ∧ (affine_geom.parallel α r s)) := and.intro hp1 hp2,
    -- revert hAnd,
-- If k = n, there is nothing to prove
    by_cases hqs: q = s ,
    {
      rw [hqs],
      -- intro hJunk,
      apply G.parallel_prop_1,
    },
-- If k ≠ n, 
    {
      apply classical.by_contradiction,
      intro hh,
      have hw := (mt (affine_geom.parallel_prop_3 q s)) hh,
      simp at hw, 
      cases hw,
      rename hw_w P,
 
      have e1: q = affine_geom.find_parallel P r := 
      begin
        apply (affine_geom.a2a P r q), 
        exact ⟨ hw_h.1, hp1⟩, 
      end,
      have e2: s = affine_geom.find_parallel P r := 
      begin
        apply (affine_geom.a2a P r s),
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

.

/- 
The first example given is that the Euclidean plane is an affine geometry. I'm going to skip that one
and move right on to the second example, just after Prop 1.2 -- a four-point affine plane. 
If first need to create a type for points; I build one with exactly four no-argument constructors. So the 
only things of type A4 are A4.P, A4.Q, A4.R, and A4.S . if we want to define a function on A4, 
we have to give its value for each of these four things. 

Just after the picture at the top of page 3, H tells us there are six lines in the geometry, each containing
two of the points, so we build a type for lines, giving it six constructors with helpful mnemonic names. 
-/

inductive A4 : Type
| P
| Q
| R 
| S

inductive A4Lines : Type
| PQ
| PR 
| PS 
| QR
| QS
| RS

/- 
Now we have to provide all the other things an affine-geometry need, starting with a "meets" function. 
We write that out with cases: 
 -/
def meetsA4 : A4 → A4Lines → Prop 
| A4.P A4Lines.PQ    := true
| A4.P A4Lines.PR    := true
| A4.P A4Lines.PS    := true
| A4.P A4Lines.QR    := false
| A4.P A4Lines.QS    := false
| A4.P A4Lines.RS    := false
| A4.Q A4Lines.PQ    := true
| A4.Q A4Lines.PR    := false
| A4.Q A4Lines.PS    := false
| A4.Q A4Lines.QR    := true
| A4.Q A4Lines.QS    := true
| A4.Q A4Lines.RS    := false
| A4.R A4Lines.PQ    := false
| A4.R A4Lines.PR    := true
| A4.R A4Lines.PS    := false
| A4.R A4Lines.QR    := true
| A4.R A4Lines.QS    := false
| A4.R A4Lines.RS    := true
| A4.S A4Lines.PQ    := false
| A4.S A4Lines.PR    := false
| A4.S A4Lines.PS    := true
| A4.S A4Lines.QR    := false
| A4.S A4Lines.QS    := true
| A4.S A4Lines.RS    := true

/- 
You should read that as "meetsA4 A4.P A4Lines.PQ is true; <and then 23 other similar things>" 

  And then we have to define a "join" function. There's the challenge of deciding "what should be
  the line joining P and P?", because ANY line containing P would "work". But if you look at the axioms,
  they never mention the value of the join function EXCEPT for distinct points, so it doesn't matter
  what we pick. I've chosen ones with cyclically permuted names. 
-/

def joinA4 : A4 → A4 → A4Lines
| A4.P A4.P := A4Lines.PQ
| A4.Q A4.Q := A4Lines.QR
| A4.R A4.R := A4Lines.RS
| A4.S A4.S := A4Lines.PS

| A4.P A4.Q := A4Lines.PQ
| A4.P A4.R := A4Lines.PR
| A4.P A4.S := A4Lines.PS
| A4.Q A4.P := A4Lines.PQ
| A4.Q A4.R := A4Lines.QR
| A4.Q A4.S := A4Lines.QS
| A4.R A4.P := A4Lines.PR
| A4.R A4.Q := A4Lines.QR
| A4.R A4.S := A4Lines.RS
| A4.S A4.P := A4Lines.PS
| A4.S A4.Q := A4Lines.QS
| A4.S A4.R := A4Lines.RS
def parallelA4 : A4Lines → A4Lines → Prop 
| A4Lines.PQ A4Lines.PQ := true
| A4Lines.PQ A4Lines.PR := false 
| A4Lines.PQ A4Lines.PS := false 
| A4Lines.PQ A4Lines.QR := false 
| A4Lines.PQ A4Lines.QS := false 
| A4Lines.PQ A4Lines.RS := true 
| A4Lines.PR A4Lines.PQ := false 
| A4Lines.PR A4Lines.PR := true 
| A4Lines.PR A4Lines.PS := false 
| A4Lines.PR A4Lines.QR := false 
| A4Lines.PR A4Lines.QS := true 
| A4Lines.PR A4Lines.RS := false 
| A4Lines.PS A4Lines.PQ := false 
| A4Lines.PS A4Lines.PR := false 
| A4Lines.PS A4Lines.PS := true 
| A4Lines.PS A4Lines.QR := true 
| A4Lines.PS A4Lines.QS := false 
| A4Lines.PS A4Lines.RS := false 
| A4Lines.QR A4Lines.PQ := false 
| A4Lines.QR A4Lines.PR := false 
| A4Lines.QR A4Lines.PS := true 
| A4Lines.QR A4Lines.QR := true 
| A4Lines.QR A4Lines.QS := false 
| A4Lines.QR A4Lines.RS := false 
| A4Lines.QS A4Lines.PQ := false 
| A4Lines.QS A4Lines.PR := true 
| A4Lines.QS A4Lines.PS := false 
| A4Lines.QS A4Lines.QR := false 
| A4Lines.QS A4Lines.QS := true 
| A4Lines.QS A4Lines.RS := false 
| A4Lines.RS A4Lines.PQ := true 
| A4Lines.RS A4Lines.PR := false 
| A4Lines.RS A4Lines.PS := false 
| A4Lines.RS A4Lines.QR := false 
| A4Lines.RS A4Lines.QS := false 
| A4Lines.RS A4Lines.RS := true



def find_parallelA4 : A4 → A4Lines → A4Lines
| A4.P A4Lines.PQ := A4Lines.PQ 
| A4.P A4Lines.PR := A4Lines.PR
| A4.P A4Lines.PS := A4Lines.PS
| A4.P A4Lines.QR := A4Lines.PS
| A4.P A4Lines.QS := A4Lines.PR 
| A4.P A4Lines.RS := A4Lines.PQ
| A4.Q A4Lines.PQ := A4Lines.PQ
| A4.Q A4Lines.PR := A4Lines.QS 
| A4.Q A4Lines.PS := A4Lines.QR
| A4.Q A4Lines.QR := A4Lines.QR
| A4.Q A4Lines.QS := A4Lines.QS
| A4.Q A4Lines.RS := A4Lines.PQ
| A4.R A4Lines.PQ := A4Lines.RS
| A4.R A4Lines.PR := A4Lines.PR
| A4.R A4Lines.PS := A4Lines.QR
| A4.R A4Lines.QR := A4Lines.QR
| A4.R A4Lines.QS := A4Lines.PR
| A4.R A4Lines.RS := A4Lines.RS
| A4.S A4Lines.PQ := A4Lines.RS
| A4.S A4Lines.PR := A4Lines.QS
| A4.S A4Lines.PS := A4Lines.PS
| A4.S A4Lines.QR := A4Lines.PS
| A4.S A4Lines.QS := A4Lines.QS 
| A4.S A4Lines.RS := A4Lines.RS

#check joinA4

@[instance] def A4affine_geom : affine_geom A4 A4Lines :=
{
  meets       := meetsA4,
  join        := joinA4,
  join_contains := begin
    intros P Q,
    cases P,
    repeat {
      cases Q,
      repeat {tauto,},
    },
  end,
  join_unique := begin
    intros P Q k,
    cases k,
    repeat {
      cases P,
      {
        repeat{
          cases Q,
          repeat {
            rw [meetsA4, joinA4], 
            tauto,
          },
        },
      },
      repeat {
        cases Q,
        repeat {
            rw [meetsA4, joinA4], 
            tauto,
        },
      },
    },
  end,
  parallel      := parallelA4,

  parallel_prop_1 := begin 
    intros k,
    cases k,
    repeat {
      rw [parallelA4],
      cc,
    },
  end,
  parallel_prop_2 := begin 
    intros k n,
    cases k,
    repeat {
      cases n,
      repeat {
        tauto,
      },
      repeat {
        intro hp,
        intro P,
        cases P,
        tauto,
      },
    },
    repeat {
      tauto,
    },
  end,
  parallel_prop_3 := begin 
    intros k n,
    intros hp,
    cases k,
    repeat {
      cases n,
      repeat {
        tauto,
      },
      repeat {
        rw [parallelA4],
        specialize hp A4.P,
        rw [meetsA4] at hp,  
        rw [meetsA4] at hp,  
        cc,
      },
      repeat {
        rw [parallelA4],
        specialize hp A4.Q,
        rw [meetsA4] at hp,  
        rw [meetsA4] at hp,  
        cc,
      },
    },
    repeat {
      rw [parallelA4],
      specialize hp A4.R,
      rw [meetsA4] at hp,  
      rw [meetsA4] at hp,  
      cc,
    },
    {
      rw [parallelA4],
      specialize hp A4.S,
      rw [meetsA4] at hp,  
      rw [meetsA4] at hp,  
      cc,
    },
    repeat {
      rw [parallelA4],
      specialize hp A4.S,
      rw [meetsA4] at hp,  
      rw [meetsA4] at hp,  
      cc,
    },
  end,
  find_parallel := find_parallelA4,
  a2a := begin
    intros P k n,
    cases P,
    repeat{cases k,
    repeat {cases n,
    repeat {
      rw [meetsA4, parallelA4, find_parallelA4],
      simp,
    },},},
  end,
  a2b := begin
    intros P k n,
    cases P,
    repeat{cases k,
    repeat {cases n,
    repeat {
      rw [meetsA4, parallelA4, find_parallelA4],
      simp,
    },},},
  end,
  a3 := begin
    have h1:A4.P ≠ A4.Q ∧ A4.Q ≠ A4.R ∧ A4.P ≠ A4.R, by simp,
    have h2:(¬ meetsA4 A4.P (joinA4 A4.Q A4.R)), by begin 
      rw [joinA4],
      intro h,
      rw [meetsA4] at h,
      assumption,
    end,
    have hh: (A4.P ≠ A4.Q ∧ A4.Q ≠ A4.R ∧ A4.P ≠ A4.R) ∧ ¬ meetsA4 A4.P (joinA4 A4.Q A4.R), begin
      apply and.intro h1 h2,
    end,
    -- have hh2: A4.P ≠ A4.Q ∧ A4.Q ≠ A4.R ∧ A4.R ≠ A4.P ∧ ¬ meetsA4 A4.P (joinA4 A4.Q A4.R), begin
    --   by simp,
    -- end,
    
    apply exists.intro A4.P,
    apply exists.intro A4.Q,
    apply exists.intro A4.R,
    apply hh,
  end
}
#check A4affine_geom 


-- Example. The ordinary plane, known to us from Euclidean geometry, satisfies the axioms A1–A3, and therefore is an affine plane.
-- STILL DO TO

-- Proposition 1.2 Two distinct lines have at most one point in common.
-- For if l, m both pass through two distinct points P, Q, then by axiom A1,
-- l = m.

lemma one_shared_point (r s: β) (P Q: α ) [G: (affine_geom α β) ]: 
r ≠ s ∧ 
affine_geom.meets P r ∧ affine_geom.meets P s ∧ 
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
  exact hrs hreqs,
end

-- @[class] structure affine_geom (α β  : Type u) :=
-- (meets           : α → β  → Prop) -- a point P:α is on a line k:β  
-- (join            : α → α → β)     -- join P Q is the unique line joining P and Q (at least when they're distinct)
-- (join_contains   : ∀ P Q, (meets P (join P Q))∧ (meets Q (join P Q)))
-- (join_unique     : ∀ P Q k, ((P ≠ Q) ∧ (meets P k) ∧ (meets Q k)) →  (k = (join P Q)))
-- (parallel        : β → β → Prop)
-- (parallel_prop_1 :  ∀ k, parallel k k) 
-- -- distinct lines that are parallel have no shared points
-- --(parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (((meets P k) →  ¬ (meets P n)))))
-- (parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (¬ ((meets P k) ∧ (meets P n)))))
-- -- lines that have no shared points are parallel. 
-- (parallel_prop_3 : ∀ k n, (∀ P:α , ((meets P k) →  ¬ (meets P n)) ) → (parallel k n)  ) 
-- (find_parallel   : α → β → β)     -- given P, k, there a unique line n parallel to k and containing P. that's 'find_parallel P k'
-- (a2              : ∀ P k n, ((meets P n ) ∧ (parallel n k)) ↔ (n = find_parallel P k))
-- (a3              : ∃ P Q R, (((P ≠ Q) ∧ (Q ≠ R) ∧ (P ≠ R)) ∧ (¬ meets P (join Q R)))) -- there are 3 noncollinear pts.

lemma one_shared_line (r s: β) (P Q: α ) [G: (affine_geom α β) ]: 
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
-- Example. An affine plane has at least four points. 
-- There is an affine plane with four points. (done above)
-- Indeed, by A3 there are three non-collinear points. Call them P, Q, R. By
-- A2 there is a line l through P, parallel to the line QR joining Q, and R, which
-- exists by A1. Similarly, there is a line m k P Q, passing through R.
-- Now l is not parallel to m (l ∦ m). For if it were, then we would have
-- P Q k m k l k QR
-- 2
-- and hence P Q k QR by Proposition 1.1. This is impossible, however, because
-- P Q 6= QR, and both contain Q.
-- Hence l must meet m in some point S.
-- m BA = 0.35 cm
-- Arrows take length 0.35cm
-- S
-- B A
-- Q R
-- P
-- Since S lies on m, which is parallel to P Q,
-- and different from P Q, S does not lie on
-- P Q, so S 6= P, and S 6= Q. Similarly S 6= R.
-- Thus S is indeed a fourth point. This proves
-- the first assertion.

-- FAILED attempt to mimic the proof above; stalled out at going from "there exist three noncollinear points" to  
-- "let's call them A,B,C" (or better still, P, Q, R)

-- lemma four_points [G: (affine_geom α β) ]: 
-- ∃ P Q R S : α,  P ≠ Q ∧  P ≠ R ∧  P ≠ S ∧  Q ≠ R ∧ Q ≠ S ∧ R ≠ S
-- :=
-- begin
--   have h3: ∃ P Q R:α , (P ≠ Q) ∧ (Q ≠ R) ∧ (P ≠ R) := 
--   begin
--     have h3a: ∃ P Q R:α , (((P ≠ Q) ∧ (Q ≠ R) ∧ (P ≠ R)) ∧ (¬ affine_geom.meets P (affine_geom.join Q R))) :=
--     begin
--       exact G.a3 , -- tried "affine_geom.a3 and that failed. because it couldn't guess \b apparently"
--     end,
--     cases h3a with P h3a1,
--     cases h3a1 with Q h3a2,
--     cases h3a2 with R h3a3,
--     have h3points: (P ≠ Q ∧ Q ≠ R ∧ P ≠ R) := begin
--       exact h3a3.1,
--     end,
--     refine Exists.intro P _,
--     refine Exists.intro Q _,
--     refine Exists.intro R _,
--     exact h3a3.1,
--   end,
--   cases h3 with P h3_1,
--   cases h3_1 with Q h3_2,
--   cases h3_2 with R h3_3,
-- -- By A2 there is a line l through P, parallel to the line QR joining Q, and R, which
-- -- exists by A1. [we'll call l by the name k -- jfh]
--   have hk: ∃ kp:β  , affine_geom.parallel α  kp (affine_geom.join Q R) :=
--   begin
--     -- let QR := affine_geom.join Q R,
--     -- let k := affine_geom.find_parallel P QR,
--     have hz: (affine_geom.meets P (affine_geom.find_parallel P (affine_geom.join Q R))) ∧ (affine_geom.parallel α (affine_geom.find_parallel P (affine_geom.join Q R)) (affine_geom.join Q R)) := 
--     begin
--       apply affine_geom.a2b,
--       refl,
--     end,

--   end,
-- end

-- Want to say: if R is on join P Q, and P,Q,R distinct, then join R Q = join P Q. How to express neatly? 

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
end affine_geometry 
end geom

-- @[class] structure affine_geom (α β  : Type u) :=
-- (meets           : α → β  → Prop) -- a point P:α is on a line k:β  
-- (join            : α → α → β)     -- join P Q is the unique line joining P and Q (at least when they're distinct)
-- (join_contains   : ∀ P Q, (meets P (join P Q))∧ (meets Q (join P Q)))
-- (join_unique     : ∀ P Q k, ((P ≠ Q) ∧ (meets P k) ∧ (meets Q k)) →  (k = (join P Q)))
-- (parallel        : β → β → Prop)
-- (parallel_prop_1 :  ∀ k, parallel k k) 
-- -- distinct lines that are parallel have no shared points
-- --(parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (((meets P k) →  ¬ (meets P n)))))
-- (parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (¬ ((meets P k) ∧ (meets P n)))))
-- -- lines that have no shared points are parallel. 
-- (parallel_prop_3 : ∀ k n, (∀ P:α , ((meets P k) →  ¬ (meets P n)) ) → (parallel k n)  ) 
-- (find_parallel   : α → β → β)     -- given P, k, there a unique line n parallel to k and containing P. that's 'find_parallel P k'
-- (a2              : ∀ P k n, ((meets P n ) ∧ (parallel n k)) ↔ (n = find_parallel P k))
-- (a3              : ∃ P Q R, (((P ≠ Q) ∧ (Q ≠ R) ∧ (P ≠ R)) ∧ (¬ meets P (join Q R)))) -- there are 3 noncollinear pts.



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
