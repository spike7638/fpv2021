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

example {p q:Prop}: (p ∧ q) ↔ (q ∧ p) := and.comm
example {p q:ℕ → Prop}: (∀ n, ((p n) ∧ (q n))) ↔ (∀ n,((q n) ∧ (p n))) := 
begin 
  refine iff.symm _,
  refine (forall_congr _).symm,
  intro,
  apply iff.intro,
  { 
    exact @and.symm (p a) (q a),
  },
  {
    exact @and.symm (q a) (p a),
  }
end

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
(parallel_prop_3 : ∀ k n, (∀ P, ((meets P k) →  ¬ (meets P n)) ) → (parallel k n)  ) 
(find_parallel   : α → β → β)     -- given P, k, there a unique line n parallel to k and containing P. that's 'find_parallel P k'
(a2              : ∀ P k n, ((meets P n ) ∧ (parallel n k)) ↔ (n = find_parallel P k))
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

lemma parallel_equivalence:
--   equivalence (G.parallel α β)    :=
equivalence (G.parallel )     := 
begin
  repeat { apply and.intro },
  {
    apply G.parallel_prop_1,
  },
  {
    rw [symmetric],
    intro k,
    intro n,
    by_cases k=n,
    {
      intro hp,
      rw h,
      apply G.parallel_prop_1,
    },
    intro hpkn,
    have kNEn: k ≠ n := h,
    have ha : (k ≠ n) ∧ (affine_geom.parallel α k n) := 
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
    have hAnd: ((affine_geom.parallel α q r) ∧ (affine_geom.parallel α r s)) := and.intro hp1 hp2,
    revert hAnd,
-- If k = n, there is nothing to prove
    by_cases hqs: q = s ,
    {
      rw [hqs],
      intro hJunk,
      apply G.parallel_prop_1,
    },
-- If k ≠ n, 
    {
      have hh : affine_geom.parallel α q s :=
        sorry,

    }
  }
      
end


--   {
--     rw [transitive],
--     intro k,
--     intro m,
--     intro n,
--     intro hp1,
--     intro hp2,
--     by_cases hkn: k = n ,
--     {
--       rw [hkn],
--       apply G.parallel_prop_1,
--     },
--     {
--         by_cases hkm: k = m,
--         {
--           have hh: m = k, by cc,
--           rw [hh] at hp2,
--           assumption,
--         },
--         {
--           by_cases hmn: m = n,
--           {
--             rewrite [hmn] at hp1,
--             assumption,
--           },
--           {
--             apply G.parallel_prop_2 k n hkn,
            
-- -- reminders:
-- -- (parallel_prop_2 : ∀ k n, ((k ≠ n) ∧  (parallel k n)) →  (∀ P, (meets P k) ↔  ¬ (meets P n)))
-- -- -- lines that have no shared points are parallel. 
-- -- (parallel_prop_3 : ∀ k n, (∀ P, (meets P k) ↔  ¬ (meets P n)) → (parallel k n)  ) 

--           }
--         },
--     }


--   }  -- transitive
-- end

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
| A4.P A4Lines.PR := A4Lines.PR
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
  a2 := begin
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

-- @[instance] def A4affine_geom : affine_geom A4 A4Lines :=
-- {
--   meets       := meetsA4,
--   join        := joinA4,
--   join_contains := begin
--     intro p, 
--     intro q,
--     cases p,
--     repeat {
--       cases q,
--       repeat {
--         refl,
--         cc
--       },
--       repeat {
--         rw [joinA4, meetsA4],
--         cc,
--       },
--       repeat {
--         rw [joinA4, meetsA4],
--         rw [meetsA4],
--         cc,
--       }
--     },
--   end,  
--   join_unique   := begin
--     intro p, 
--     intro q, 
--     intro k,
--     cases p,
--     repeat {
--       cases q,
--       {
--         rw [joinA4], 
--         simp,
--         cases k,
--         repeat {
--           cc,
--         },
--       },
--     },
--     repeat {
--       rw [joinA4], 
--       simp,
--       cases k,
--       repeat {
--         rw [meetsA4],
--         simp,
--       },
--       repeat {
--         cc,
--       },
--       repeat {
--         rw [meetsA4],
--         cc,
--       },
--     },
--     repeat {
--       cases q,
--       repeat {
--         rw [joinA4],
--         cases k,
--         repeat {
--           rw [meetsA4],
--           cc,
--         },
--         repeat {
--           simp,
--           rw [meetsA4],
--           rw [meetsA4],
--           cc,
--         },
--       },
--     },
--   end,
--   parallel      := parallelA4,

--   parallel_prop_1 := begin 
--     intros k,
--     cases k,
--     repeat {
--       rw [parallelA4],
--       cc,
--     },
--   end,
--   parallel_prop_2 := begin
    
--       intros k n P,
--       cases k,
--       repeat {
--         cases n,
--         repeat {
--           cases P,
--           repeat {
--             rw [meetsA4, parallelA4],
--             cc,
--           },
--           cc,
--         },
--         repeat {cc},
--       },
--     repeat {
--       rw [meetsA4, parallelA4],
--       simp,
--       rw [meetsA4],
--       cc,
--     },
--     repeat {
--       simp,
--       rw [parallelA4],
--       intro h,
--       exfalso, 
--       assumption,     
--     },
--     repeat {
--       simp,
--       rw [parallelA4],
--       intro h,
--       cases P,
--       repeat{
--         rw [meetsA4],
--         rw [meetsA4],
--         cc,
--       }
--     },
--     repeat {
--       intro P,
--       cases P,
--       {
--         rw [parallelA4] at P,
--         rw [meetsA4],
--         exfalso,
--         cc,
--       },
--     },
--     repeat {
--       rw [parallelA4] at P,
--       rw [meetsA4],
--       simp,
--     },
--     repeat{
--       rw [meetsA4],
--       simp,
--     },
--     repeat{
--       simp at P,
--       exfalso,
--       assumption,
--     },
--     repeat {
--       simp at P,
--       intro S,
--       cases S,
--       rw [meetsA4],
--       rw [meetsA4],
--       simp,
--     },
--     repeat {
--       rw[meetsA4],
--       simp,
--     },
--   end,
--   parallel_prop_3 := begin 
--     intros k,
--     intros n,
--     cases k,
--     cases n,
--     repeat {
--       rw [parallelA4, meetsA4],
--       simp, 
--       cc,
--     },
--     repeat { 
--       intro P,
--       intro S,
--       rw [parallelA4],
--       simp,
--     },
--     repeat {
--       simp,
--       by cc,
--     },
--     repeat {
--       simp,
--       cc,
--     },
--     repeat {
--       simp,
--       intro t,
--       rw [parallelA4],
--       cc,
--     },
--     repeat {
--       intro hp, 
--       specialize hp A4.P,
--       rw [meetsA4] at hp,
--       rw [meetsA4] at hp,
--       cc,
--       -- have (∀ P : A4, (meetsA4 P A4Lines.PQ ↔ ¬meetsA4 P A4Lines.PR)),
--     },
--     {
--       intro hp, 
--       specialize hp A4.Q,
--       rw [meetsA4] at hp,
--       rw [meetsA4] at hp,
--       cc,
--     },
--     {
--       intro hp, 
--       specialize hp A4.Q,
--       rw [meetsA4] at hp,
--       rw [meetsA4] at hp,
--       cc,
--     },
--     {
--       intro hp, 
--       rw [parallelA4],
--       cc,
--     },
--     repeat {
--       cases n,
--       intro hp,
--       specialize hp A4.P,
--       rw [meetsA4] at hp,
--       rw [meetsA4] at hp,
--       rw [parallelA4],
--       cc,
--     },
--     {
--       intro hp,
--       rw [parallelA4],
--       cc,
--     },
--     tautos,


--   end,
--   find_parallel := find_parallelA4,
--   a2 := begin
--     intros P k n,
--     cases P,
--     repeat{cases k,
--     repeat {cases n,
--     repeat {
--       rw [meetsA4, parallelA4, find_parallelA4],
--       simp,
--     },},},
--   end,
--   a3 := begin
--     have h1:A4.P ≠ A4.Q ∧ A4.Q ≠ A4.R ∧ A4.P ≠ A4.R, by simp,
--     have h2:(¬ meetsA4 A4.P (joinA4 A4.Q A4.R)), by begin 
--       rw [joinA4],
--       intro h,
--       rw [meetsA4] at h,
--       assumption,
--     end,
--     have hh: (A4.P ≠ A4.Q ∧ A4.Q ≠ A4.R ∧ A4.P ≠ A4.R) ∧ ¬ meetsA4 A4.P (joinA4 A4.Q A4.R), begin
--       apply and.intro h1 h2,
--     end,
--     -- have hh2: A4.P ≠ A4.Q ∧ A4.Q ≠ A4.R ∧ A4.R ≠ A4.P ∧ ¬ meetsA4 A4.P (joinA4 A4.Q A4.R), begin
--     --   by simp,
--     -- end,
    
--     apply exists.intro A4.P,
--     apply exists.intro A4.Q,
--     apply exists.intro A4.R,
--     apply hh,
--   end
-- }
#check A4affine_geom


-- lemma card_units_lt (M₀ : Type*) [monoid_with_zero M₀] [nontrivial M₀] [fintype M₀] :
--   fintype.card (units M₀) < fintype.card M₀ :=
-- fintype.card_lt_of_injective_of_not_mem (coe : units M₀ → M₀) units.ext not_is_unit_zero

end affine_geometry 
end geom
