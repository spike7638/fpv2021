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
parallel or not. Actually, "parallel" (the function) is first asserted to exist [or, if you like, required to exist
if you want to build an affine-geometry structure on some points and lines]. The next two conditions say
that (1) lines are parallel to themselves, and (2) that if k and n are distinct and parallel, then any point on k
is NOT a point on n. 

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
(parallel_prop_2 : ∀ k n P, ((k ≠ n) ∧ parallel k n ∧  meets P k) →  ¬ (meets P n))
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
/- 
The first example given is that the Euclidean plane is an affine geometry. I'm going to skip that one
and move right on tot he second example, just after Prop 1.2 -- a four-point affine plane. 
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
    intro p, 
    intro q,
    cases p,
    repeat {
      cases q,
      repeat {
        repeat {
          rw [joinA4, meetsA4],
          simp,
        },
      }
    },
  end,
  join_unique   := begin
    intro p, 
    intro q, 
    intro k,
    cases p,
    repeat {
      cases q,
      {
        rw [joinA4], 
        simp,
        cases k,
        repeat {
          cc,
        },
      },
    },
    repeat {
      rw [joinA4], 
      simp,
      cases k,
      repeat {
        rw [meetsA4],
        simp,
      },
      repeat {
        cc,
      },
      repeat {
        rw [meetsA4],
        cc,
      },
    },
    repeat {
      cases q,
      repeat {
        rw [joinA4],
        cases k,
        repeat {
          rw [meetsA4],
          cc,
        },
        repeat {
          simp,
          rw [meetsA4],
          rw [meetsA4],
          cc,
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
    
      intros k n P,
      cases k,
      repeat {
        cases n,
        repeat {
          cases P,
          repeat {
            rw [meetsA4, parallelA4],
            cc,
          },
        },
      },
    repeat {
      rw [meetsA4, parallelA4],
      simp,
      rw [meetsA4],
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


end affine_geometry 
