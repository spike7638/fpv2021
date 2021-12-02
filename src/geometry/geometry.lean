namespace geom
universe u

section affine_geometry

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
