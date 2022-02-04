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
    -- Also (and probably related): parallel seems to be taking an extra parameter α , even though I would have said that 
    -- α is implicit in the definition of G. Maybe not...but why doesn't it also want β?  And why does parallel_prop_1 not have either?
    -- Why does "meets" not have it? 
    -- perhaps up on line 95, I shuld have said that (G.parallel α), which actually IS a function of two args, is symmetric; that seems to make
    -- more sense that claiming a function of 3 args is symmetric. But it also doesn't work...apparently in the theorem statement, I have to 
    -- NOT use the α for some reason. 
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
    rw [transitive],
    intro q,
    intro r,
    intro s,
    intro hp1,
    intro hp2,

    by_cases hqs: q = s ,
    {
      rw [hqs],
      apply G.parallel_prop_1,
    },
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

-- This proof (and the one above it) can be considered "dual" to one another. (In a projective geometry, they actually will be.) "Dual" here
-- means that if you swap "point" and "line", "lies on" and "contains", you turn one theorem into the other. (Two distinct points lie on at most one common
-- line. <---> Two distinct lines contain at most one common point.) The proof (if we were in projective geometry) can also be dualized, because it turns
-- out that each axiom in projective geometry is the "dual" of some easily-proved theorem. 
--
-- My idle question here is whether this can actually be turned into a "morphism" of statements-and-proofs into dual-statements-and-their-dual-proofs. 



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


-- Lemma: if R lies on join P Q, then join PQ is the same as join Q R (if P, Q, R all distinct).
lemma same_joins [G : (affine_geom α β)]:
∀ P  Q  R:α ,∀ m:β , (P ≠ Q ∧  P ≠ R ∧  Q ≠ R ∧ (m = affine_geom.join P Q) ∧ (affine_geom.meets R m)) → (affine_geom.join Q R = m) :=
-- My first attempt at the theorem-statement didn't include the name "m" for join P Q; it just repeatedly used "join P Q". 
-- Why didn't Lean like this: 
-- ∀ P  Q  R:α , (P ≠ Q ∧  P ≠ R ∧  Q ≠ R  ∧ (affine_geom.meets R (affine_geom.join P Q))) → (affine_geom.join Q R = (affine_geom.join P Q)) :=
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

-- lemma; join P Q is the same as join Q P. 
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
-- 350 lines of the ugliest code you'll see this week. 
-- It is sobering that Hartshorne does this in 6 lines, and only takes that many because it's an elementary text...
-- Line 543 has an actual question for you, though. 

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

      assume hh: m = PQ, --contradiction hyp
      show false, from
      begin
        have hRmz: (affine_geom.meets R m) ∧ (affine_geom.parallel α m PQ):=
        begin
          apply (affine_geom.a2b R PQ m),
          exact hm,
        end,
        have hRm: (affine_geom.meets R m) := hRmz.1,
  
        have hRm: (affine_geom.meets R PQ) := 
        begin
          rw hh at hRm,
          exact hRm,
        end,
        tauto,
      end,

      have hmPQz: affine_geom.meets R m ∧ affine_geom.parallel α m PQ :=
      begin
        apply (affine_geom.a2b R PQ m),
        exact hm,        
      end,
      have hmPQy: affine_geom.parallel α m PQ := hmPQz.2,

      have hh: (m ≠ PQ ∧ affine_geom.parallel α  m PQ) :=
      begin
        simp [hmPQ, hmPQy],
      end, 
      have hnosharemPQ: ∀ X:α, ¬ ((affine_geom.meets X m) ∧ (affine_geom.meets X PQ)) := 
      begin
        apply (affine_geom.parallel_prop_2 m PQ hh),
      end,
      have h1: ¬ ((affine_geom.meets S m) ∧ (affine_geom.meets S PQ)) := (hnosharemPQ S),
      simp [hs1] at h1,
      have h2z: (affine_geom.meets P PQ) ∧ (affine_geom.meets Q PQ) := (affine_geom.join_contains P Q),
      have h2: (affine_geom.meets P PQ) := h2z.1,
      assume hC: P = S,
      show false, from
      begin
        simp [hC] at h2,
        tauto,
      end,
    end
  },
  exact h3_3.1.2.1,
  {  
    begin
      have hs1: affine_geom.meets S m := hS.1,
      have hmpq1: (affine_geom.meets R m)∧ (affine_geom.parallel α m PQ) := begin
        apply (affine_geom.a2b R PQ m hm),
      end,
      have hmpqr: (affine_geom.parallel α m PQ) := hmpq1.2,
      
      have hmPQ: ¬ (m = PQ) := 
      have hRma: affine_geom.meets R m  ∧ affine_geom.parallel α m PQ:=
      begin
        apply (affine_geom.a2b R PQ m),
        exact hm,
      end,
      have hRm: affine_geom.meets R m := by exact(hRma.1),
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
          -- This next line didn't work without the type-ascriptions; I don't really understand why. I put them in there because
          -- Dhruv suggested that they might be necessary when Lean couldn't figure out the type of some expression/term, and I suppose
          -- this is a manifestation of the same problem I had above where α and β don't seem to be "known" as part of G. 
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
        have hRm: (affine_geom.meets R PQ) := 
        begin
          rw hh at hRm,
          exact hRm,
        end,
        tauto,
      end,
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
        have hPnQR: ¬ affine_geom.meets P QR :=
          assume hhPQR: affine_geom.meets P QR,
          show false, from
          begin
            have PQQR: affine_geom.join Q P = QR := 
            begin
              apply (same_joins R Q P QR),
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

        rw hh at hPl,
        tauto,
      end,

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

.
end affine_geometry 
end geom