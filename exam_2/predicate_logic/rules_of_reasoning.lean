

axiom P : Prop
axiom Q : Prop
axiom R : Prop


-->> def true_intro : pExp := pTrue
#check true       -- a type
#check true.intro -- a constructor (value)
#print true

-- true is a proposition 
-- in Lean represented as a type
-- intro is defined to be a proof of it (a value)
-- because there is proof, we judge the proposition to be true
-- a proof is necessary and sufficient *evidence* of truth

-- *** FALSE ***

-- false
#check false
#print false
-- there is no proof of the proposition false
-- this is by definition of false as a type with no values
-- so we judge the proposition, false, to be false (untrue)

-->> def false_elim := pFalse >> P
#check @false.elim


-- def true_imp := pTrue >> P
-- oops, this is not a valid law

def true_imp : ∀ (P : Prop), true → P :=
λ P t, _

-- *** AND ***

#check and
#print and

-->> def and_intro := P >> Q >> P ∧ Q
#check @and.intro -- constructor

-->> def and_elim_left := P ∧ Q >> P
#check @and.elim_left
#print and.elim_left


-->> def and_elim_right := P ∧ Q >> Q
#check @and.elim_right
#print and.elim_right

-- *** OR ***

-->> def or_intro_left := P >> P ∨ Q
#check @or.intro_left

-->> def or_intro_right := Q >> P ∨ Q
#check @or.intro_right

-->> def or_elim := P ∨ Q >> (P >> R) >> (Q >> R) >> R
#check @or.elim

-- *** IFF ***

#check iff
#print iff

-- def iff_intro := (P >> Q) >> (Q >> P) >> (P ↔ Q)
#check @iff.intro

-- def iff_elim_left := (P ↔ Q) >> (P >> Q)
#check @iff.elim_left
#check @iff.mp

-- def iff_elim_right := (P ↔ Q) >> (Q >> P)
#check @iff.elim_right
#check @iff.mpr

-- *** ARROW ***

-- introduction rule:
-- if you show that given any (p : P) you can derive
-- a value (q : Q), then you've proven P → Q. To prove
-- P → Q, define any function of this type. The totality
-- of functions in Lean is essential here: to the "any".
  
-- def arrow_elim := (P >> Q) >> P >> Q
-- if you're given a function of type P → Q and 
-- any value of type P, you can derive one of type Q

axiom p : P
axiom pf : P → Q
#check (pf p)

-- *** RESOLUTION ***
--def resolution := (P ∨ Q) >> (¬ Q ∨ R) >> (P ∨ R)
--def unit_resolution := (P ∨ Q) >> ¬ Q >> P

-- The resolution rules are used in some automated
-- theorem provers. We won't study them in this class
-- That said, they are clearly valid reasoning rules.

-- *** NEGATION

-- def neg_intro := (P >> pFalse) >> (¬ P)
#print not

-- def neg_elim := (¬¬P) >> P -- "proof by contradiction"

#check classical.em


-- *** THEOREMS ***

-- def syllogism := (P >> Q) >> (Q >> R) >> (P >> R)
def syllogism : ∀ {P Q R : Prop}, (P → Q) → (Q → R) → (P → R) :=
  λ (P Q R : Prop) (pq : P → Q) (qr : Q → R), 
    qr ∘ pq

--def modus_tollens := (P >> Q) >> (¬ Q >> ¬ P)
theorem modus_tollens : ∀ {P Q : Prop}, (P → Q) → ¬ Q → ¬ P :=
λ P Q pq nq, syllogism pq nq

-- *** AXIOMS ***

-- def excluded_middle := P ∨ (¬ P)
#check classical.em


-- *** NON-THEOREMS (FALSEHOODS) ***
--def affirm_consequence := (P >> Q) >> (Q >> P)

theorem affirm_consequence : ∀ {P Q : Prop}, (P → Q) → Q → P :=
λ P Q pq q, _                             -- sTuCK!

--def affirm_disjunct := (P ∨ Q) >> (P >> ¬ Q)
theorem  affirm_disjunct : ∀ {P Q : Prop }, (P ∨ Q) → P → ¬ Q :=
λ (P Q : Prop) (pq : P ∨ Q) (p : P), _    -- sTuCK!

--def deny_antecedent := (P >> Q) >> (¬ P >> ¬ Q)
theorem deny_antecedent : ∀ {P Q : Prop }, (P → Q) → (¬P → ¬Q) :=
λ P Q pq np, _  