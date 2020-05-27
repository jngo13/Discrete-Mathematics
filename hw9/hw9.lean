/-
Justin Ngo
jmn4fms
4/28/20
Sullivan 2102-001
-/

/-
HOMEWORK #9 

There is no need to import our previous definitions.
For this homework you will just use Lean's built-in
notations and definitions. 
-/

/-
Prove the following. Note that you can read each of 
the propositions to be proved as either a logical
statement or as simply a function definition. Use
what you already know about the latter to arrive
at a proof, and then understand the proof as one
that shows that the logical statement is true.
-/

theorem t1 {P Q : Prop} (p2q : P → Q) (p : P) : Q :=
/-If you have a proof of P → Q p2q, and a proof of P,
  you can get a proof of Q -/
  p2q p

theorem t2 {P Q R : Prop} (p2q : P → Q) (q2r : Q → R): P → R :=
  λ (p : P), -- Assume I have a proof of P, called p
    q2r (p2q p)

/-
Use "example" to state and prove the preceding two 
theorems but using "cases" style notation rather
than C-style. Remember, "example" is a way to state
a proposition/type and give an example of a value.
Here's an example of the use of "example". Give
your answers following this example.
-/

-- example
example : ℕ := 5

-- Your two answers here
-- by cases
-- theorem t1 {P Q : Prop} (p2q : P → Q) (p : P) : Q :=
example: ∀ {P Q : Prop}, (P → Q) → P → Q :=
λ P Q p2q,
  λ p,
    p2q p

-- theorem t2 {P Q R : Prop} (p2q : P → Q) (q2r : Q → R): P → R :=
example: ∀ {P Q R : Prop}, (P → Q) → (Q → R) → P → R :=
λ P Q R p2q q2r, 
  λ p,
    q2r (p2q p)

/-
Now give English-language versions of your two proofs.

1. If for and proposition P and Q, if P implies Q, then
    if we have a proof of P we can get a proof of Q.

2. If for any propositoins P, Q, and R, if P implies Q, and
    if Q implies R, then if we have a proof of P we can get
    a proof of R.
-/


/-
Prove the following using case analysis on one
of the arguments (i.e., use match...with...end
at a key point in your proof). Use "cases" style
notation. 
-/

-- false elimination, false implies anything
theorem t3' : ∀ (P : Prop), false → P
/- For any proposition P, if false if true than p is true-/
| P f := false.elim f
-- false elim on f (false) to get p

theorem t3 : ∀ (P : Prop), false → P
| P f := match f with /-no cases-/ end

/-
Prove false → true by applying t3 to a proposition.
You have to figure out which one.
-/
theorem t4 : false → true := t3 true
-- apply t3 to true to get a proof of false → true

/-
Define t5 to be the same as t3 but with P taken as
an implicit argument.
-/
theorem t5 : ∀ {P : Prop}, false → P
| P f := false.elim f

/-
Define t6 to be a proof of false → true by
applying t5 to the right argument(s). 
-/
theorem t6 : false → true := t5
-- implicit so we do not need to provide proposition

/-
That is almost magic. In English, t3 proves 
that false implies *any* proposition, so just
*apply* t3 to *true* in particular, but use t5 
instead of t3.

What you see here is really important: Once 
we've proved a general theorem (a ∀ proposition)
we can *apply the proof* to any *particular* case 
to yield a proof for that specific case. This is 
the elimination rule for ∀. It is also known as
universal instantiation (UI). 
-/


/-
Next we see the idea that test cases are really
just equality propositions to be proved. Here, 
for example, is a definition of the factorial
function.
-/

def fac : ℕ → ℕ 
| 0 := 1
| (n' + 1) := (n' + 1) * fac n'

/-
Use "example" to write test cases for the
first ten natural number arguments to this
function.
-/

example : fac 0 = 1 := eq.refl 1
example : fac 1 = 1 := eq.refl _  -- Inferred
example : fac 2 = 2 := rfl        -- Shorthand
#check @rfl           -- infers type and value


-- The rest of your answers here
example : fac 3 = 6 := eq.refl _
example : fac 4 = 24 := eq.refl _
example : fac 5 = 120 := eq.refl _

/-
Insight: A test case is an equality proposition.
It is proved by "running" the program under test
to reduce the application of the function to input
arguments to produce an output that is then asserted
to be equal to an expected output. 

In many cases, all we have to do is to simplify
the expressions on each side of the eq to see if
they reduce to exactly the same value. If so, we
can *apply* eq.refl (a universal generalization!)
to that value. Using rfl we can avoid even having
to type that value in cases where Lean can infer
it.
-/


/-
The next problem requires thave you give a proof of 
a bi-implication, a proposition whose connective is 
↔. To prove a bi-implication requires that one prove
an implication in each direction. 

Here you are asked to prove P ∧ Q ↔ Q ∧ P. What this
formula asserts is that ∧ is commutative. To construct
a proof of this proposition you will have to apply 
iff.intro to two smaller proofs, one of P → Q and 
and of Q → P. 

Start by "assuming" that P and Q are arbitary but 
specific propositions (∀ introduction), then apply 
iff.intro to two "stubbed out" arguments (underscores). 
We suggest that you put the underscores in parentheses 
on different lines. Then recursively fill in each of
these stubs with the required types of proofs. Study
the context that Lean shows you in its Messages panel
to see what you have to work with at each point in 
your proof constructions.
-/

theorem t7 : ∀ {P Q : Prop}, P ∧ Q ↔ Q ∧ P :=
-- need to use iff.intro (to prove if) 
-- and and.intro to solve
λ P Q,
  iff.intro 
    (λ pandq, 
      and.intro pandq.right pandq.left)
    (λ qandp, 
      and.intro qandp.right qandp.left)

-- P ∧ Q -- and.intro p q
-- P ↔ Q -- iff.intro p2q q2p
  -- Assume P then show Q (P → Q)
  -- Assume Q then show P (Q → P)

theorem and_intro {P Q : Prop} (pfPtoQ : P → Q) (pfQtoP : Q → P) : P ↔ Q :=
iff.intro pfPtoQ pfQtoP
/- 
and.intro _ _ (Given pfP and pfQ, proves P ∧ Q)
-/


/-
In English, when asked to prove P ↔ Q, one says, "it
will suffice to show P → Q and then to show Q → P." One
then goes on to give a proof of each implication. It
then follows from iff.intro that a proof of P ↔ Q can
be constructed, proving the bi-implication.
-/


/-
The trick here is to do case analysis on porq
(use match ... with ... end) and to show that 
a proof of R can be constructed *in either case*.
-/

/-
P ∨ Q can be constructed in 2 ways:
or.inl pfP (proves anything or P)
or.inr pfQ (proves anything or Q)
-/

theorem t8 
          {P Q R : Prop} 
          (p2r : P → R) 
          (q2r : Q → R) 
          (porq : P ∨ Q) : 
          R := 
  match porq with
    | or.inl p := p2r p
    | or.inr q := q2r q
    end

theorem t8'
          {P Q R : Prop} 
          (p2r : P → R) 
          (q2r : Q → R) 
          (porq : P ∨ Q) : 
          R := 
  or.elim porq p2r q2r

/- Prove P ∨ Q → R,
  it will suffice to show P → R and then Q → R 
  because if we do tha then we can use 
  or.elim to get a proof of R.-/

/-
We suggest that you use  "let ... in" to give
names to intermediate results that you then combine
in a final expression to finish the proof.
-/
theorem t9 : ∀ (P Q: Prop), (P → Q) → ¬ (P ∧ ¬ Q) :=
λ P Q,
  λ (p2q : (P → Q)),
    λ (pandnq : (P ∧ ¬ Q)),
    -- ¬ (P ∧ ¬ Q) == (P ∧ ¬ Q) → false
      ( let p := pandnq.left in
        let nq := pandnq.right in
        let q := p2q p in
        nq q -- adding "¬" to (pandnq :(P ∧ ¬ Q))
      )

/-
To prove ¬ P, assume P and show that this leads to
a contradiction, then from that derive a proof of false, 
and use false.elim to finish the proof.

* This is called "proof by negation"
-/

/-
Proof by contradiction. 
To prove P, assume ¬ P, and show that leads to
a contradiction. This shows ¬ (¬ P). Now, use
the *classical* principle of negation elimination 
to deduce P
-/

/-
theorem neg_elim' : ∀ (P : Prop), ¬ ¬ P → P :=
λ P,
λ nnp,
_           -- STUCK!!
-/

theorem neg_elim : ∀ (P : Prop), (P ∨ ¬ P) → (¬ ¬ P → P):= 
λ P, -- Assume P is an arbitrary proposition
    λ excl_middle, -- Assume law of excluded middle/ "p or not p" (h)
        λ nnp,
            match excl_middle with -- case analysis on excl_middle (h)
            | or.inl p := p
            | or.inr np := false.elim (nnp np)  -- false elimination on a proof of false
            end

-- nnp : (¬ P) → false
-- np : ¬ P
-- nnp np = false!

-- Let's use excl_middle/ ("p or not p")/ (h) to mean 
-- There is a sub-exponential time algorithm for Boolean sat.
-- ¬ excl_middle (h) means that there's not one.
-- (excl_middle ∨ ¬ excl_middle) H ∨ ¬H

-- make Lean into a classical logic
axiom em : ∀ (P : Prop), P ∨ ¬ P
#check classical.em
open classical

theorem t10 : ∀ (P : Prop), P ∨ ¬ P :=
  classical.em
  /-λ P,                      -- forall introduction 
    λ (h : P ∨ ¬P),           -- proof by negation
      let p := (h.left) in    -- and.elim_left 
      let np := (h.right) in  -- and.elim_right
      (np p) -/   


#check @or.inl
#check @or.inr

theorem t11 : ∀ (P Q : Prop), ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
λ P Q, 
    iff.intro 
        -- first case
        (λ not_porq, -- Assume proof of ¬ (P ∨ Q)
            match (classical.em P) with -- Proof of p or not p
              | or.inl p := false.elim (not_porq (or.inl p))
              -- ¬ (P ∨ Q) == (P ∨ Q → false)
              -- use false.elim when a case is not possible
              | or.inr np := 
                  match (classical.em Q) with
                    | or.inl q := false.elim (not_porq (or.inr q))
                    | or.inr nq := and.intro np nq
                  end
            end    
        )
        -- second case
        (λ np_and_nq,
          λ porq,
          -- need to do case analysis on the disjuntion
            match (porq) with
              | or.inl p := and.elim_left np_and_nq p
              | or.inr q := and.elim_right np_and_nq q
            end
        )


theorem t12 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
λ P Q,
  iff.intro
    (λ (n_pandq),
      match (classical.em P) with
        | or.inl p := 
            match (classical.em Q) with
              | or.inl q := false.elim (n_pandq _)
              | or.inr nq := _
            end
        | or.inr np := 
          match (classical.em P) with
            | or.inl p := _
            | or.inr np := _
      end
    )
    _

/-
For the following exercises, we assume that there is 
a type called Person and a binary relation, Likes, on
pairs of people.
-/
axiom Person : Type
axiom Likes : Person → Person → Prop


/-
Prove the following
-/
theorem t13 : 
  (∃ (p : Person), ∀ (q : Person), Likes q p) → 
  -- If there is someone that everyone likes
  (∀ (p : Person), ∃ (q : Person), Likes p q) :=
  -- Then everyone likes someone
λ h, -- Assume there is some person everyone likes
    match h with
    | exists.intro p pf := 
        λ q, 
            (exists.intro p (pf q))
    end


/-
theorem t13' : 
  (∃ (p : Person), ∀ (q : Person), Likes q p) → 
  -- If there is someone that everyone likes
  (∀ (p : Person), ∃ (q : Person), Likes p q) :=
  -- Then everyone likes someone
λ h, -- Assume there is some person everyone likes
  λ p, 
      (match h with
        | exists.intro loved pf := exists.intro loved _
      end
      )
-/

-- Notes
/-axiom Person : Type
axioms (Nice : Person → Prop)(Old : Person → Prop)

example : (∃ (p : Person), Nice p ∨ Old p) → 
            (∃ (p : Person), Nice p) ∨ 
            (∃ (p : Person), Old p) :=
λ p_nice_or_old,
    match p_nice_or_old with
        | exists.intro fred pf_fred_either_nice_or_old :=
            -- need to break down proof of fred nice or old, elim
            match pf_fred_either_nice_or_old with
                | or.inl n := or.inl (exists.intro fred n)
                | or.inr o := or.inr (exists.intro fred o)
            end
        end
-/

/- Notes (not answer)
Answer looks like:
Proof by induction. Our aim is to prove that
for all n, the number of combinations of n bool variables
is 2^n. It will suffice to show that [two cases]
-/

-- exists.intro and exists.elim
-- intro rule builds a proof of an or (or.inl/ or.inr)
-- and elim rule uses a proof of an or

/-
Test cases for question 4
#reduce all_zero_interp (a_var.mk 5)

#reduce an_interp (a_var.mk 0) = 3
#reduce an_interp (a_var.mk 1) = 7
#reduce an_interp (a_var.mk 2) = 1
#reduce an_interp (a_var.mk 4) = 0
-/