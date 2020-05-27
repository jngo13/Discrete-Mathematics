/-
Justin Ngo
jmn4fms
4/5/20
Sullivan 2102-001
-/

import .propositional_logic_syntax_and_semantics

open pExp

/-
Your task: We give you propositions in zero to 
three variables (P, Q, and, R). You must decide
whether each is valid or not. To do this, you
must use pEval to evaluate any given propositions
under each of the possible interpretations of its
variables. 

To test a 1-variable proposition will require
two interpretations; for 2 variables, four; for
three, eight, etc. In general, there are 2^n,
where n is the number of variables. Adding one
variable geometrically increases the number of
possible interpretations.
-/

/-
Here are the three propositional variables, P
Q, and R that we'll use to write propositions 
and test them here. 
-/

def P := pVar (var.mk 0)
def Q := pVar (var.mk 1)
def R := pVar (var.mk 2)

/-
Below is a list of formulae, many of which
express fundamental rules of valid reasoning.
We also state several fallacies: desceptively
faulty, which is to say invalid, non-rules of
logically sound reasoning.  

Your job is to classify each as valid or not 
valid. To do this you will produce a truth 
table for each one. It is good that we have 
an automatic evaluator as that makes the job 
easy. For each of the formulae that's not valid, 
give an English language counterexample: some 
scenario that shows that the formula is
not always true. 

To do this assignment, evaluate each proposition
under each of its possible interpretations. Each
interpretation defines the inputs in one row of
the truth table, and the result of applying pEval
to the expression under that interpetation, gives
you the truth value of the proposition under that
interpretation. 

A given proposition will be valid if it evalutes
to true under *all* of its interpretations. You
have to define some interpretations, then apply 
the pEval function to the given proposition for
each of its possible interpretation.axioms

Some of the formulae contain only one variable.
We use P. You will need two interpretations in 
this cases. Call them Pt and Pf. A one-variable
propositions has two interpretations, and thus
two rows in its truth table.

Some formula have two variables. We call them
P and Q. Now there are four interpretations. Call 
them PtQt, PtQf, PfQt, PfQf. 

Finally, some of the propositions we give you have 
three variables. Here we have eight interpretations
under which to evaluate each such proposition. You
can give them names such as PtQtRt, PtQtRf, etc. 

If we look at the sequence of t's and f's in each
of these names and rewrite t's as ones f's as zeros, 
then we see that our names basically count down from
2^n-1 to zero in binary notation.  

PQR
ttt 111 7   2^3-1
ttf 110 6
tft 101 5
tff 100 4
ftt 011 3
ftf 010 2
fft 001 1
fff 000 0   

So, for each proposition, evaluate it under each
of its possible interpretations; then look at the
list of resulting truth values. If all are true,
then you have proved that the proposition is valid.
If there is at least one interpretation under which
the proposition evaluates to true, it's decidable.
If there is no interpretation that makes it true,
then it is unsatisfiable.
-/

/- # 1. 

Define three sets of interpretations, one for each 
"arity" of proposition (1-, 2-, or 3 variables), as
explained above.
-/

-- Answer
-- Set 1
def Pt: var→ bool
| (var.mk 0) := tt
| _ := ff

def Pf: var→ bool
| (var.mk 0) := ff
| _ := tt

--Set 2
def PtQt: var→ bool
| (var.mk 0) := tt
| (var.mk 1) := tt
| _ := ff

def PtQf: var→ bool
| (var.mk 0) := tt
| (var.mk 1) := ff
| _ := ff

def PfQt: var→ bool
| (var.mk 0) := ff
| (var.mk 1) := tt
| _ := ff

def PfQf: var→ bool
| (var.mk 0) := ff
| (var.mk 1) := ff
| _ := ff

-- Set 3
def PtQtRt: var→ bool
| (var.mk 0) := tt
| (var.mk 1) := tt
| (var.mk 2) := tt
| _ := ff

def PtQtRf: var→ bool
| (var.mk 0) := tt
| (var.mk 1) := tt
| (var.mk 2) := ff
| _ := ff

def PtQfRt: var→ bool
| (var.mk 0) := tt
| (var.mk 1) := ff
| (var.mk 2) := tt
| _ := ff

def PtQfRf: var→ bool
| (var.mk 0) := tt
| (var.mk 1) := ff
| (var.mk 2) := ff
| _ := ff

def PfQtRt: var→ bool
| (var.mk 0) := ff
| (var.mk 1) := tt
| (var.mk 2) := tt
| _ := ff

def PfQtRf: var→ bool
| (var.mk 0) := ff
| (var.mk 1) := tt
| (var.mk 2) := ff
| _ := ff

def PfQfRt: var→ bool
| (var.mk 0) := ff
| (var.mk 1) := ff
| (var.mk 2) := tt
| _ := ff

def PfQfRf: var→ bool
| (var.mk 0) := ff
| (var.mk 1) := ff
| (var.mk 2) := ff
| _ := ff

/-
2. Use pEval to evaluate each of the following formulae
under each of its possible interpretations. The use the
resulting list of Boolean truth values to decide which
properties the proposition has. Here are the propositions
for which you are to decide the properties it has.
-/

def true_intro : pExp := pTrue

#eval pEval true_intro Pt
#eval pEval true_intro Pf

-- valid

def false_elim := pFalse >> P

#eval pEval false_elim Pt
#eval pEval false_elim Pf

-- valid

def true_imp := pTrue >> P

#eval pEval true_imp Pt
#eval pEval true_imp Pf

-- satisfiable
-- TRUE if it is raining outside, then the streets are wet
-- FALSE if the streets are wet, then it is raining outside
-- the streets could be wet for another reason

def and_intro := P >> Q >> (P ∧ Q)

#eval pEval and_intro PtQt
#eval pEval and_intro PtQf
#eval pEval and_intro PfQt
#eval pEval and_intro PfQf

-- valid

def and_elim_left := (P ∧ Q) >> P

#eval pEval and_elim_left PtQt
#eval pEval and_elim_left PtQf
#eval pEval and_elim_left PfQt
#eval pEval and_elim_left PfQf

-- valid

def and_elim_right := (P ∧ Q) >> Q

#eval pEval and_elim_right PtQt
#eval pEval and_elim_right PtQf
#eval pEval and_elim_right PfQt
#eval pEval and_elim_right PfQf

-- valid

def or_intro_left := P >> (P ∨ Q)

#eval pEval or_intro_left PtQt
#eval pEval or_intro_left PtQf
#eval pEval or_intro_left PfQt
#eval pEval or_intro_left PfQf

-- valid

def or_intro_right := Q >> (P ∨ Q)

#eval pEval or_intro_right PtQt
#eval pEval or_intro_right PtQf
#eval pEval or_intro_right PfQt
#eval pEval or_intro_right PfQf

-- valid

def or_elim := (P ∨ Q) >> (P >> R) >> (Q >> R) >> R

#eval pEval or_elim PtQtRt
#eval pEval or_elim PtQtRf
#eval pEval or_elim PtQfRt
#eval pEval or_elim PtQfRf
#eval pEval or_elim PfQtRt
#eval pEval or_elim PfQtRf
#eval pEval or_elim PfQfRt
#eval pEval or_elim PfQfRf

-- valid

def iff_intro :=   (P >> Q) >> (Q >> P) >> (P ↔ Q)

#eval pEval iff_intro PtQt
#eval pEval iff_intro PtQf
#eval pEval iff_intro PfQt
#eval pEval iff_intro PfQf

-- valid

def iff_intro' := ((P >> Q) ∧ (Q >> P)) >> (P ↔ Q)

#eval pEval iff_intro' PtQt
#eval pEval iff_intro' PtQf
#eval pEval iff_intro' PfQt
#eval pEval iff_intro' PfQf

-- valid

def iff_elim_left := (P ↔ Q) >> (P >> Q)

#eval pEval iff_elim_left PtQt
#eval pEval iff_elim_left PtQf
#eval pEval iff_elim_left PfQt
#eval pEval iff_elim_left PfQf

-- valid

def iff_elim_right := (P ↔ Q) >> (Q >> P)

#eval pEval iff_elim_right PtQt
#eval pEval iff_elim_right PtQf
#eval pEval iff_elim_right PfQt
#eval pEval iff_elim_right PfQf

-- valid

def arrow_elim := (P >> Q) >> (P >> Q)

#eval pEval arrow_elim PtQt
#eval pEval arrow_elim PtQf
#eval pEval arrow_elim PfQt
#eval pEval arrow_elim PfQf

def resolution := (P ∨ Q) >> (¬ Q ∨ R) >> (P ∨ R)

#eval pEval resolution PtQtRt
#eval pEval resolution PtQtRf
#eval pEval resolution PtQfRt
#eval pEval resolution PtQfRf
#eval pEval resolution PfQtRt
#eval pEval resolution PfQtRf
#eval pEval resolution PfQfRt
#eval pEval resolution PfQfRf

-- valid

def unit_resolution := (P ∨ Q) >> ((¬ Q) >> P)

#eval pEval unit_resolution PtQt
#eval pEval unit_resolution PtQf
#eval pEval unit_resolution PfQt
#eval pEval unit_resolution PfQf

-- valid

def syllogism := (P >> Q) >> (Q >> R) >> (P >> R)

#eval pEval syllogism PtQtRt
#eval pEval syllogism PtQtRf
#eval pEval syllogism PtQfRt
#eval pEval syllogism PtQfRf
#eval pEval syllogism PfQtRt
#eval pEval syllogism PfQtRf
#eval pEval syllogism PfQfRt
#eval pEval syllogism PfQfRf

-- valid

def modus_tollens := (P >> Q) >> (¬ Q >> ¬ P)

#eval pEval modus_tollens PtQt
#eval pEval modus_tollens PtQf
#eval pEval modus_tollens PfQt
#eval pEval modus_tollens PfQf

-- valid

def neg_elim := (¬ ¬ P) >> P

#eval pEval neg_elim Pt
#eval pEval neg_elim Pf

-- valid

def excluded_middle := P ∨ (¬ P)

#eval pEval excluded_middle Pt
#eval pEval excluded_middle Pf

-- valid

def neg_intro := (P >> pFalse) >> (¬ P)

#eval pEval neg_intro Pt
#eval pEval neg_intro Pf

-- valid

def affirm_consequence := (P >> Q) >> (Q >> P)

#eval pEval affirm_consequence PtQt
#eval pEval affirm_consequence PtQf
#eval pEval affirm_consequence PfQt
#eval pEval affirm_consequence PfQf

-- satisfiable
-- if it is NOT raining outside, then the streets can be wet = TRUE
-- if the streets are wet, then it is NOT raining outside = FALSE
-- true >> false = false

def affirm_disjunct := (P ∨ Q) >> (P >> ¬ Q)

#eval pEval affirm_disjunct PtQt
#eval pEval affirm_disjunct PtQf
#eval pEval affirm_disjunct PfQt
#eval pEval affirm_disjunct PfQf

-- satisfiable
-- if it is raining outside OR the streets are wet = TRUE
-- if if its raining outside, then the streets are NOT wet = FALSE
-- true >> false = false

def deny_antecedent := (P >> Q) >> (¬ P >> ¬ Q)

#eval pEval deny_antecedent PtQt
#eval pEval deny_antecedent PtQf
#eval pEval deny_antecedent PfQt
#eval pEval deny_antecedent PfQf

-- satisfiable
-- if it is raining outside  the streets are wet = TRUE
-- if it is NOT raining outside, then the streets can NOT be wet = FALSE
-- true >> false = false

axioms A B : Prop

#check A ∨ B ∧ B ∨ A
#check (A ∨ B) ∧ (B ∨ A)
#check A ∨ (B ∧ B) ∨ A

#check  A ∨ B → B ∨ A
#check  (A ∨ B) → (B ∨ A)
#check A ∨ (B → B) ∨ A

#check A → B ↔ B → A 
#check (A → B) ↔ (B → A) 
#check A → (B ↔ B) → A

#check  A ↔ B ∨ B ↔ A
#check  (A ↔ B) ∨ (B ↔ A)
#check  A ↔ (B ∨ B) ↔ A

#check A → B ∨ B → A
#check (A → B) ∨ (B → A)
#check A → (B ∨ B) → A


/-
Study the valid rules and learn their names. 
These rules, which, here, we are validating 
"semantically" (by the method of truth tables)
will become fundamental "rules of inference",
for reasoning "syntactically" when we get to 
predicate logic. There is not much memorizing
in this class, but this is one case where you
will find it important to learn the names and
definitions of these rules.
-/