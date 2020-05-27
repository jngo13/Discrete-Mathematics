/-
Justin Ngo
jmn4fms
4/12/20
Sullivan 2102-001
-/

import .satisfiability
import .rules_of_reasoning

/-
CS2102 Exam #2: Propositional Logic
-/

/-
#1. Define a predicate function, is_satisfiable: pExp → bool
that returns true iff the given proposition is satisfiable.
Hint: Model your answer on our definition of is_valid. You
may need to define one or more helper functions. You should
test your solution, but we will only grade your definition.
Please write test cases in a separate file. Do not submit
that file.
-/

-- Answer here

open pExp

def foldr_or' : list bool → bool
| [] := ff
| (h::t) := bor h (foldr_or' t)

def is_satisfiable (e : pExp) : bool :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    let rs := map_pEval_over_interps e is in 
        foldr_or' rs

/-
#2. Clearly the propositions in rules_of_reasoning.lean that
are valid are also satisfiable. But what about the following?
Apply your satisfiability predicate function to decide whether
or not each of the following formulae is satisfiable or not.
Write an "#eval is_satisfiable e" command for each expression.


A. The "fallacies" in that file (the ones that aren't valid).

B. The proposition, pFalse.

C. The following propositions:

1. P ∧ ¬ P
2. P ∨ ¬ P
3. = (¬x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ ¬x4) ∧ (x1 ∨ x2 ∨ x3 ∨ ¬x4)

Note that for 3. you will have to define four new variables.
Call them x1, x2, x3, and x4.
-/

-- Answers here
-- A.
#eval is_satisfiable true_imp
#eval is_satisfiable affirm_consequence
#eval is_satisfiable affirm_disjunct
#eval is_satisfiable deny_antecedent

--B.
#eval is_satisfiable pFalse

--C.
#eval is_satisfiable (P ∧ ¬ P)
#eval is_satisfiable (P ∨ ¬ P)

def x1 := pVar (var.mk 0)
def x2 := pVar (var.mk 1)
def x3 := pVar (var.mk 2)
def x4 := pVar (var.mk 3)
#eval is_satisfiable ((¬x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ ¬x4) ∧ (x1 ∨ x2 ∨ x3 ∨ ¬x4))


/-
3. In the previous problems, you defined a satisfiability
predicate function that returns true or false depending on
whether a given formula is satisfiable or not. Often we will
want to know not only whether there exists a solution but an
actual example of a solution, if there is one. Define a function
called sat_solver : pExp → option (var → bool) that returns a
satisfying interpretation (as "some interpretation") if there
is one, or "none" otherwise. Hint: Model your solution on our
validity checker. 

1. First compute the list of interpretations for
a given expression, e, 
2. then reduce that list to a value of type
option (var → bool). 
3. Evaluate e under each interpretation in 
the list until either (A) you find one, call it i, for which e
evaluates to true, or until you reach the empty list, empty
handed. 
-/

-- Answer here

def i := pEval

def itr_find : (list bool) → (option (var → bool))
| [] := none
| (h :: t) := match h with
                | ff := option.some i
                -- option.some interp
                | _ := itr_find t
                end

def sat_solver (e : pExp) : option (var → bool) :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    let rs := map_pEval_over_interps e is in
    let x :=  itr_find rs in
        foldr_and rs

/-
3.4. determine if there is at least one interpretation of a proposition 
that makes a certain proposition true, 
and if so return that interpretation
-/

def itr_find' : (list bool) → (option (var → bool))
| [] := none
| (h :: t) := match h with
                | tt := option.some i
                -- option.some interp
                | _ := itr_find t
                end

def sat_solver' (e : pExp) : option (var → bool) :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    let rs := map_pEval_over_interps e is in
    let x :=  itr_find' rs in
        foldr_and rs                

/-
4. Define a predicate function, is_unsatisfiable : pExp → bool,
that takes a propositional logic formula, e, and returns true
iff e is unsatisfiable. Hint: Easy. Build on what you have.
-/

-- Answer here
def foldr_or'' : list bool → bool
| [] := ff
| (h::t) := bor h (foldr_or'' t)

def is_unsatisfiable (e : pExp) : bool :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    let rs := map_pEval_over_interps e is in 
    let x := foldr_or'' rs in
        not x

/-
5. Given a propositional logic expression, e, and an incorrect
claim that it's valid, we often want to produce a counter-example
to that claim. Such a counter example is an interpretation under
which the expression is not true. Equivalently, a counterexample
is an interpretation under which the *negation* of the expression
*is* true. 

Define a function, counterexample : pExp → option (var → bool),
that takes any expression e and returns either a counterexample
(as "some interpretation") or "none" if there isn't one. Hint:
given e, try to find a model for the expression, ¬ e.
-/

-- Answer here
-- option is a type, look at notes on polymorphism
def counterexample : pExp → option (var → bool)

def counter (e : pExp) : option (var → bool) :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    let rs := map_pEval_over_interps e is in
    let x :=  counterexample rs in
        foldr_and rs         

/-
6. Give an English language example for every valid rule of
reasoning in rules_of_reasoning.lean, and also give an English
language counter-example for each fallacy.

For example, for the rule, P >> Q >> P ∧ Q, you could say,
"If the ball is red then if (in addition to that) the box
is blue, then (in this context) the ball is red AND the box
is blue." It will be easiest is you re-use the same words
for P, Q, and R, in all of your examples. E.g., P means "the
ball is red", Q means "the box is blue", etc.

Copy the contents of rules_of_reasoning.lean into this comment
block and under each rule give your English language sentence.

P: Ball is red
Q: Box is blue
R: Cake is sweet

def true_intro : pExp := pTrue
- The ball is a ball

def false_elim := pFalse >> P
- If the ball is not a ball, then the ball is red

def true_imp := pTrue >> P
- If there is a ball, then the ball is red
- Not always true because not all balls are red

def and_intro := P >> Q >> P ∧ Q
- If the ball is red, then if the box is blue, then the ball 
is red and the box is blue

def and_elim_left := P ∧ Q >> P
- If the ball is red and the box is blue, then the ball is red

def and_elim_right := P ∧ Q >> Q
- If the ball is red and the box is blue, then the box is blue

def or_intro_left := P >> P ∨ Q
- If the ball is red, then the ball is red or the box is blue

def or_intro_right := Q >> P ∨ Q
- If the box is blue, then the ball is red or the box is blue

def or_elim := P ∨ Q >> (P >> R) >> (Q >> R) >> R
- If the ball is red or the box is blue, then, if the ball is red
then the cake is sweet, then, if the box is blue then the cake is sweet,
then the cake is sweet

def iff_intro := (P >> Q) >> (Q >> P) >> (P ↔ Q)
- If the ball is red then the box is blue, then, if the box is blue
then the ball is red, then, the ball is red implies the box is blue
(a red ball implies a blue box)

def iff_intro' := (P >> Q) ∧ (Q >> P) >> (P ↔ Q)
- If the ball is red then the box is blue, and if the box is blue
then the ball is red, then the ball is red implies 
the box is blue (a red ball implies a blue box)

def iff_elim_left := (P ↔ Q) >> (P >> Q)
- If the ball is red implies the box is blue, then if the
ball is red then the box is blue

def iff_elim_right := (P ↔ Q) >> (Q >> P)
- If the ball is red implies the box is blue, then if the box
is blue then the ball is red

def arrow_elim := (P >> Q) >> (P >> Q)
- If the ball is red then the box is blue, then, if the ball
is red then the box is blue

def resolution := (P ∨ Q) >> (¬ Q ∨ R) >> (P ∨ R)
- If the ball is red or the box is blue, then, if the box is not
blue or the cake is sweet, then the ball is red or the cake is sweet

def unit_resolution := (P ∨ Q) >> ((¬ Q) >> P)
- If the ball is red or the box is blue, then, if the box is not blue
then the ball is red

def syllogism := (P >> Q) >> (Q >> R) >> (P >> R)
- If the box is red then the ball is blue, then, if the ball is blue
then the cake is sweet, then if the box is red then the cake is sweet

def modus_tollens := (P >> Q) >> (¬ Q >> ¬ P)
- If the box is red then the ball is blue, then, if the ball is not blue
then the box is not red

def neg_elim := (¬ ¬ P) >> P
- If the box is not red and that is not true, then the box is red.

def excluded_middle := P ∨ (¬ P)
- The box is red or the box is not red

def neg_intro := (P >> pFalse) >> (¬ P)
- If the box is red then the box is not a box,
then the box is not red

-----
P: It is raining outside
Q: The streets are wet

def affirm_consequence := (P >> Q) >> (Q >> P)
- If it is raining outside then the streets are wet, then, if the streets
are wet it is raining outside
- Not always true because the streets can be wet without it having to rain
-- if it is NOT raining outside, then the streets can be wet = TRUE
-- if the streets are wet, then it is NOT raining outside = FALSE
-- true >> false = false

def affirm_disjunct := (P ∨ Q) >> (P >> ¬ Q)
- If it is raining outside or the streets are wet, then, if it is raining
outside then the streets are not wet
- Not always true becuase if it is raining the streets can be wet
-- if it is raining outside OR the streets are wet = TRUE
-- if if its raining outside, then the streets are NOT wet = FALSE
-- true >> false = false

def deny_antecedent := (P >> Q) >> (¬ P >> ¬ Q)
- If it is raining outside then the streets are wet, then, if it
is not raining outside then the streets are not wet
- Not always true because the streets can be wet for other reasons
besides rain
-- if it is raining outside  the streets are wet = TRUE
-- if it is NOT raining outside, then the streets can NOT be wet = FALSE
-- true >> false = false

-/