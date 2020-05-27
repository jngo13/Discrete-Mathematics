import .satisfiability
import .rules_of_reasoning
..
/-
CS2102 Exam #2: Propositional Logic
-/

-- You submitted an exam: [3 points free!]

/- [20 points]

    2 for header
    9 for reaching until list of interpretations (First 2 lines of is_satisfaible)
    4.5 for the helper function (fold_or) and 
    4.5 for calling it from is_satisfiable


#1. Define a predicate function, is_satisfiable: pExp → bool
that returns true iff the given proposition is satisfiable.
Hint: Model your answer on our definition of is_valid. You
may need to define one or more helper functions. You should
test your solution, but we will only grade your definition.
Please write test cases in a separate file. Do not submit
that file.
-/
--returns true if at least one interpretation results in 
--the expression being true
def foldr_or : list bool → bool
| [] := ff
| (h::t) := bor h (foldr_or t)


-- Answer here
def is_satisfiable (e : pExp) : bool :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    let rs := map_pEval_over_interps e is in 
    foldr_or rs



/-

[8 points]
1 point each

#2. Clearly the propositions in rules_of_reasoning.lean 
that are valid are also satisfiable. But what about the following?
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

x1...x4 are needed for last one but is not graded

-/
def x1 : pExp := pExp.pVar (var.mk 0)
def x2 : pExp := pExp.pVar (var.mk 1)
def x3 : pExp := pExp.pVar (var.mk 2)
def x4 : pExp := pExp.pVar (var.mk 3)

-- Answers here
--All satisfiable but not valid
#eval is_satisfiable true_imp
#eval is_satisfiable affirm_consequence
#eval is_satisfiable affirm_disjunct
#eval is_satisfiable deny_antecedent

--False is unsatisfiable
#eval is_satisfiable pExp.pFalse


#eval is_satisfiable (P ∧ ¬ P) --unsatisfiable
#eval is_satisfiable (P ∨ ¬ P) --satisfiable (valid)
#eval is_satisfiable ((¬x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ ¬x4) ∧ (x1 ∨ x2 ∨ x3 ∨ ¬x4))
--also satisfiable (all true)

/- 20 POINTS

-- 8 points for generating all interpretations
-- 8 points for seeing that you need to find a satisfying one
-- 4 points for returning the value correctly as an option value

3. In the previous problems, you defined a satisfiability
predicate function that returns true or false depending on
whether a given formula is satisfiable or not. Often we will
want to know not only whether there exists a solution but an
actual example of a solution, if there is one. Define a function
called sat_solver : pExp → option (var → bool) that returns a
satisfying interpretation (as "some interpretation") if there
is one, or "none" otherwise. Hint: Model your solution on our
validity checker. First compute the list of interpretations for
a given expression, e, then reduce that list to a value of type
option (var → bool). Evaluate e under each interpretation in 
the list until either (A) you find one, call it i, for which e
evaluates to true, or until you reach the empty list, empty
handed. 
-/


-- Answer here
--helper function
def reduce_interpretations : pExp → list (var → bool) → option (var → bool)
| e list.nil := none
| e (h::t) := match (pEval e h) with
        | tt := some h
        | ff := reduce_interpretations e t
        end


def sat_solver (e : pExp) : option (var → bool) :=
    let n := number_of_variables_in_expression e in
    let is := interpretations_for_n_vars n in
    reduce_interpretations e is


-- Example (OPTIONAL)
#reduce sat_solver (P ∧ Q >> (¬ P))


-- for getting the truth value you can also do (OPTIONAL)

def option_to_interp'' : option (var → bool) → (var → bool)
| none := λ (v : var), ff
| (some i) := i

#reduce option_to_interp'' (sat_solver (P ∧ Q >> (¬ P)))

#eval pEval (P ∧ Q >> (¬ P)) (option_to_interp'' (sat_solver (P ∧ Q >> (¬ P))))
    


/- [10 points] All or nothing/ Just make sure it works

4. Define a predicate function, is_unsatisfiable : pExp → bool,
that takes a propositional logic formula, e, and returns true
iff e is unsatisfiable. Hint: Easy. Build on what you have.
-/

-- Answer here

-- 3 different ways:

--1
---------------------------------------------------------------------
def is_unsatisfiable (e : pExp) : bool := ¬ (is_satisfiable e)
---------------------------------------------------------------------
--2
---------------------------------------------------------------------
def F_to_T : list bool → list bool
| [] := []
| (h::t) := ((¬h) :: F_to_T t)

def is_unsatisfiable' (e : pExp) : bool :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in 
    let rs := map_pEval_over_interps e is in 
    let ft := F_to_T rs in 
    foldr_and ft
---------------------------------------------------------------------
--3
---------------------------------------------------------------------
def is_unsatisfiable'' : pExp → bool
| e := match (sat_solver e) with
        | none := tt
        | _ := ff
        end
---------------------------------------------------------------------

-- For proof checking check these propositions

#eval is_unsatisfiable ((P ∧ ¬ Q) ∨ ((Q ∧ ¬ P)))        --ff
#eval is_unsatisfiable ((P ∧ ¬ Q))                      --ff
#eval is_unsatisfiable (P ∧ ¬ P)                        --tt
#eval is_unsatisfiable pExp.pFalse                      --tt
#eval is_unsatisfiable pExp.pTrue                       --ff



/- [15 points]

4 => for finding list of interps
8 points => Find which interps work as a counter example (match...with or if..else or simply called sat_solver with ¬e)
3 => returning as an option


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
-- 2 different ways
--1
---------------------------------------------------------------------
def mk_counter_example : pExp → list (var → bool) → option (var → bool)
| e list.nil := none
| e (h::t) := match (pEval e h) with
        | ff := some h
        | tt := mk_counter_example e t
        end

def counter_example (e : pExp) : option (var → bool) :=
    let n := number_of_variables_in_expression e in
    let is := interpretations_for_n_vars n in
    mk_counter_example e is
---------------------------------------------------------------------
--2
---------------------------------------------------------------------
def counter_example' (e : pExp) : option (var → bool) :=
    let n := number_of_variables_in_expression e in
    let is := interpretations_for_n_vars n in
    sat_solver (¬ e)
---------------------------------------------------------------------


-- OPTIONAL for checking

def option_to_interp : option (var → bool) → (var → bool)
| none := λ (v : var), ff
| (some i) := i

#reduce pEval deny_antecedent (option_to_interp (counter_example' deny_antecedent))




/- ONE POINT EACH (24 points)

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
-/

--english examples etc.

/-
def true_intro : pExp := pTrue

True is true.

def false_elim := pFalse >> P

False implies anything.
If false is true then anything is true.

def true_imp := pTrue >> P

Fallacy.
True implies anything.
If true is true then anything is true. 
If 1=1 then 1=0.

def and_intro := P >> Q >> P ∧ Q

If it's raining then if the streets 
are wet then it's raining and the streets are wet.


def and_elim_left := P ∧ Q >> P

If it's raining and the streets are wet then it's raining.

def and_elim_right := P ∧ Q >> Q

If it's raining and the streets are wet then the streets are wet.


def or_intro_left := P >> P ∨ Q

If it's raining then it's raining or the the streets are wet.


def or_intro_right := Q >> P ∨ Q

If the streets are wet then it's raining or the the streets are wet.

------------------------------------------------------------------------------ (First 8)

def or_elim := P ∨ Q >> (P >> R) >> (Q >> R) >> R

If it's raining or the sprinkler is running, then if whenever its
raining the streets are wet, then if whenever the sprinkler is running
the streets are wet, then the streets are wet.


def iff_intro := (P >> Q) >> (Q >> P) >> (P ↔ Q)

If it's the case that if it's spring the flowers are blooming, and 
then it's also the case that if the flowers are blooming then it's
springtime, then the flowers are blooming if and only if it's spring.


def iff_intro' := (P >> Q) ∧ (Q >> P) >> (P ↔ Q)

If it's the case that if it's spring the flowers are blooming, and 
it's also the case that if the flowers are blooming then it's
springtime, then the flowers are blooming if and only if it's spring.



def iff_elim_left := (P ↔ Q) >> (P >> Q)

If the flowers are blooming if and only if it's spring, then if the 
flowers are blooming then it's spring. 

def iff_elim_right := (P ↔ Q) >> (Q >> P)

If the flowers are blooming if and only if it's spring, then if it's
spring then the flowers are blooming. 


def arrow_elim := (P >> Q) >> (P >> Q)

If whenever it's raining the streets are wet, then if it's raining, 
the streets are wet. 


def resolution := (P ∨ Q) >> (¬ Q ∨ R) >> (P ∨ R)

If the pizza is hot (P) or the soda is cold (Q), then if the soda is
warm (¬ Q) or the cheese sticks are tasty (R), then the pizza is hot
or the cheese sticks are tasty.

def unit_resolution := (P ∨ Q) >> ((¬ Q) >> P)

If the pizza is hot or the soda is cold, then if the soda is not cold,
the pizza must be hot.

-------------------------------------------------------------------------------------- (Middle 8)


def syllogism := (P >> Q) >> (Q >> R) >> (P >> R)

If being sick makes you sad, and being sad makes you cry, then
being sick makes you cry.

def modus_tollens := (P >> Q) >> (¬ Q >> ¬ P)

If being sick makes you cry, then if you're not crying you must 
not be sick.

def neg_elim := (¬ ¬ P) >> P

If a natural number, n, is not not even, then n is even. 

If you're not not happy, then you're happy.
(The connotation of not not happy in English is not really exactly
the same as the connotation of happy. So here the English and the 
logic don't quite align.)

def excluded_middle := P ∨ (¬ P)

A natural number, n, is even or n is not even.

def neg_intro := (P >> pFalse) >> (¬ P)

If the assumption that a = b let's you deduce something that's 
impossible, then a=b can't be true, and must be false. 

def affirm_consequence := (P >> Q) >> (Q >> P)

If it's raining then the streets are wet, then if the streets are wet
it must be raining. This is fallacy, as the streets could be wet even if
it's not raining (by other causes).

def affirm_disjunct := (P ∨ Q) >> (P >> ¬ Q)

Professor Foo is great or Prof. Bar is great, so if Prof. Foo is great
then Prof. Bar must not be. This is also a fallacy, as both can be great.


def deny_antecedent := (P >> Q) >> (¬ P >> ¬ Q)

If it's raining means the streets are wet, then if it's not raining the
streets must be dry. Also a fallacy, for the same reason as above. The
streets could be wet even it's not raining. Maybe someone spilled their 
drink.
-------------------------------------------------------------------------------- (Last 8)

-/