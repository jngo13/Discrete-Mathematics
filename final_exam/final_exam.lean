/-
Justin Ngo
jmn4fms
5/4/20
Sullivan 2102-001
-/

/-
CS2102 Spring 2020 Final Exam. You are
to take this exam entirely on your own.
You may not discuss it with anyone but
the instructor and TAs. The exam has 6
qustions, some with several parts. Read
the entire exam first to get a sense of
the easy and hard parts. Do the easier
parts first while letting your mind work
in the background on the harder parts.
Submit your completed exam on Collab.
The exam is due no later than 5PM sharp
***EDT*** on May 8. Please set yourself
a reminder.
-/


/-
1. You know from our study of the Boolean 
satisfiability problem that there are 2^n
possible combinations of Boolean values for
n Boolean variables. 

Your task here is to give an English 
language (quasi-formal) proof of this fact
*by induction*.

To get started, let's make the property of
natural numbers that is at issue clear by
defining "P n" to be proposition that "the
number of possible combinations of values
for *n* Boolean variables is *2^n*."

What you are to prove is the proposition
that this is true for any value of n. That
is, you are to prove ∀ n, P n.

Next, recall that a proof of a universal
generalization (such as ∀ n, P n) *by induction*
is based on the application of the *induction
principle* for for the given data type. Here 
the data type is ℕ, and the induction rule for
ℕ is as follows:

∀ {P : ℕ → Prop}, 
P 0 → 
(∀ n', P n' → P (n' + 1)) → 
∀ n, P n.

** You should assume that the number of
** combinations of zero boolean variables
** is 1.

Reading backwards, this says that if you
want to prove ∀ n, P n, it will *suffice*
to prove P 0 and ∀ n', P n' → P (n' + 1)).
The reason is that you can then apply the
rule to deduce that ∀ n, P n must be true.
In other words, you can reduce the task of
proving ∀ n, P n to the tasks of proving
the two antecedents of this conclusion in
the induction rule.

This induction principles tells you exactly
what needs to be done. We give you the start
of a quasi-formal proof. You must complete it.
-/

-- Answer
/-
Theorem: For any natural number, n, the
number of combinations of values for n
Boolean variables is 2^n.

Proof: By induction. To prove ∀ n, P n,
where P is defined to be the proposition,
"the number of possible combinations of
values for n Boolean variables is 2^n,"
it will suffice ... <the rest of your
answer here>. 
-/

/- **** ANSWER ****
It will suffice to show that "∀ n, P n" is true for 
all natural numbers.

Assume that n is an arbitrary but specific natural number.

1. It will sufffice to show that it is true for the base case
    n = 0 or 0 (P 0 →)
2. And to show that it is true for n+1 ((∀ n, P n → P (n + 1)) → ),
    assuming it is true for n.

For any natural number n, if the number of combinations
of n boolean variables is 2^n, then the number of combinations
of n+1 boolean variables is 2^(n+1).
And thus holds true for all natural numbers.

PROOF:
Given
-- Number of combinations of 0 boolean variables is 1
And assumming
-- P n = 2^n

-- 2^n = 2^(n-1) * 2 [by property of exponents]
Therefore,
-- 2^(n+1) = 2^n * 2
-- P (n+1) = (P n) * 2
-- P (n+1) = 2^n * 2 
and since
-- 2^n * 2 = 2^(n+1), 
the number of combinations of n+1 boolean variables is 2^(n+1)

Thus
P (n+1) = 2^(n+1)
QED
-/

/- 2.
Consider the following proposition.
-/

def aProp :=    ∀ (α : Type), ∀ (Heavy Charmed: α → Prop),
                (∃ (a : α), Heavy a ∧ Charmed a) →
                (∃ (a : α), Charmed a)

/- 2a. Give an English language rendition 
of this proposition. In plain English, what
does it say?
-/

/-  **** Answer ****
Suppose we have an object of type α;
Suppose "heavy" and "charmed" are objects/ properties
of type alpha
If there exists an object "a" of this type
and "a" is both heavy and charmed,
THEN there exists an object that is charmed 
-/

/- 2b. Give a formal proof of it.
-/

example : aProp := 
    λ a,
        λ H C, -- Heavy, Charmed
            λ heavy_and_charmed,
                match heavy_and_charmed with
                    | exists.intro fred pf_fred_charmed :=
                        match pf_fred_charmed with
                            | and.intro c h := (exists.intro fred pf_fred_charmed.right)
                        end
                end

/- 2c. Give a quasi-formal, English-language
proof of it. Try to be guided by your formal
proof. Justify each step in your proof by
naming the inference rule that you're using.
-/

-- Your answer here
/- **** Answer ****
Assume we have an object a of type alpha 
Assume that the object a of type alpha has properties
heavy and charmed. 
Assumming there exists an object a that is both heavy
and charmed.
Deconstruct this assumption to prove that there 
exists an object fred which is heavy and charmed
by doing case analysis.
And further deconstruct the assumption of a heavy
and charmed object, fred, to get a proof that 
there exists an object that is charmed.
-/


/- 3. 
Consider the following proposition.
-/

def aProp2 :=   ∀ (α : Type), ∀ (Heavy Charmed: α → Prop),
                (∃ (a : α), Heavy a ∨ Charmed a) →
                (∃ (a : α), Heavy a) ∨ (∃ (a : α), Charmed a)



/- 3a. Give an English language rendition 
of this proposition. In plain English, what
does it say?
-/

/- **** Answer ****
Suppose we have an object of type α;
Suppose "heavy" and "charmed" are objects/ properties
of type alpha
If there exists an object "a" of this type
such that "a" is heavy or charmed,
THEN there either exists an object that is heavy OR
there exists an object that is charmed 
-/

/- 3b. Give a formal proof of it.
-/

example : aProp2 :=
    λ a, 
        λ H C, -- Heavy, Charmed
            λ heavy_or_charmed,
                match heavy_or_charmed with
                    | exists.intro fred pf_fred_either_heavy_or_charmed :=
                        match pf_fred_either_heavy_or_charmed with
                            | or.inl h := or.inl (exists.intro fred h)
                            | or.inr c := or.inr (exists.intro fred c)
                        end
                end

/- 3c. Give a quasi-formal, English-language
proof of it. Try to be guided by your formal
proof. Justify each step in your proof by
naming the inference rule that you're using.
-/

-- Your answer here
/- **** Answer ****
Assume we have an object a of type alpha 
Assume that the object a of type alpha has properties
heavy and charmed. 
Assumming there exists an object a that is either heavy
or an object a that is charmed.
Deconstruct this assumption to prove that there 
exists an object fred which is heavy or there exists
an object fred that is charmed by doing case analysis.

And further deconstruct the assumption of a heavy
or charmed object, fred, to get a proof that 
there exists an object that is heavy or there exists
an object that is charmed.
-/

/- 4.
Formally specify the syntax and semantics
of a language of *arithmetic* expressions that
can include variables, where the meaning of
an expression is (reduces to) a natural number.

Hint: model your answer on our specification
of the syntax and semantics of *propositional
logic* expressions.
-/

/- In this language, an interpretation will
map variables to natural numbers rather than
to Boolean values. We'll give you a start on
a solution by defining 

(1) a type of variables that are distinguished 
    from one another by a ℕ-valued index, 

(2) specifying the type of an interpretation, and 

(3) giving an example of an interpretation 
    in which all variables have the value zero.
-/

-- our variable type
structure a_var : Type := mk :: (index : ℕ)


-- friendly names for a few variables
def X_var := a_var.mk 0
def Y_var := a_var.mk 1
def Z_var := a_var.mk 2

-- the type of an interpretation
def interp := a_var → ℕ 

-- one possible interpretation, "all zero"
def all_zero_interp : interp := 
    λ v, 0

/-
4a. Define an interpretation in which X has
value 3, Y has value 7, and Z has value 1,
and all other variables have value 0.
-/

def an_interp : interp :=
    λ (v : a_var),
        match v with
            | a_var.mk 0 := 3 -- X
            | a_var.mk 1 := 7 -- Y
            | a_var.mk 2 := 1 -- Z
            | _ := 0
        end

/-
4b. Define the syntax of your language to have
the following kinds of expressions. 

- ℕ literal expression
- ℕ variable expression
- expression + expression
- expression * expression

Do this by defining an inductive type, aexp, 
the values of which are arithmetic expressions
in our language. Call your constructors lit, 
var, add, and mul. When you succeed, the test
expressions we give you should type check.
-/

inductive aexp : Type
-- fill in constructors here
| lit : ℕ → aexp
| var : a_var → aexp
| add : aexp → aexp → aexp
| mul : aexp → aexp → aexp
open aexp

-- These expressions should type-check
def X := aexp.var X_var
def Y := aexp.var Y_var
def Z := aexp.var Z_var
def l6 := aexp.lit 6
def e1 := aexp.add X Y
def e2 := aexp.mul X Z
def e3 := aexp.mul e1 l6

/-
4c. Define a semantics for your
language so that expressions evaluate
to natural numbers as they would using
the standard notions of addition and
multiplication. Furthermore, literal
expressions should evaluate to their
natural numbers arguments, and variable
expressions should evaluate the natural
numbers according to an interpretation
given to the evaluation function (call
it aEval). Remember to put constructor
expressions in parentheses when using
pattern matching / destructuring. When
you've succeeded, the test cases we've
provided should all pass.
-/

-- Your answer here
def aEval : aexp → interp → ℕ 
-- fill in cases here
| (lit v) i := v
| (var v) i := i v
| (add e1 e2) i := (aEval e1 i) + (aEval e2 i)  
| (mul e1 e2) i := (aEval e1 i) * (aEval e2 i)

-- Test cases that should pass when you've succeeded
example : aEval X an_interp = 3 := rfl
example : aEval Y an_interp = 7 := rfl
example : aEval Z an_interp = 1 := rfl
example : aEval l6 all_zero_interp = 6 := rfl
example : aEval e1 all_zero_interp = 0  := rfl
example : aEval e2 an_interp = 3 := rfl
example : aEval e3 an_interp = 60 := rfl


/-
5. Explain concisely but also precisely how a
proof of a proposition, P, "by contradiction"
would be carried out. Be sure to point out
exactly where negation elimination is involved.

Then explain concisely and precisely how a
proof of a proposition, ¬ P, would be carried
out. 
-/

/- **** Answer ****
To prove proposition P "by contradiction",
Assume P is false which also assumes that ¬P
is assumed to be true.
Prove that the results of these assumptions 
contradict each other because it violates the 
law of the excluded middle: either P is true OR
¬P is true. Once the proof is reduced to ¬ (¬ P),
negation elimination can be used to deduce that P
is true.

To prove ¬ P, assume P is true and show that 
this leads to a contradiction, then from that 
derive a proof of P being false, 
and use false.elim to finish the proof. 
This is called a "proof by negation". 
This shows ¬ (¬ P) is false. 
And then, according to the the classical principle of 
negation elimination, ¬P can be deduced true.
-/

/- 6. A simplish proof. Give a formal proof
of the following proposition. Then explain
briefly in English why the proposition must
be true no matter what propositions P and Q
are.
-/

example : ∀ (P Q R : Prop), ¬ ((P ∧ ¬ Q) ∧ (Q ∧ ¬ R)) :=
    λ P Q R,
        (λ wholeprop,
           (let pandnq := wholeprop.left in
            let qandnr := wholeprop.right in
            let nq := pandnq.right in
            let q := qandnr.left in
            false.elim (nq q)
            )
        )
           
-- Your explanation
/- **** Answer ****
A proof of a negation is a proof that some proposition
implies false, in this case
¬ ((P ∧ ¬ Q) ∧ (Q ∧ ¬ R)) where ((P ∧ ¬ Q) ∧ (Q ∧ ¬ R))
must be proven false.
If X = ((P ∧ ¬ Q) ∧ (Q ∧ ¬ R)),
In order to prove a proposition ¬X, we have to prove
X implies false. So assume X can lead to a contradiction.

Isolating Q and ¬Q in this proof X, the two contradict
each other and both Q and ¬Q cannot be true because of
the law of the excluded middle. Q and ¬Q are isolated
using let...in statements to retrieve the separated
Q and ¬Q in the proof.
Thus, Q ∧ ¬Q will always be false 
no matter what P and R are. 
And by appyling false.elim, the proof of a 
negation Q and ¬Q evaluates to false,
and the entire proof is deduced to be true.
-/
