/-
CS 2102 Spring 2020, Sullivan, Exam #1

READ THIS:Put away all electronics except for 
your laptops. Included in the list are watched
and headphones. Do not access *any* electronics
at all except for your laptop. Close all browser
windows and *all* other applications except for
VS Code and any browser tab you need to access 
class notes. Do not access any other browser 
tabs whatsoever. ** DISABLE ALL COMMUNICATION
APPS ** If you see someone cheating, say so,
as they put you at a relative disadvantage,
and you do not need to tolerate that.

Collaboration policy: Communicating with anyone
in any way about any aspect of this exam but for
the instructor is absolutely prohibited. Cases of
possible violations will be addressed in accord
with class and University policy.

Note: on this exam, you are meant to use
built-in Lean types on all problems. You
won't need to use our dm_ versions. Those
we developed just so you understand how
Lean's types are defined and how they work.

Complete the problems below. The be *sure*
to save your file to a known location on 
your machine. We suggest saving your finished
exam to your Desktop. Then upload the file to
Collab. Finally, check that you uploaded the
right file. Leave enough time at the end of
the class to make sure you've submitted the
right file.

This exam has four questions. Most have several
parts. There are 11 individual parts, adding up
to 100 points, and one extra credit question at
the end, worth 10. We strongly recommend that
you attempt the extra credit problem only after
satisfactorily completing the main part of the 
exam. 
-/



/- 1. Product types (ordered pairs) [30 points]

The concept of ordered pairs is essential
in mathematics and logic. One of the most
fundamental of data types in logic, then, 
is the type of ordered pairs.

Here is the actual definition of Lean's 
product type, prod, straight from Lean's
libraries.

structure prod (α : Type u) (β : Type v) :=
(fst : α) (snd : β)

Note that the name of the constructor is
not stated explicitly here. In this case,
Lean assumes that the constructor name is
mk. So the definition is equivalent to:

structure prod (α : Type u) (β : Type v) :=
mk :: (fst : α) (snd : β)

Furthermore, because prod is polymorphic,
so is the mk constructor function; but it
takes its type arguments implicitly. That
is just how Lean works.
-/

/- A. [6 points]

2 points per question 
All or nothing each part



Define p1, p2, and p3 as names for three
ordered pair objects, where p1 has first
element tt and second element ff; pair2 
has first element 7 and second element 49;
and pair3 has first element 5 and second
element ff. 
-/

def p1 := prod.mk tt ff
def p2 := prod.mk 7 3
def p3 := prod.mk 5 ff

/- B. [8 points]

2 each
2 free
All or nothing


Lean provides a convenient notation for
working with ordered pairs. The notation
(x, y) gets "de-sugared" to prod.mk x y.
Define p1', p2', and p3' to be the same
pairs as p1, p2, and p3, respectively,
but use this more convenient notation.
-/

def p1' := (tt,ff)
def p2' := (7, 3)
def p3' := (5, ff)


/- C. [8 points]

4 each
All or nothing (As long as it works)

The main benefit of using "structure"
rather than "inductive" when defining
a product type is that the field names
used in the type definition can also 
be used as accessor/projection funtions.
Use #eval <expr> twice, replacing the
<expr>'s with expressions using these
function names first to get/compute the
first element of p1, and then to get the
the second element of p2.
-/

#eval p1.fst
#eval p2.snd



/- D. [8 points]

4 points each => 2 for header and 2 for body 
+1 for each if they did extra credit part

Subtract 1 from header for each if student used explicit type arguments


Complete the definitions of the following
set_fst and set_snd functions. Each one is
to take an ordered pair of type prod α β,
and a value of type α for set_fst or β for
set_snd, and return a new pair where the 
first or second value is replace with the
given argument value, where the other value
is the same as in the given pair. 

You will receive 2 extra credit points for
using Lean's convenient notation for pairs
in your solutions.
-/

open prod
--Regular Versions
def set_fst {α β : Type}: prod α β → α → prod α β
| prd a := mk a prd.snd

def set_snd {α β : Type}: prod α β → β → prod α β
| prd b := mk prd.fst b

--Extra Credit Versions
def set_fst' {α β : Type}: prod α β → α → prod α β
| prd a := (a, prd.snd)

def set_snd' {α β : Type}: prod α β → β → prod α β
| prd b := (prd.fst, b)



/- 2. Inductive definitions (sequences) [30 points] 

Imperative programming languages are based on
a few basic commands: assignment, if_then_else,
and while. A program in such a language is just
a sequence of such commands. In this question,
you will show that you can use the concepts you
have learned in this class to define a hugely 
simplified imperative programming language!
-/

/- A. [6 points]

All or nothing


Define a data type (a sum type) called cmd,
the values (constructors) of which are called 
assign, ite (short for if_then_else), and while. 
These constructors take no arguments.
-/

inductive cmd : Type
| assign
| ite
| while 


/- B. [8 points]


1 for header; 
2 for blank
(5 for sequence) => All or nothing


Define a data type called program, where
a program is either blank, or is constructed
from a command (a value of type cmd) followed 
by another program. In other words, a program 
is a possibly empty sequence of commands. Your 
data type will have two constructors. Call the 
first one "blank", and the second one "seq".
The first will take no arguments (it's the
base case for your inductive definition). 
The second will take two arguments.
-/

inductive program : Type
| blank
| seq (c : cmd) (p : program)



/- C. [8 points]

8 => If entire question is correct
4 => If it has Simple mistakes
0 => Bizzare mistakes


Define prog1 to be a value of type program
with three commands in a row: first assign,
then while, then ite. (Open the program and
cmd namespaces if you wish.)
-/
open program
open cmd 
def prog1 := seq (assign) (seq (while) (seq (ite) (blank)))


/- D. [8 points]

No recurisive => 0 points
4 for simple mistakes (parenthesis)
8 for correct


One often wants to know how many lines of code
are in a program. Consider each command (cmd) in
a value of type program to be a "line of code".
Write a function called loc that takes a value
of type program as an argument and that returns
the number of commands it contains. Note that 
this function will have to be recursive, so be
sure to use "by cases" notation. Use #eval to
apply loc to prog1 to test your definition.
-/

def loc : program → ℕ 
| blank := 0
| (seq c p) := 1 + loc(p)



/- 3. Polymorphic types (binary trees) [20 points]

A binary tree of values of some arbitrary type,
α, is either empty or it is a node with a value of 
type α and two smaller trees, usually called left
and right.
-/

/- A. Data type [10 points]

10 for full
9 if {} is not used in base case.
5 for simple mistakes i.e. are going in right direction
0 for completely wrong


Define a polymorphic "tree" data type as stated,
with constructors called empty and node. (Be sure
to explicitly state the type of empty to be tree).
-/

inductive tree (α : Type) : Type
| empty{}: tree
| node (a : α) (left : tree) (right:tree): tree


/-
Here are examples of trees that you can use to
test the function that you are about to define.
This "code" will work once you correcty complete
your definition of the polymorphic tree type.
Put {} after "empty" in the first constructor 
to tell Lean to take the type argument to this
constructor implicity.
-/

def e := @tree.empty bool
def t4 := tree.node 
            tt
            (tree.node 
                ff
                (e)
                (tree.node
                    tt
                    (e)
                    (e)
                )
            )
            (tree.node
                tt
                (e)
                (e)
            ) 

-- note that e has zero nodes and t4 has 4

/- B. Function [10 points]

No recurisive => 0 points
5 for simple mistakes (parenthesis)
10 for correct


Define a function called tree_size that takes 
a tree (of α for any type α), and that returns
the number of values of this type (which is the
same as the number of nodes) in the tree. Make
type argument implicit. You may open the tree
namespace if you wish.
-/

open tree
def tree_size {α : Type}: tree α → ℕ
| (empty) := 0
| (node v l r) := 1 + tree_size l + tree_size r



/-
4. Partial functions [20 points]

A partial function is a function that is not defined 
for all values of its argument types. 

Here's an example: a function that takes two natural
numbers, a and b, and that returns a representation 
of the rational number (fraction), a/b. 

One might start with the following function. It takes
two natural numbers, a and b, and simply returns the
ordered pair, (a, b), which we will take to represent
the fraction, a/b. 
-/

def mk_rat' : ℕ → ℕ → (prod ℕ ℕ) 
| a b := (a, b)     -- notation for prod.mk a b

/-

10 for header (5 points if they attempted to use option but did not succeed)
5 for "none"
5 for "some"

10 points if partially correct and heading in right direction




The problem with this definition is that it "works"
even when b = 0, even though a/0 is always undefined. 
The problem is that the mathematical function that 
takes  two natural numbers, a and b, and returns a/b, 
is *partial*. It's undefined whenever b = 0.

Your task is to write an improved version of mk_rat',
call it mk_rat, that correctly represents this partial
function as a total function in Lean.

Hints: You will have to change the type of the mk_rat'
function. And do case analysis on the second argument.
Finally, put parenthesis around (prod ℕ ℕ) where it 
will appear in the new function type specification, so
that Lean parses your definition correctly.
-/

def mk_rat : ℕ → ℕ → option (prod ℕ ℕ)
| a 0 := none
| a b := some (a,b)


-- This one is also correct. lean infers the type

def mk_rat'' : ℕ → ℕ → option (prod ℕ ℕ) 
| a 0 := none
| a b := (a, b)



/-
5. EXTRA CREDIT. [10 points]

All or nothing

Define function, polymorphic with one type parameter, α, called
filter, that takes a value of type list α and a function,f, of 
type α → bool, and that returns a value of type list α with all
and only those elements, e, of the given list for which (f e) is
true. To test your function, define a function called is_even that
takes a natural number and returns true if it is even, otherwise
false. Finally test your filter function by applying it to the 
list [0, 1, 2, 3, 4, 5, 6] using the is_even predicate function.
The result should be the list, [0, 2, 4, 6].
-/
open list
def filter {α : Type} : list α → (α → bool) → list α 
| (nil) _ := nil
| (cons h t) f := match f(h) with 
    | tt := cons h (filter t f)
    | ff := filter t f
    end


def is_even: ℕ → bool
| n := match (n % 2) with
    | 0 := tt
    | _ := ff
    end

def l1 := [0, 1, 2, 3, 4, 5, 6]
#reduce filter l1 is_even
