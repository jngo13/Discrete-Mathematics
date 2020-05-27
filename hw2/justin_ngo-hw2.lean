-- Justin Ngo
-- jmn4fms
-- 2/3/20
-- Sullivan 2102-001

/-
UVa CS2102/Sullivan, Spring 2020, Homework #2

This homework assignment is due by noon on Tuesday, 
Feb 4. Submit your result through the HW#2 tab under
the Assignments category on Collab. Do so by uploading
a completed version of this file.

The goal of this assignment is to develop and evaluate 
your ability to write simple abstract data types in Lean,
comprising both inductive data definitions and definitions
of functions, in several syntactic styles, that operate 
on values of such types. 
-/

/- [49 points]

#1. In the space after this comment, first define a data 
type, dm_bool, as we did in class, with values dm_tt and
dm_ff. We will take the values of this type to represent
the Boolean algebra truth values, true and false. Then
define functions operating on values of type dm_bool that 
implement the Boolean functions, not, and, or, nand, xor, 
implies, an equiv (iff). 

Note: The heads-up announcement of a few days ago mis-stated
the types of these operations as involving values of type
bool. You must use dm_bool throughout. The point is that you
are now seeing how to specify/implement Boolean algebra, not
just to use Boolean algebra functions built in to a language.

Precede each of your function definitions with a comment
presenting the "truth table" for the function to be 
defined. Then *after* each function definition, use Lean's 
#eval or #reduce command to test it for all possible 
combinations of argument values. For example, you should
have four test cases for each binary function, for each of
the four combinations of two Boolean values. You may use 
resources  such as Wikipedia to learn the truth tables for
each of these functions if you don't already know them. 
-/

inductive dm_bool : Type
| dm_tt : dm_bool --first type of dm_bool
| dm_ff : dm_bool --second type of dm_bool

open dm_bool --data type has its own namespace
def b1 := dm_tt
def b2 := dm_ff

/-
NOT

dm_tt := dm_ff
dm_ff := dm_tt

Truth table for Boolean negation (not)

arg     res
-------------
dm_tt | dm_ff
dm_ff | dm_tt
-/

def dm_not :dm_bool → dm_bool := --backslash "to" to get the arrow
    λ (b : dm_bool), --lamda expression is defined as a function value
    --lamda can be pronounced as "a function"
    -- ...that takes in an argument b of type bool and returns a function"
        match b with
        | dm_tt := dm_ff
        | dm_ff := dm_tt
        end

#reduce dm_not dm_tt
#reduce dm_not dm_ff

/-
AND

Truth table for "and"
b1 b2 res
---------
tt tt tt
tt ff ff
ff tt ff
ff ff ff
-/

def dm_and : dm_bool → dm_bool → dm_bool :=
    λ (b1 b2: dm_bool),
        match b1, b2 with
        | dm_tt, dm_tt := dm_tt
        | dm_tt, dm_ff := dm_ff
        | dm_ff, dm_tt := dm_ff
        | dm_ff, dm_ff := dm_ff
end

#reduce dm_and dm_tt dm_tt
#reduce dm_and dm_tt dm_ff
#reduce dm_and dm_ff dm_tt
#reduce dm_and dm_ff dm_ff

/-
OR

Truth table for "or"
b1 b2 res
---------
tt tt tt
tt ff tt
ff tt tt
ff ff ff
-/

def dm_or : dm_bool → dm_bool → dm_bool :=
   λ (b1 b2 : dm_bool),
    match b1, b2 with
        | dm_tt, dm_tt := dm_tt
        | dm_tt, dm_ff := dm_tt
        | dm_ff, dm_tt := dm_tt
        | dm_ff, dm_ff := dm_ff
end

#reduce dm_or dm_tt dm_tt
#reduce dm_or dm_tt dm_ff
#reduce dm_or dm_ff dm_tt
#reduce dm_or dm_ff dm_ff

/-
NAND

Truth table for "nand"
b1 b2 res
---------
tt tt ff
tt ff tt
ff tt tt
ff ff tt
-/

def dm_nand : dm_bool → dm_bool → dm_bool :=
   λ (b1 b2 : dm_bool),
    match b1, b2 with
        | dm_tt, dm_tt := dm_ff
        | dm_tt, dm_ff := dm_tt
        | dm_ff, dm_tt := dm_tt
        | dm_ff, dm_ff := dm_tt
end

#reduce dm_nand dm_tt dm_tt
#reduce dm_nand dm_tt dm_ff
#reduce dm_nand dm_ff dm_tt
#reduce dm_nand dm_ff dm_ff

/-
XOR

Truth table for "xor"
b1 b2 res
---------
tt tt ff
tt ff tt
ff tt tt
ff ff ff
-/

def dm_xor : dm_bool → dm_bool → dm_bool :=
   λ (b1 b2 : dm_bool),
    match b1, b2 with
        | dm_tt, dm_tt := dm_ff
        | dm_tt, dm_ff := dm_tt
        | dm_ff, dm_tt := dm_tt
        | dm_ff, dm_ff := dm_ff
end

#reduce dm_xor dm_tt dm_tt
#reduce dm_xor dm_tt dm_ff
#reduce dm_xor dm_ff dm_tt
#reduce dm_xor dm_ff dm_ff

/-
IMPLIES

Truth table for "implies"
b1 b2 res
---------
tt tt tt
tt ff ff
ff tt tt
ff ff tt
-/

def dm_implies : dm_bool → dm_bool → dm_bool :=
   λ (b1 b2 : dm_bool),
    match b1, b2 with
        | dm_tt, dm_tt := dm_tt
        | dm_tt, dm_ff := dm_ff
        | dm_ff, dm_tt := dm_tt
        | dm_ff, dm_ff := dm_tt
end

#reduce dm_implies dm_tt dm_tt
#reduce dm_implies dm_tt dm_ff
#reduce dm_implies dm_ff dm_tt
#reduce dm_implies dm_ff dm_ff

/-
IFF

Truth table for "implies"
b1 b2 res
---------
tt tt tt
tt ff ff
ff tt ff
ff ff tt
-/

def dm_iff : dm_bool → dm_bool → dm_bool :=
   λ (b1 b2 : dm_bool),
    match b1, b2 with
        | dm_tt, dm_tt := dm_tt
        | dm_tt, dm_ff := dm_ff
        | dm_ff, dm_tt := dm_ff
        | dm_ff, dm_ff := dm_tt
end

#reduce dm_iff dm_tt dm_tt
#reduce dm_iff dm_tt dm_ff
#reduce dm_iff dm_ff dm_tt
#reduce dm_iff dm_ff dm_ff

/- [51 points]

#2. In a separate file called months.lean, define a new
abstract data type. It will define a data type, months,
the values of which are the names of the months. Use all
lower case names for months, e.g., january. 
-/

inductive month : Type
| january : month
| february : month
| march : month
| april : month
| may : month
| june : month
| july : month
| august : month
| september : month
| october : month
| november : month
| december : month

open month --data type has its own namespace

/-
Complete your "month" ADT definition with definitions of
two functions, next_month and is_winter_month, as follows.
However, to practice writing functions in different ways,
write each of the two functions in each of the following
styles, adding "prime" marks to the function names so as 
to avoid naming conflicts:

- lambda expression (with a match/with expression)
- C-style (with a match/with expression)
- by cases (no explicit match/with expression needed)

-/

/-
A. Given a month as an argument, return the next month in
the sequence of months of the year. E.g., the function 
application, (next_month december), will return january. 
-/

-- lambda expression (with a match/with expression)
def next_month : month → month :=
   λ (m : month),
    match m with
        | january := february
        | february := march
        | march := april
        | april := may
        | may := june
        | june := july
        | july := august
        | august := september
        | september := october
        | october := november
        | november := december
        | december := january
end

#reduce next_month january
#reduce next_month february
#reduce next_month march
#reduce next_month april
#reduce next_month may
#reduce next_month june
#reduce next_month july
#reduce next_month august
#reduce next_month september
#reduce next_month october
#reduce next_month november
#reduce next_month december

-- C-style (with a match/with expression)
def next_month' (m: month): month :=
    match m with
    | january := february
    | february := march
    | march := april
    | april := may
    | may := june
    | june := july
    | july := august
    | august := september
    | september := october
    | october := november
    | november := december
    | december := january
end

#reduce next_month' january
#reduce next_month' january
#reduce next_month' february
#reduce next_month' march
#reduce next_month' april
#reduce next_month' may
#reduce next_month' june
#reduce next_month' july
#reduce next_month' august
#reduce next_month' september
#reduce next_month' october
#reduce next_month' november
#reduce next_month' december

-- by cases (no explicit match/with expression needed)
def next_month'' : month → month
| january := february
| february := march
| march := april
| april := may
| may := june
| june := july
| july := august
| august := september
| september := october
| october := november
| november := december
| december := january

#reduce next_month'' january
#reduce next_month'' february
#reduce next_month'' march
#reduce next_month'' april
#reduce next_month'' may
#reduce next_month'' june
#reduce next_month'' july
#reduce next_month'' august
#reduce next_month'' september
#reduce next_month'' october
#reduce next_month'' november
#reduce next_month'' december

/-
B. Given a month as an argument, return the dm_bool 
value, dm_tt (representing "true"), if the given month
is a winter month (december, january, or february), 
and dm_ff otherwise. Do not use more than four pattern
matching rules.
-/

-- lambda expression (with a match/with expression)
def is_winter_month : month → dm_bool :=
   λ (m : month),
    match m with
        | january := dm_tt
        | february := dm_tt
        | december := dm_tt
        | _ := dm_ff
end

#reduce is_winter_month january
#reduce is_winter_month february
#reduce is_winter_month march
#reduce is_winter_month april
#reduce is_winter_month may
#reduce is_winter_month june
#reduce is_winter_month july
#reduce is_winter_month august
#reduce is_winter_month september
#reduce is_winter_month october
#reduce is_winter_month november
#reduce is_winter_month december

-- C-style (with a match/with expression)

def is_winter_month' (m: month) (dm_tt dm_ff: dm_bool): dm_bool:=
    match m with
        | january := dm_tt
        | february := dm_tt
        | december := dm_tt
        | _ := dm_ff
end

#reduce is_winter_month' january
#reduce is_winter_month' february
#reduce is_winter_month' march
#reduce is_winter_month' april
#reduce is_winter_month' may
#reduce is_winter_month' june
#reduce is_winter_month' july
#reduce is_winter_month' august
#reduce is_winter_month' september
#reduce is_winter_month' october
#reduce is_winter_month' november
#reduce is_winter_month' december

-- by cases (no explicit match/with expression needed)

def is_winter_month'' : month → dm_bool
    | january := dm_tt
    | february := dm_tt
    | december := dm_tt
    | _ := dm_ff

#reduce is_winter_month'' january
#reduce is_winter_month'' february
#reduce is_winter_month'' march
#reduce is_winter_month'' april
#reduce is_winter_month'' may
#reduce is_winter_month'' june
#reduce is_winter_month'' july
#reduce is_winter_month'' august
#reduce is_winter_month'' september
#reduce is_winter_month'' october
#reduce is_winter_month'' november
#reduce is_winter_month'' december