/-
We've seen identity functions for specific types.
For example, here are identity functions for the
types, ℕ, bool, and string.
-/

def id_nat      (a : ℕ) :       ℕ       := a
def id_bool     (a : bool) :    bool    := a
def id_string   (a : string) :  string  := a

/-
These functions differ only in the types of 
values they take and return. We don't want to
have to repeat ourselves in this way. What we
can do is to "factor out" the variation in the
types of values into a parameter, namely into 
a *type parameter.

The goal is to write a single paramterized
function definition rather than many slightly
varying copies of the essentially the same
definition. Adding a type parameter is the
solution. Our function will now take two
arguments:
- a type, α 
- a value, (a : α), of that type
-/

def dm_id' (α : Type) (a : α): α := a

#check dm_id'

#eval dm_id' bool tt
#eval dm_id' ℕ 3
#eval dm_id' string "Hello, Logic!"

def fun_id_bool := dm_id' bool
def fun_id_nat := dm_id' nat
def fun_id_string := dm_id' string

#check fun_id_bool

/-
A little thought leads us to see that
if we supply the second argument, such
as 3, to this function, Lean should be
able to infer the value of the first
argument. In this case it would be ℕ,
for example. Indeed, using underscore
instead of an explicit type name will
work: Lean will infer and fill in the
missing value!
-/

#eval dm_id' _ tt
#eval dm_id' _ 3
#eval dm_id' _ "Hello, Logic!"

/-
Even better though would be to have a
way to tell Lean to infer the missing
value without our having the explicitly
include those underscores in function
application expressions. We Lean calls
"implicit arguments" is the solution.
We tell Lean to silently infer argument
values by surrounding the argument
declarations not with parentheses but
with curly braces.
-/

def dm_id {α : Type} (a : α) : α := a
-- def dm_id' (α : Type) (a : α): α := a
-- {} tells it to infer the type with what is given

#eval dm_id tt
#eval dm_id 3
#eval dm_id "Hello, Logic!"

/-
We can now write "clean" polymorphic 
function application expressions! 
-/

/-
Note that giving explicit type arguments
is not an option here. Try it and you'll
see that Lean gives a type error. It is
expecting that you will NOT give explicit
arguments where implicit arguments are
specified.
-/

-- Try it

/-
In some cases, as we'll see later, Lean is
unable to infer the value of an implicit
argument. In such cases, you have to turn
off implicit arguments and given arguments 
explicitly within a given expression. In
these cases, you can turn off implicit
arguments on a case-by-case basis by adding
an at sign (@) to the beginning of such an
expression.
-/

#eval @dm_id bool tt
#eval @dm_id ℕ 3
#eval @dm_id string "Hello, Logic!"


/-
Now you understand exactly how Lean's
polymorphic id function works! It is 
defined in Lean's standard libraries.
-/

#eval id tt
#eval id 3
#eval id "I love this stuff!"


/-
Yay!
-/