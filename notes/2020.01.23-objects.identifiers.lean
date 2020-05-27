def b := tt -- "":="" binds
def s := "hello"
def n := 5

#eval tt
#eval b
#eval s
#eval n

/-
mutable store. storing values in 
memory that can be "overwritten"
-/

/-
imperative vs functional
command vs expression 
mutable vs immutable
variable vs identifier
-/

/-
Types
Every term has exactly one type
A type defines a set of terms
These sets are disjoint
-/

#check true -- checks the type, true is a logical proposition
#check 0
#check "hello"
#check tt
#check prod.mk 2 "hi"

#check bool
#check string
#check ℕ --backslash + nat

#check Type 0
#check Type

#check Prop
#check Sort 0
#check Sort 1

/-
Identifiers and bindings
-/

def b' : bool := tt -- "":="" binds
-- binds b' to type bool, binds to tt
def b'' := tt

-- type interference, it can guess what types you are talking abnout

def s' : string := "hello"
def n' : ℕ := 5
-- Cannot begin an identifier with a number

/-
Functions and their application
-/

--Abstract data type - packaged up data types with functions

#eval band tt tt
-- function application term/ application
-- band is bound to a function and applied to two arguments
#eval tt && tt

#eval nat.add 3 4

#eval string.append "Hello, " "Logic!"
#eval "Hello, " ++ "Logic!"

#check band