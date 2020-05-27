--Namespace
namespace hidden

/-
An abstract data type combines a data type 
and a set of functions that operate on values 
of that type. As we're implementing a Boolean
algebra ADT, we define a bool data type and a
set of standard Boolean operators (functions). 
-/

-- Data type bool

-- type name: dm_bool
-- type values: dm_tt, dm_ff

inductive dm_bool: Type --Just introducing another type. dm_bool is of type "type"
| dm_tt : dm_bool --first type of dm_bool
| dm_ff : dm_bool

--def b:= dm_ff does not work bc needs namespace

/-def b1 := dm_bool.dm_tt -- needs the dm_bool. before bc its in the namespace
def b2 := dm_bool.dm_ff
-/

--Alternative to defining thats better
open dm_bool --data type has its own namespace
def b1 := dm_tt
def b2 := dm_ff

-- Functions of type bool -> something
---- unary functions

#check 0
#check 0

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

---- binary functions aka operators

/-
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

-- A shorter though less clear definition
def dm_and' : dm_bool → dm_bool → dm_bool :=
    λ(b1 b2 : dm_bool),
        match b1 with
        | dm_tt := b2
        | _ := dm_ff
        end

-- The definition of "or" is similar
def dm_or : dm_bool → dm_bool → dm_bool :=
   λ (b1 b2 : dm_bool),
    match b1 with
    | dm_ff := b2
    | _ := dm_tt
    end

end hidden -- End namespace

---- ternary functions (did not cover)

--Homework 1/28/20
dm_id: bool -> bool
-- returns the value of its argument, thus called the "identity" function

dm_or: bool -> bool -> bool
dm_xor: bool -> bool -> bool
dm_nand: bool -> bool -> bool
dm_implies: bool -> bool -> bool
dm_equiv: bool -> bool -> bool