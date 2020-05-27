/-
Suppose we want to compute a boolean value, with the 
result, true (tt), if all of the strings in a lisst of
strings has even length, and false (ff) otherwise. To
build this function, it'd  be nice to have two helper
functions: len : string → ℕ , that computes the length 
of a given string, and one, ev, that decides whether
a given natural number is even or odd. Here are such
functions.
-/

/- 
What do we have to work with?
- string length string → nat
is_even : nat → bool
composeL α → β → β → γ → α → γ 
case analysis,m [] or h::t
recusrion
-/

/-
[] = tt
["Hello"] - ff
["Hello!"] - tt
["Hello", ...]
-/


def compose {α β γ : Type} : (α → β ) → (β → γ) → (α → γ)
| f g := λ (a : α), g(f a)

def len := string.length

def ev : ℕ → bool
    | 0:=tt
    | 1:=ff
    | (n' + 2):= ev n'

def ev_string := ev ∘ len

/-
cons "Hello" nil
nil
cons "Hello" (cons "These" nil)
op: (len string h) AND (rest of the list is all even strings)
op: string → bool → bool
-/

def all_even_op:= string → bool → bool
    | s b := band (all_even_op s) b
    -- combines using band

/-
Now to reduce an entire list, we apply this function
recursively. Here's an implementation.
-/

def foldr {α β : Type} :
    /-op:-/     (α → β → β ) → 
    /-id:-/     β → 
    /-list:-/   list α → 
    /-result:-/ β 
-- by case analysis on list
| op id [] := id
| op id (h :: t) := op h (foldr op id t)

#eval foldr nat.add 0 [1,2,3,4,5,6,7,8,9,10]

def sum_list := foldr nat.add 0
def prod_list := foldr nat.mul 1
def all_ev := foldr all_even_op tt

#eval all_even_op ["ee", "eeee", "ffffff"]