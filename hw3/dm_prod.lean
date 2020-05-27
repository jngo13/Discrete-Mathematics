-- Justin Ngo
-- jmn4fms
-- 2/3/20
-- Sullivan 2102-001
/-
1. [30 points]

In class we implemented a polymorphic ordered
pair abstract data type that we called prod_S_T.
In a new file called dm_prod.lean re-implement
this ADT but call it dm_prod. Implement at least
the following functions:

- fst
- snd
- set_fst
- set_snd
- swap

For this part of the homework, write the function
definitions using lambda expressions and in all 
cases specific "implicit arguments" for the type
arguments of these functions.
-/

/-
2. [40 points].

After each function definition in your dm_prod.test
file, write two new equivalent function definitions,
the first one using C-style and the second using "by
cases" style. Add one prime/tick mark to the name of
each C-style function to avoid name conflicts, and
two tick marks for the "cases-style" definitions. For
all functions, specify the use of implicit arguments
for type arguments.
-/

inductive dm_prod (S T :Type) : Type
| mk : S → T → dm_prod

def fst {S T: Type}: (dm_prod S T) → S:=
    λ (p : dm_prod S T),
        match p with
        |(dm_prod.mk x _) := x
end

def snd {S T: Type}: (dm_prod S T) → T:=
    λ (p : dm_prod S T),
        match p with
        |(dm_prod.mk _ y) := y
end

def set_fst {S T : Type} : (dm_prod S T) → S → dm_prod S T :=
    λ (p : dm_prod S T) (s : S),
        dm_prod.mk s (snd p)

def set_snd {S T : Type}: (dm_prod S T) → T → dm_prod S T :=
    λ (p : dm_prod S T) (t : T),
        dm_prod.mk (fst p) t

def swap {S T: Type}: (dm_prod S T) → S → T → dm_prod T S:=
    λ (p: dm_prod S T) (s:S) (t:T),
        dm_prod.mk (snd p) (fst p)

