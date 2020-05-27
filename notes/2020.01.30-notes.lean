--Takes any nat and returns 0
#check (λ (n : nat), 0) --function takes n of type nat and returns 0

-- Takes and two nat and returns the same nat
#check (λ (n:nat), n)

-- Takes any two nat and returns (a+b)
#check (λ (a b :nat), a+b)

--Takes a, b, c type nat and returns ax^2 + bx + c
#check (λ (a b c x:nat), a*x^2+b*x^2+c)

#check (fun (a b c x:nat), a*x^2+b*x+c) 1 2 3 10
#eval (fun (a b c x:nat), a*x^2+b*x+c) 1 2 3 10
#eval (λ (a b :nat), a+b) 3 4

-- binding names to functions

def z:= λ (n: nat), 0

/-
namespace hidden
def id_nat := λ(n:nat), n
end hidden

#check id
#check hidden.id_nat
-/

def id_nat:=λ(n:nat), n
def add:= λ(a b:nat), a+b
def quad:= λ(a b c x: nat), a*x^2 + b*x + c

--function application expressions

#eval z 5
#eval id_nat 5
#eval add 2 3
#eval quad 1 2 3 10

--Lean has type reference, thats how it knows some types

-- C-Style
def z' (n:nat) :=0
#reduce z'

--By cases
def z'' : nat → nat
|_:=0

--By cases
def id_nat'': nat→ nat
| n:=n

-- C style

def quad'(a b c x: nat):=
    a*x^2 + b*x + c

-- By cases
def quad'': nat → nat → nat → nat → nat
| a b c x:= a*x^2 + b*x + c

-- Defining things with different styles

-- Multiple types of arguments
def if_then_else (b:bool) (n m : nat) :=
    match b with --match b with possible constructors
    -- C style
    | tt :=n
    | ff := m
    end

--Lamda style
def my_ite: bool → nat → nat → nat :=
    λ (b : bool) (n m : nat), -- argument types separated
        match b with
        | tt:=n
        | ff:= m
    end

--No name, basically if then else
def my_ite' : bool → nat → nat → nat
| tt n m := n
| ff m n := m
--| _ _ m := m ->otherwise ignore the first arg and return the second

/-
Error message if misspelling tt to t

equation compiler error, 
equation #2 has not been used in the 
compilation (possible solution: 
delete equation)
-/