def apply {α β : Type} (f : α → β) (a : α) : β := 
f a

#eval apply nat.succ 1
#eval apply nat.pred 1
#eval apply string.length "I love logic!" --type string to nat, α string and β nat

/-
Returns function as a result
-/

def apply_twice {α : Type} (f : α → α): α → α :=
--takes a function and returns a function as a result
    λ a, f (f a) -- a function that takes an argument a 
                    --and returns f applied twice to a

#reduce apply_twice nat.succ
#reduce apply_twice nat.pred

def double (n : ℕ) := 2*n

#eval apply_twice nat.succ 3 -- application is left associative
#eval apply_twice nat.pred 3
#eval (apply_twice double) 3

def square (n : ℕ) := n^2

def square_twice := apply_twice square
def double_twice := apply_twice double

#eval square_twice 5

--if you want to return a function you have to use a lamda expression

/-
That's composition of a function with itself,
but we can also compose different functions.
Here's a special case
-/