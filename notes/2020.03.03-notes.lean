--def apply_n {α : Type} : (α → α) → ℕ → (α → α)
def apply_n {α : Type} : (α → α) → ℕ → α → α
| f 0 := λ ( a : α ), a
| f (nat.succ n') := 
    λ (a : α), f(( apply_n f n') a)

#eval apply_n (λ n, n^2) 2 5
#eval apply_n nat.succ 2 5

def compose {α β γ : Type} : (β → γ) → (α → β) → (α → γ) :=
λ g f,
    λ (a : α), 
        g(f a)

def is_even : ℕ → bool
| 0 := tt
| 1 := ff
| (n + 2) := is_even n

#eval (compose is_even string.length) "I love logic!"

def even_string := compose is_even string.length
-- functions are just data objects like anything else
-- can pass functions into functions

#eval even_string "justin"

def list_map {α β : Type} : (α → β) → list α → list β
| f [] := []
| f (h :: t) := (f h :: (list_map f t))

#eval list_map is_even [1,2,3,4,5]

def exclaim : string → string
| s := s ++ "!"

#eval list_map exclaim ["Hello", "Lean"]

def foldn : (ℕ → ℕ → ℕ ) → ℕ → (list ℕ) → ℕ
| op id [] := id 
| op id (h::t) := op h (foldn op id t)
-- h cons t

#eval foldn nat.add 0 [1,2,3,4,5]
#eval foldn nat.mul 1 [1,2,3,4,5]
