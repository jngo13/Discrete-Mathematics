/-
Justin Ngo
jmn4fms
2/25/20
Sullivan 2102-001
-/

-- Answers to Y/N questions at bottom of file

/-inductive var : Type
| P
| Q
| R
open var-/

inductive var : Type
| mk : ℕ → var

def V_0 := var.mk 0
def V_1 := var.mk 1
def V_2 := var.mk 2
-- variables indexed by natural numbers

inductive pExp : Type
| pTrue : pExp
| pFalse : pExp
| pNot : pExp → pExp
| pAnd : pExp → pExp → pExp
| pOr : pExp → pExp → pExp
| pImp : pExp → pExp → pExp
| pFol : pExp → pExp → pExp
| pVar : var → pExp
| pIff : pExp → pExp → pExp

open pExp

def band' :  bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := ff

-- or
def bor' :  bool → bool → bool
| tt tt := tt
| tt ff := tt
| ff tt := tt
| ff ff := ff

-- implies
def bimp : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := tt
| ff ff := tt

-- follows
def bfol : bool → bool → bool
| tt tt := tt
| tt ff := tt
| ff tt := ff
| ff ff := ff

-- if and only if (iff)
def biff : bool → bool → bool
| tt tt := tt
| ff ff := tt
| _ _  := ff

/-
An interpretation is a mapping i.e,
a function, from variables
to a boolean "meanings" (values)
-/

def interp_all_false: var → bool
| _ := ff

def pEval : pExp → (var → bool) → bool
| pTrue _ := tt 
| pFalse _ := ff

/-
| (pVar P) := tt
| (pVar Q) := ff
| (pVar R) := tt
-/
|(pVar v) i := i v
-- what variable v means comes from the interpretation

| (pNot e) i := bnot (pEval e i)
| (pAnd e1 e2) i := band (pEval e1 i) (pEval e2 i) 
| (pOr e1 e2) i := bor (pEval e1 i) (pEval e2 i)
| (pImp e1 e2) i := bimp (pEval e1 i) (pEval e2 i)
| (pFol e1 e2) i := bfol (pEval e1 i) (pEval e2 i)
| (pIff e1 e2) i := biff (pEval e1 i) (pEval e2 i)

-- P ↔ Q (if and only if \iff)
-- tt tt tt
-- ff ff tt
-- _  _  ff

#eval pEval pTrue
#eval pEval pFalse
#eval pEval (pNot pTrue)
#eval pEval (pNot pFalse)

def p1 := pTrue
def p2 := pFalse
def p25 := pNot p2
def p3 := pAnd pTrue pFalse
def p4 := pOr p3 p2

#eval pEval p3
#eval pEval p4
#eval pEval (pImp p3 p4)

-- Variable expressions

def P := V_0
def Q := V_1
def R := V_2

def p5 := pVar P
def p6 := pOr (pVar P) (pVar Q)
def p7 := pAnd
            (pOr (pVar P) (pVar Q))
            (pNot (pVar Q))
        -- (P ∨ Q) ∧ (-Q)

#eval pEval p7 interp_all_false
-- needs interpretation as pEval p7

def interp_makes_p7_true : var → bool
| (var.mk 0) := tt -- basically variable P
| (var.mk 1) := ff -- basically variable Q
| (var.mk 2) := ff -- basically variable R
| (var.mk _) := ff -- for everything else

#eval pEval p7 interp_makes_p7_true

/-
Example:
(Q ∨ R) ∧ (¬ R ∧ ¬ Q) -- Not satisfiable

(P ∧ Q) → (Q ∧ P) -- VALID IMPLICATION (no matter P and Q)

¬(P ∧ Q) → (¬ P) ∨ (¬ Q) -- DeMorgan Laws
¬ (P ∨ Q) → (¬ P) ∧ (¬ Q)
-/

/-
define my_prop to be the following proposition formalized
as an expression of type pExp: (P and Q) iff (Q and P). 
Finally, answer this question: Is this proposition 
respectively unsatisfiable, satisfiable, or valid? Just 
three yes/no answers will do.
-/

def my_prop := pIff
                (pAnd (pVar P) (pVar Q))
                (pAnd (pVar Q) (pVar P))

#eval pEval my_prop interp_makes_p7_true

/-
Is this proposition respectively 
unsatisfiable? No
satisfiable? Yes
valid? Yes
-/