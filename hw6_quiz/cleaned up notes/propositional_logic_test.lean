--justin
import .propositional_logic_syntax_and_semantics

#check pAnd P Q
#check P ∧ Q
#check P ∨ Q
#check ¬ P
#check P > Q

#eval pEval P interp_all_false
#eval pEval P interp_all_true

#eval pEval Q
#eval pEval R

-- Examples of larger expressions
#eval pEval (pOr (pAnd P Q) R)    -- (P ∧ Q) ∨ R

#eval pEval ((P ∧ Q) ∨ R)
-- if you want to evaluate it, you have to do it under an interpretation

#eval pEval ((P ∧ Q) ∨ R) interp_all_false
#eval pEval ((P ∧ Q) ∨ R) interp_all_true

#eval pEval (pAnd    
                (pOr 
                    P
                    Q
                )
                (pAnd
                    P 
                    Q
                )
            )
            interp_all_true

-- Let's rewrite in nicer notation
#eval pEval ((P ∨ Q) ∧ (P ∧ Q)) interp_all_true

#eval pEval (P > Q) interp_all_false
#eval pEval (P > Q) interp_all_true


def tt_ff_interp : var → bool
| (var.mk 0) := tt-- P_var
| (var.mk 1) := ff -- Q_var
| _ := ff

#eval pEval (P > Q) tt_ff_interp

def lots_of_fun := pAnd (pOr P Q) (pNot P)
def lots_of_fun' := (P ∨ Q) ∧ ¬ P

def sat : var → bool
| (var.mk 0) := ff       -- P_var
| (var.mk 1) := tt       -- Q_var
| (var.mk _) := ff       -- otherwise



#eval pEval lots_of_fun sat

-- We have found a *satisfying solution*
-- An interpretation that makes an expression true!

-- A problem that has a solution is said to be *satisfiable*
-- A problem that has no solution is said be *unsatisfiable*
-- A problem for which every interp is a solution is said to be *valid*
-- Satisfiable but not valid


-- pAnd P (pNot P)  -- P ∧ ¬ P      -- never true
-- pOr P (pNot P)   -- P ∨ ¬ P

/-
Proof by case analysis
- P=true: true ∨ false = true
- P=false: false ∨ true = true
-/


/- VALID RULES OF REASON

-- 
(P ∧ Q) → (Q ∧ P)
¬ (P ∧ Q) → (¬ P) ∨ (¬ Q)
¬ (P ∨ Q) → (¬ P ∧ ¬ Q)

-- not valid
(P → Q) → (Q → P)
-/


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