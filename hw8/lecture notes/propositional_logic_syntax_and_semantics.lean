-- justin
inductive var : Type
| mk : ℕ → var

-- SYNTAX
inductive pExp : Type
| pTrue : pExp
| pFalse : pExp
| pVar : var → pExp
| pNot : pExp → pExp
| pAnd : pExp → pExp → pExp
| pOr : pExp → pExp → pExp
| pImp : pExp → pExp → pExp
| pIff : pExp → pExp → pExp
| pXor : pExp → pExp → pExp 

-- Utility function
def bimp : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := tt
| ff ff := tt

open pExp

-- ABSTRACT SEMANTICS
def pEval : pExp → (var → bool) → bool
| pTrue _ := tt 
| pFalse _ := ff
| (pVar v) i := i v
| (pNot e) i := bnot (pEval e i)
| (pAnd e1 e2) i := band (pEval e1 i) (pEval e2 i) 
| (pOr e1 e2) i := bor (pEval e1 i) (pEval e2 i)
| (pImp e1 e2) i := bimp (pEval e1 i) (pEval e2 i)
| (pIff e1 e2) i := tt  -- HOMEWORK
| (pXor e1 e2) i := xor (pEval e1 i) (pEval e2 i)

-- CONCRETE SYNTAX ("syntactic sugar")
notation e1 ∧ e2 :=  pAnd e1 e2 --desugaring
notation e1 ∨ e2 :=  pOr e1 e2
notation ¬ e := pNot e
notation e1 > e2 := pImp e1 e2 
-- infixr ` >> ` : 30 := pImp 
notation e1 ↔ e2 := pIff e1 e2
notation e1 ⊕ e2 := pXor e1 e2

