inductive pExp : Type
| pTrue
| pFalse
| pNot : pExp → pExp --unary
-- binary operators
| pAnd : pExp → pExp → pExp
| pOr : pExp → pExp → pExp
| pImp : pExp → pExp → pExp


open pExp

def bimp : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff _ := tt

def p1 := pTrue
def p2 := pFalse
def p25 := pNot p2
def p3 := pAnd pTrue pFalse
def p4 := pOr p3 p2

def pEval : pExp → bool
| pTrue := tt
| pFalse := ff
| (pNot e) := bnot(pEval e)
| (pAnd e1 e2) := band (pEval e1) (pEval e2)
| (pOr e1 e2) := bor (pEval e1) (pEval e2)
| (pImp e1 e2) := bimp (pEval e1) (pEval e2)

#eval pEval pTrue
#eval pEval p2
#eval pEval p25
#eval pEval p3