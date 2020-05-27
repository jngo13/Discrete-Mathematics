/-
some type
variant type

ordered pair type, prod

-/
namespace hidden

inductive prod_nat_nat :Type
| mk : nat → nat → prod_nat_nat

--parametric polymorphism
-- similar to generics
inductive prod_S_T (S T :Type) : Type
| mk : S → T → prod_S_T

def p1:= prod_nat_nat.mk 5 0
def p2 := prod_nat_nat.mk 3 2

--polymorphic
--def p03 := prod_S_T.mk "yo" "kaitlin"

def p3:= prod_S_T.mk 3 0
def p4:= prod_S_T.mk tt ff
def p5:= prod_S_T.mk "hello" 3


#reduce p1

--first
def first: prod_nat_nat → nat:=
    λ (p: prod_nat_nat),
        match p with
        |(prod_nat_nat.mk x _) := x
        end

#eval first p1
#eval first p2

def p_first (S T: Type): (prod_S_T S T) → S:=
    λ (p : prod_S_T S T),
        match p with
        |(prod_S_T.mk x _) := x
end

--sideways t = turnstile in logic, return type
/-we constructed p, now we have to destruct p -> cracking 
it open so you can see and use the pairs-/

--swap

def swap: prod_nat_nat → prod_nat_nat:=
    λ (p: prod_nat_nat),
        match p with
        |(prod_nat_nat.mk x y) := (prod_nat_nat.mk y x)
end

#eval swap p1
#eval swap p2

--second

def second: prod_nat_nat → nat:=
    λ (p: prod_nat_nat),
        match p with
        |(prod_nat_nat.mk _ y) := y
        end

#eval second p1
#eval second p2

def p_second (S T: Type): (prod_S_T S T) → T:=
    λ (p : prod_S_T S T),
        match p with
        |(prod_S_T.mk _ y) := y
end

#check p_second string nat p5

--set first

def set_first: prod_nat_nat → nat → prod_nat_nat:=
    λ (p: prod_nat_nat) (n: nat),
        match p with
        |(prod_nat_nat.mk x y) := (prod_nat_nat.mk n y)
end

#eval set_first p1
#eval set_first p2

--set second

def set_second: prod_nat_nat → nat → prod_nat_nat:=
    λ (p: prod_nat_nat) (n: nat),
        match p with
        |(prod_nat_nat.mk x y) := (prod_nat_nat.mk x n)
end

#eval set_first p1
#eval set_second p2

--diff
--def diff: prod_nat_nat → prod_nat_nat → prod_nat_nat := _
-- check to see if elements are equal or not pair → bool

end hidden