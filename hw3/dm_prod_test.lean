-- Justin Ngo
-- jmn4fms
-- 2/3/20
-- Sullivan 2102-001
/-Then, in a second file called dm_prod_test.lean,
write test cases for your implementation. You
will have to import your dm_prod.lean file into
this test file so that it has access to your 
dm_prod definitions.

Your test cases should include (1) the definitions 
of three ordered pairs, p1, p2, and p3, with elements 
types of ℕ and ℕ, ℕ and bool, and bool and bool,
respectively; (2) the use of #eval or #reduce to
confirm that your functions operate as expected,
at least for these test cases.
-/
import .dm_prod

def p1 := dm_prod.mk 5 3
def p2 := dm_prod.mk 4 tt
def p3 := dm_prod.mk tt ff

#reduce fst p1
#reduce fst p2
#reduce fst p3

#reduce snd p1
#reduce snd p2
#reduce snd p3

#reduce set_fst p1 6
#reduce set_fst p2 5
#reduce set_fst p3 ff

#reduce set_snd p1
#reduce set_snd p2
#reduce set_snd p3

#reduce swap p1
#reduce swap p2
#reduce swap p3

-- C-style
def fst' {S T: Type} (p : dm_prod S T):=
    match p with
        |(dm_prod.mk x _) := x
end

def snd' {S T: Type} (p : dm_prod S T):=
    match p with
        |(dm_prod.mk _ y) := y
end

def set_fst' {S T : Type} (p: dm_prod S T) (s : S):=
    match p with
        |dm_prod.mk x y := dm_prod.mk s y
end

def set_snd' {S T : Type} (p: dm_prod S T) (t : T) :=
    match p with
        |dm_prod.mk x y := dm_prod.mk x t
end

def swap' {S T: Type} (p: dm_prod S T):=
    match p with
    |dm_prod.mk x y := dm_prod.mk y x
end

-- By case
def fst'' {S T: Type}: (dm_prod S T) → S
    |(dm_prod.mk x _) := x

def snd'' {S T: Type}: (dm_prod S T) → T
    |(dm_prod.mk _ y) := y

def set_fst'' {S T : Type} : (dm_prod S T) → S → dm_prod S T
    |(dm_prod.mk x y) (s:S) := dm_prod.mk s y

def set_snd'' {S T : Type}: (dm_prod S T) → T → dm_prod S T
    |(dm_prod.mk x y) (t:T) := dm_prod.mk x t

def swap'' {S T: Type}: (dm_prod S T) → dm_prod T S
    |(dm_prod.mk x y) := dm_prod.mk y x

#reduce fst'' p1
#reduce fst'' p2
#reduce fst'' p3

#reduce snd'' p1
#reduce snd'' p2
#reduce snd'' p3

#reduce set_fst'' p1 6
#reduce set_fst'' p2 5
#reduce set_fst'' p3 ff

#reduce set_snd'' p1 4
#reduce set_snd'' p2 ff
#reduce set_snd'' p3 tt

#reduce swap'' p1
#reduce swap'' p2
#reduce swap'' p3