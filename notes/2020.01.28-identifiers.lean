def z := nat.zero
#eval z

-- Bind identifer bool_true to term, tt, for Boolean true
def bool_true := tt

-- Bind the name, a_string, to the string, "I love logic!"
def a_string := "I love logic!"
#eval a_string

a_string = "logic is cool"
#eval a_string

def z' : ℕ := (nat.zero : ℕ)
def z''  := (nat.zero : ℕ)
def z''' : ℕ := nat.zero
def z := 0

-- If you want a rational or real, you'd have to say so

def q := (0 : ℚ)
def r := (0 : ℝ)
def z := (0 : ℤ)

def b := tt
#eval b

def s := "exercise"
#eval s

--Func Notes
-- Function expression are terms that have types
#check band 
#check nat.add
#check string.append

-- Function application expressions are terms that have types
#check band tt tt
#check nat.add 2 3
#check string.append "I love " "logic!"

-- Function application expessions reduce to return values
#eval band tt tt
#eval nat.add 2 3
#eval string.append "I love " "logic!"

-- Lean strictly and statically enforces typing 
#check band ff "Hi!"
#check nat.add 4 tt
#eval string.append "I love " 5 -- strange error, same problem

#check bor tt tt