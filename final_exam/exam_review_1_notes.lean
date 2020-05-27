axiom Person : Type
axioms (Nice: Person → Prop) (Old : Person → Prop)


example :   (∃ (p : Person), Nice p ∨ Old p) → 
            (∃ (p : Person), Nice p) ∨
            (∃ (p : Person), Old p) := 
λ pno, 
    match pno with
    | exists.intro fred pf_fred_either_nice_or_old := 
        match pf_fred_either_nice_or_old with
        | or.inl n := or.inl (exists.intro fred n)
        | or.inr o := _
        end
    end 



example : (∃ (n : ℕ), n > 0) → true :=
λ h, 
    match h with
    | exists.intro v pf := _    -- not meant to be finished
    end