import .exam2
--import .satisfiability


#eval is_satisfiable true_intro
#eval is_satisfiable false_elim
#eval is_satisfiable true_imp
#eval is_satisfiable true_intro 
#eval is_satisfiable false_elim 
#eval is_satisfiable  and_intro 
#eval is_satisfiable  and_elim_left 
#eval is_satisfiable  and_elim_right 
#eval is_satisfiable  or_intro_left 
#eval is_satisfiable  or_intro_right 
#eval is_satisfiable  or_elim 
#eval is_satisfiable  iff_intro 
#eval is_satisfiable  iff_intro' 
#eval is_satisfiable  iff_elim_left
#eval is_satisfiable  iff_elim_right 
#eval is_satisfiable  arrow_elim 
#eval is_satisfiable  resolution 
#eval is_satisfiable  unit_resolution 
#eval is_satisfiable  syllogism 
#eval is_satisfiable  modus_tollens 
#eval is_satisfiable  neg_elim 
#eval is_satisfiable  excluded_middle 
#eval is_satisfiable  neg_intro 
#eval is_satisfiable  affirm_consequence 
#eval is_satisfiable  affirm_disjunct 
#eval is_satisfiable  deny_antecedent 

#eval is_unsatisfiable true_intro
#eval is_unsatisfiable false_elim
#eval is_unsatisfiable true_imp
#eval is_unsatisfiable true_intro 
#eval is_unsatisfiable false_elim 
#eval is_unsatisfiable  and_intro 
#eval is_unsatisfiable  and_elim_left 
#eval is_unsatisfiable  and_elim_right 
#eval is_unsatisfiable  or_intro_left 
#eval is_unsatisfiable  or_intro_right 
#eval is_unsatisfiable  or_elim 
#eval is_unsatisfiable  iff_intro 
#eval is_unsatisfiable  iff_intro' 
#eval is_unsatisfiable  iff_elim_left
#eval is_unsatisfiable  iff_elim_right 
#eval is_unsatisfiable  arrow_elim 
#eval is_unsatisfiable  resolution 
#eval is_unsatisfiable  unit_resolution 
#eval is_unsatisfiable  syllogism 
#eval is_unsatisfiable  modus_tollens 
#eval is_unsatisfiable  neg_elim 
#eval is_unsatisfiable  excluded_middle 
#eval is_unsatisfiable  neg_intro 
#eval is_unsatisfiable  affirm_consequence 
#eval is_unsatisfiable  affirm_disjunct 
#eval is_unsatisfiable  deny_antecedent 

#eval is_unsatisfiable (P ∧ ¬ P)