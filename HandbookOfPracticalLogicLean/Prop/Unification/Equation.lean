import HandbookOfPracticalLogicLean.Prop.Var


set_option autoImplicit false


open Formula_


/--
  The type of equations.
-/
structure Equation : Type where
  /-- The left hand side of the equation. -/
  (lhs : Formula_)

  /-- The right hand side of the equation. -/
  (rhs : Formula_)
  deriving Inhabited, DecidableEq, Repr


/--
  `equation_list_formula_list ES` := The list of all of the formulas that have an occurrence in the list of equations `ES`.
-/
def equation_list_formula_list
  (ES : List Equation) :
  List Formula_ :=
  List.foldr (fun (next : Equation) (prev : List Formula_) => next.lhs :: next.rhs :: prev) [] ES

#eval equation_list_formula_list []
#eval equation_list_formula_list [⟨var_ "P", var_ "Q"⟩]
#eval equation_list_formula_list [⟨var_ "P", var_ "Q"⟩, ⟨var_ "Q", var_ "R"⟩]
#eval equation_list_formula_list [⟨var_ "P", var_ "Q"⟩, ⟨var_ "R", var_ "S"⟩]


/--
  `equation_list_var_set ES` := The set of all of the variables that have an occurrence in the list of equations `ES`.
-/
def equation_list_var_set
  (ES : List Equation) :
  Finset String :=
  formula_list_var_set (equation_list_formula_list ES)

#eval equation_list_var_set {}
#eval equation_list_var_set [⟨var_ "P", var_ "Q"⟩]
#eval equation_list_var_set [⟨var_ "P", var_ "Q"⟩, ⟨var_ "Q", var_ "R"⟩]
#eval equation_list_var_set [⟨var_ "P", var_ "Q"⟩, ⟨var_ "R", var_ "S"⟩]


#lint
