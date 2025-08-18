import HandbookOfPracticalLogicLean.Prop.Replace.Var.One.Rec.Replace
import HandbookOfPracticalLogicLean.Prop.Size
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


-------------------------------------------------------------------------------


/--
  `Equation.var_set E` := The set of all of the variables that have an occurrence in the equation `E`.
-/
def Equation.var_set
  (E : Equation) :
  Finset String :=
  E.lhs.var_set ∪ E.rhs.var_set


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


-------------------------------------------------------------------------------


/--
  `Equation.size E` := The number of subformulas in the equation `E`.
-/
def Equation.size
  (E : Equation) :
  Nat :=
  E.lhs.size + E.rhs.size


/--
  `equation_list_size ES` := The number of subformulas in the list of equations `ES`.
-/
def equation_list_size
  (ES : List Equation) :
  Nat :=
  formula_list_size (equation_list_formula_list ES)


-------------------------------------------------------------------------------


/--
  `equation_replace_var_one_rec X F E` :=

  `X → F` in `E` for each occurrence of the variable `X` in the equation `E`

  The result of simultaneously replacing each occurrence of the variable `X` in the equation `E` by an occurrence of the formula `F`.
-/
def equation_replace_var_one_rec
  (X : String)
  (F : Formula_)
  (E : Equation) :
  Equation :=
  ⟨replace_var_one_rec X F E.lhs, replace_var_one_rec X F E.rhs⟩



/--
  `equation_list_replace_var_one_rec X F ES` :=

  `X → F` in `ES` for each occurrence of the variable `X` in the list of equations `ES`

  The result of simultaneously replacing each occurrence of the variable `X` in the list of equations `ES` by an occurrence of the formula `F`.
-/
def equation_list_replace_var_one_rec
  (X : String)
  (F : Formula_)
  (ES : List Equation) :
  List Equation :=
  ES.map (fun (E : Equation) => equation_replace_var_one_rec X F E)


#lint
