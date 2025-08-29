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


-------------------------------------------------------------------------------


/--
  `equation_list_formula_set ES` := The set of all of the formulas that have an occurrence in the list of equations `ES`.
-/
def equation_list_formula_set
  (ES : List Equation) :
  Finset Formula_ :=
  List.foldr (fun (next : Equation) (prev : Finset Formula_) => {next.lhs} ∪ {next.rhs} ∪ prev) {} ES


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


lemma mem_equation_list_formula_list_imp_exists_mem_equation_list
  (F : Formula_)
  (ES : List Equation)
  (h1 : F ∈ equation_list_formula_list ES) :
  ∃ (E : Equation), E ∈ ES ∧ (F = E.lhs ∨ F = E.rhs) :=
  by
  unfold equation_list_formula_list at h1
  induction ES
  case nil =>
    simp only [List.foldr_nil, List.not_mem_nil] at h1
  case cons hd tl ih =>
    simp only [List.foldr_cons, List.mem_cons] at h1

    simp only [List.mem_cons]
    cases h1
    case inl h1 =>
      apply Exists.intro hd
      constructor
      · left
        rfl
      · left
        exact h1
    case inr h1 =>
      cases h1
      case inl h1 =>
        apply Exists.intro hd
        constructor
        · left
          rfl
        · right
          exact h1
      case inr h1 =>
        specialize ih h1
        obtain ⟨E, ih_left, ih_right⟩ := ih
        apply Exists.intro E
        constructor
        · right
          exact ih_left
        · exact ih_right


lemma mem_equation_list_imp_mem_equation_list_formula_list_left
  (E : Equation)
  (ES : List Equation)
  (h1 : E ∈ ES) :
  E.lhs ∈ equation_list_formula_list ES :=
  by
  induction ES
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    unfold equation_list_formula_list at ih
    simp only [List.mem_cons] at h1

    unfold equation_list_formula_list
    simp only [List.foldr_cons, List.mem_cons]
    cases h1
    case inl h1 =>
      left
      rewrite [h1]
      rfl
    case inr h1 =>
      right
      right
      apply ih
      exact h1


lemma mem_equation_list_imp_mem_equation_list_formula_list_right
  (E : Equation)
  (ES : List Equation)
  (h1 : E ∈ ES) :
  E.rhs ∈ equation_list_formula_list ES :=
  by
  induction ES
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    unfold equation_list_formula_list at ih
    simp only [List.mem_cons] at h1

    unfold equation_list_formula_list
    simp only [List.foldr_cons, List.mem_cons]
    cases h1
    case inl h1 =>
      right
      left
      rewrite [h1]
      rfl
    case inr h1 =>
      right
      right
      apply ih
      exact h1


-------------------------------------------------------------------------------


/--
  `Equation.var_set E` := The set of all of the variables that have an occurrence in the equation `E`.
-/
def Equation.var_set
  (E : Equation) :
  Finset String :=
  E.lhs.var_set ∪ E.rhs.var_set


/--
  `Equation.var_list E` := The list of all of the variables that have an occurrence in the equation `E`.
-/
def Equation.var_list
  (E : Equation) :
  List String :=
  E.lhs.var_list ++ E.rhs.var_list


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


/--
  `equation_list_var_list ES` := The list of all of the variables that have an occurrence in the list of equations `ES`.
-/
def equation_list_var_list
  (ES : List Equation) :
  List String :=
  formula_list_var_list (equation_list_formula_list ES)


example
  (X : String)
  (ES : List Equation) :
  X ∈ equation_list_var_set ES ↔ ∃ (F : Formula_), F ∈ equation_list_formula_list ES ∧ X ∈ F.var_set :=
  by
  unfold equation_list_var_set
  simp only [← var_occurs_in_formula_list_iff_mem_formula_list_var_set]
  unfold var_occurs_in_formula_list
  simp only [var_occurs_in_formula_iff_mem_formula_var_set]


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
