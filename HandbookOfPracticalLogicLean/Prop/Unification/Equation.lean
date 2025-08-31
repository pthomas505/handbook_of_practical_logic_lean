import HandbookOfPracticalLogicLean.Prop.Replace.Var.One.Rec.Replace
import HandbookOfPracticalLogicLean.Prop.Size
import HandbookOfPracticalLogicLean.Prop.Var

import MathlibExtraLean.List


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


/--
  `formula_occurs_in_equation_list F ES` := True if and only if there is an occurrence of the formula `F` in the list of equations `ES`.
-/
def formula_occurs_in_equation_list
  (F : Formula_)
  (ES : List Equation) :
  Prop :=
  ∃ (E : Equation), E ∈ ES ∧ (F = E.lhs ∨ F = E.rhs)

instance
  (F : Formula_)
  (ES : List Equation) :
  Decidable (formula_occurs_in_equation_list F ES) :=
  by
  unfold formula_occurs_in_equation_list
  infer_instance


-------------------------------------------------------------------------------


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


lemma mem_equation_list_formula_list_imp_formula_occurs_in_equation_list
  (F : Formula_)
  (ES : List Equation)
  (h1 : F ∈ equation_list_formula_list ES) :
  formula_occurs_in_equation_list F ES :=
  by
  unfold equation_list_formula_list at h1

  unfold formula_occurs_in_equation_list
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


lemma formula_occurs_in_equation_list_iff_mem_equation_list_formula_list
  (F : Formula_)
  (ES : List Equation) :
  formula_occurs_in_equation_list F ES ↔ F ∈ equation_list_formula_list ES :=
  by
  constructor
  · intro a1
    obtain ⟨E, a1_left, a1_right⟩ := a1
    cases a1_right
    case inl a1_right =>
      rewrite [a1_right]
      apply mem_equation_list_imp_mem_equation_list_formula_list_left
      exact a1_left
    case inr a1_right =>
      rewrite [a1_right]
      apply mem_equation_list_imp_mem_equation_list_formula_list_right
      exact a1_left
  · apply mem_equation_list_formula_list_imp_formula_occurs_in_equation_list


-------------------------------------------------------------------------------


lemma formula_occurs_in_equation_list_iff_mem_equation_list_formula_set
  (F : Formula_)
  (ES : List Equation) :
  formula_occurs_in_equation_list F ES ↔ F ∈ equation_list_formula_set ES :=
  by
  sorry


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
  `var_occurs_in_equation V E` := True if and only if there is an occurrence of the variable `V` in the equation `E`.
-/
def var_occurs_in_equation
  (V : String)
  (E : Equation) :
  Prop :=
  var_occurs_in_formula V E.lhs ∨ var_occurs_in_formula V E.rhs

instance
  (V : String)
  (E : Equation) :
  Decidable (var_occurs_in_equation V E) :=
  by
  unfold var_occurs_in_equation
  infer_instance


lemma var_occurs_in_equation_iff_mem_equation_var_set
  (V : String)
  (E : Equation) :
  var_occurs_in_equation V E ↔ V ∈ E.var_set :=
  by
  unfold var_occurs_in_equation
  unfold Equation.var_set
  simp only [Finset.mem_union]
  simp only [var_occurs_in_formula_iff_mem_formula_var_set]


lemma var_occurs_in_equation_iff_mem_equation_var_list
  (V : String)
  (E : Equation) :
  var_occurs_in_equation V E ↔ V ∈ E.var_list :=
  by
  unfold var_occurs_in_equation
  unfold Equation.var_list
  simp only [List.mem_append]
  simp only [var_occurs_in_formula_iff_mem_formula_var_list]


-------------------------------------------------------------------------------

/--
  `equation_list_var_set ES` := The set of all of the variables that have an occurrence in the list of equations `ES`.
-/
def equation_list_var_set
  (ES : List Equation) :
  Finset String :=
  List.foldr (fun (next : Equation) (prev : Finset String) => next.var_set ∪ prev) {} ES
  -- formula_list_var_set (equation_list_formula_list ES)

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
  List.foldr (fun (next : Equation) (prev : List String) => next.var_list ++ prev) [] ES
  -- formula_list_var_list (equation_list_formula_list ES)


/--
  `var_occurs_in_equation_list X ES` := True if and only if there is an occurrence of the variable `X` in the list of equations `ES`.
-/
def var_occurs_in_equation_list
  (X : String)
  (ES : List Equation) :
  Prop :=
  ∃ (E : Equation), E ∈ ES ∧ var_occurs_in_equation X E


-------------------------------------------------------------------------------


lemma var_occurs_in_equation_list_imp_mem_equation_list_var_set
  (X : String)
  (ES : List Equation)
  (E : Equation)
  (h1 : E ∈ ES)
  (h2 : var_occurs_in_equation X E) :
  X ∈ equation_list_var_set ES :=
  by
  induction ES
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1

    simp only [var_occurs_in_equation_iff_mem_equation_var_set] at h2

    unfold equation_list_var_set
    simp only [List.foldr_cons, Finset.mem_union]
    cases h1
    case inl h1 =>
      left
      rewrite [← h1]
      exact h2
    case inr h1 =>
      right
      unfold equation_list_var_set at ih
      apply ih
      exact h1


lemma mem_equation_list_var_set_imp_var_occurs_in_equation_list
  (X : String)
  (ES : List Equation)
  (h1 : X ∈ equation_list_var_set ES) :
  var_occurs_in_equation_list X ES :=
  by
  induction ES
  case nil =>
    unfold equation_list_var_set at h1
    simp only [List.foldr_nil, Finset.not_mem_empty] at h1
  case cons hd tl ih =>
    unfold equation_list_var_set at h1
    simp only [List.foldr_cons, Finset.mem_union] at h1

    unfold var_occurs_in_equation_list
    cases h1
    case inl h1 =>
      apply Exists.intro hd
      constructor
      · simp only [List.mem_cons]
        left
        exact trivial
      · simp only [var_occurs_in_equation_iff_mem_equation_var_set]
        exact h1
    case inr h1 =>
      unfold var_occurs_in_equation_list at ih
      unfold equation_list_var_set at ih
      specialize ih h1
      obtain ⟨E, ih_left, ih_right⟩ := ih

      apply Exists.intro E
      constructor
      · simp only [List.mem_cons]
        right
        exact ih_left
      · exact ih_right


lemma var_occurs_in_equation_list_iff_mem_equation_list_var_set
  (X : String)
  (ES : List Equation) :
  var_occurs_in_equation_list X ES ↔
  X ∈ equation_list_var_set ES :=
  by
  constructor
  · intro a1
    unfold var_occurs_in_equation_list at a1
    obtain ⟨E, a1_left, a1_right⟩ := a1
    apply var_occurs_in_equation_list_imp_mem_equation_list_var_set X ES E
    · exact a1_left
    · exact a1_right
  · apply mem_equation_list_var_set_imp_var_occurs_in_equation_list


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


example
  (X : String)
  (F : Formula_)
  (ES : List Equation)
  (h1 : X ∉ equation_list_var_set ES) :
  equation_list_replace_var_one_rec X F ES = ES :=
  by
  unfold equation_list_replace_var_one_rec
  apply List.fun_is_id_on_mem_imp_map_eq_self
  intro E a1
  unfold equation_replace_var_one_rec
  congr
  · apply not_var_occurs_in_replace_var_one_rec_self
    intro contra
    apply h1
    simp only [← var_occurs_in_equation_list_iff_mem_equation_list_var_set]
    unfold var_occurs_in_equation_list
    apply Exists.intro E
    constructor
    · exact a1
    · unfold var_occurs_in_equation
      left
      exact contra
  · apply not_var_occurs_in_replace_var_one_rec_self
    intro contra
    apply h1
    simp only [← var_occurs_in_equation_list_iff_mem_equation_list_var_set]
    unfold var_occurs_in_equation_list
    apply Exists.intro E
    constructor
    · exact a1
    · unfold var_occurs_in_equation
      right
      exact contra


lemma var_occurs_in_equation_equation_replace_var_one_rec
  (X : String)
  (F : Formula_)
  (E : Equation)
  (h1 : var_occurs_in_equation X (equation_replace_var_one_rec X F E)) :
  var_occurs_in_formula X F :=
  by
  unfold equation_replace_var_one_rec at h1
  unfold var_occurs_in_equation at h1
  simp only at h1
  cases h1
  case inl h1 =>
    apply var_occurs_in_formula_replace_var_one_rec X F E.lhs
    exact h1
  case inr h1 =>
    apply var_occurs_in_formula_replace_var_one_rec X F E.rhs
    exact h1


lemma var_occurs_in_equation_list_equation_list_replace_var_one_rec
  (X : String)
  (F : Formula_)
  (ES : List Equation)
  (h1 : var_occurs_in_equation_list X (equation_list_replace_var_one_rec X F ES)) :
  var_occurs_in_formula X F :=
  by
  unfold var_occurs_in_equation_list at h1
  obtain ⟨E, h1_left, h1_right⟩ := h1
  unfold equation_list_replace_var_one_rec at h1_left
  simp only [List.mem_map] at h1_left
  obtain ⟨E', h1_left_left, h1_left_right⟩ := h1_left
  rewrite [← h1_left_right] at h1_right
  apply var_occurs_in_equation_equation_replace_var_one_rec X F E'
  exact h1_right


lemma equation_replace_var_one_rec_var_set_subset
  (X : String)
  (F : Formula_)
  (E : Equation) :
  (equation_replace_var_one_rec X F E).var_set ⊆
    F.var_set ∪ E.var_set :=
  by
  unfold equation_replace_var_one_rec
  unfold Equation.var_set
  simp only
  rewrite [Finset.union_union_distrib_left]
  apply Finset.union_subset_union
  · apply replace_var_one_rec_var_set_subset
  · apply replace_var_one_rec_var_set_subset


lemma equation_list_replace_var_one_rec_equation_list_var_set_subset
  (X : String)
  (F : Formula_)
  (ES : List Equation) :
  equation_list_var_set (equation_list_replace_var_one_rec X F ES) ⊆
    F.var_set ∪ equation_list_var_set ES :=
  by
  unfold equation_list_replace_var_one_rec
  unfold equation_list_var_set

  induction ES
  case nil =>
    simp only [List.map_nil, List.foldr_nil, Finset.union_empty, Finset.empty_subset]
  case cons hd tl ih =>
    simp only [List.map_cons, List.foldr_cons]
    rewrite [Finset.union_union_distrib_left]
    apply Finset.union_subset_union
    · apply equation_replace_var_one_rec_var_set_subset
    · exact ih


theorem extracted_1
  (X : String)
  (F : Formula_)
  (ES : List Equation)
  (h1 : ¬ var_occurs_in_formula X F) :
  equation_list_var_set (equation_list_replace_var_one_rec X F ES) ⊂ {X} ∪ F.var_set ∪ equation_list_var_set ES :=
  by
  simp only [Finset.ssubset_iff]
  apply Exists.intro X
  constructor
  · intro contra
    apply h1
    simp only [← var_occurs_in_equation_list_iff_mem_equation_list_var_set] at contra
    apply var_occurs_in_equation_list_equation_list_replace_var_one_rec X F ES
    exact contra
  · simp only [Finset.insert_eq]
    simp only [Finset.union_assoc]
    apply Finset.union_subset_union
    · rfl
    · apply equation_list_replace_var_one_rec_equation_list_var_set_subset


#lint
