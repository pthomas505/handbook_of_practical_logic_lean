import HandbookOfPracticalLogicLean.Prop.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `Formula_.is_var F` := True if and only if the formula `F` is an `var_`.
-/
def Formula_.is_var :
  Formula_ → Prop
| var_ _ => True
| _ => False

instance
  (F : Formula_) :
  Decidable (is_var F) :=
  by
  cases F
  all_goals
    unfold is_var
    infer_instance


/--
  `Formula_.var_set F` := The set of all of the vars that have an occurrence in the formula `F`.
-/
def Formula_.var_set :
  Formula_ → Finset String
  | false_ => ∅
  | true_ => ∅
  | var_ X => {X}
  | not_ phi => phi.var_set
  | and_ phi psi => phi.var_set ∪ psi.var_set
  | or_ phi psi => phi.var_set ∪ psi.var_set
  | imp_ phi psi => phi.var_set ∪ psi.var_set
  | iff_ phi psi => phi.var_set ∪ psi.var_set


/--
  `Formula_.var_list F` := The list of all of the vars that have an occurrence in the formula `F`.
-/
def Formula_.var_list :
  Formula_ → List String
  | false_ => []
  | true_ => []
  | var_ X => [X]
  | not_ phi => phi.var_list
  | and_ phi psi => phi.var_list ++ psi.var_list
  | or_ phi psi => phi.var_list ++ psi.var_list
  | imp_ phi psi => phi.var_list ++ psi.var_list
  | iff_ phi psi => phi.var_list ++ psi.var_list


/--
  `var_occurs_in_formula A F` := True if and only if there is an occurrence of the var `A` in the formula `F`.
-/
def var_occurs_in_formula
  (A : String) :
  Formula_ → Prop
  | false_ => False
  | true_ => False
  | var_ X => A = X
  | not_ phi => var_occurs_in_formula A phi
  | and_ phi psi => var_occurs_in_formula A phi ∨ var_occurs_in_formula A psi
  | or_ phi psi => var_occurs_in_formula A phi ∨ var_occurs_in_formula A psi
  | imp_ phi psi => var_occurs_in_formula A phi ∨ var_occurs_in_formula A psi
  | iff_ phi psi => var_occurs_in_formula A phi ∨ var_occurs_in_formula A psi

instance
  (A : String)
  (F : Formula_) :
  Decidable (var_occurs_in_formula A F) :=
  by
  induction F
  all_goals
    unfold var_occurs_in_formula
    infer_instance


-------------------------------------------------------------------------------


lemma var_occurs_in_formula_iff_mem_var_set
  (A : String)
  (F : Formula_) :
  var_occurs_in_formula A F ↔ A ∈ F.var_set :=
  by
  induction F
  all_goals
    unfold var_occurs_in_formula
    unfold var_set
  case true_ | false_ =>
    simp only [Finset.not_mem_empty]
  case var_ X =>
    simp only [Finset.mem_singleton]
  case not_ phi ih =>
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [Finset.mem_union]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


lemma var_occurs_in_formula_iff_mem_var_list
  (A : String)
  (F : Formula_) :
  var_occurs_in_formula A F ↔ A ∈ F.var_list :=
  by
  induction F
  all_goals
    unfold var_occurs_in_formula
    unfold var_list
  case true_ | false_ =>
    simp only [List.not_mem_nil]
  case var_ X =>
    simp only [List.mem_singleton]
  case not_ phi ih =>
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [List.mem_append]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


-------------------------------------------------------------------------------


/--
  `formula_list_var_set FS` := The set of all of the vars that have an occurrence in the list of formulas `FS`.
-/
def formula_list_var_set
  (FS : List Formula_) :
  Finset String :=
  List.foldr (fun (next : Formula_) (prev : Finset String) => next.var_set ∪ prev) {} FS


/--
  `formula_list_var_list FS` := The list of all of the vars that have an occurrence in the list of formulas `FS`.
-/
def formula_list_var_list
  (FS : List Formula_) :
  List String :=
  List.foldr (fun (next : Formula_) (prev : List String) => next.var_list ++ prev) [] FS


/--
  `var_occurs_in_formula_formula_list A FS` := True if and only if there is an occurrence of the var `A` in the list of formulas `FS`.
-/
def var_occurs_in_formula_formula_list
  (A : String)
  (FS : List Formula_) :
  Prop :=
  ∃ (F : Formula_), F ∈ FS ∧ var_occurs_in_formula A F

instance
  (A : String)
  (FS : List Formula_) :
  Decidable (var_occurs_in_formula_formula_list A FS) :=
  by
  unfold var_occurs_in_formula_formula_list
  infer_instance


-------------------------------------------------------------------------------


lemma var_occurs_in_formula_formula_list_imp_mem_formula_list_var_set
  (A : String)
  (FS : List Formula_)
  (F : Formula_)
  (h1 : F ∈ FS)
  (h2 : var_occurs_in_formula A F) :
  A ∈ formula_list_var_set FS :=
  by
  unfold formula_list_var_set

  induction FS
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1

    simp only [List.foldr_cons, Finset.mem_union]

    cases h1
    case inl h1 =>
      rewrite [← h1]
      left
      simp only [← var_occurs_in_formula_iff_mem_var_set]
      exact h2
    case inr h1 =>
      right
      apply ih
      exact h1


lemma mem_formula_list_var_set_imp_var_occurs_in_formula_formula_list
  (A : String)
  (FS : List Formula_)
  (h1 : A ∈ formula_list_var_set FS) :
  var_occurs_in_formula_formula_list A FS :=
  by
  unfold formula_list_var_set at h1

  unfold var_occurs_in_formula_formula_list
  induction FS
  case nil =>
    simp only [List.foldr_nil, Finset.not_mem_empty] at h1
  case cons hd tl ih =>
    simp only [List.foldr_cons, Finset.mem_union] at h1

    simp only [List.mem_cons]
    cases h1
    case inl h1 =>
      apply Exists.intro hd
      constructor
      · left
        rfl
      · simp only [var_occurs_in_formula_iff_mem_var_set]
        exact h1
    case inr h1 =>
      specialize ih h1
      obtain ⟨F, ih_left, ih_right⟩ := ih

      apply Exists.intro F
      constructor
      · right
        exact ih_left
      · exact ih_right


lemma var_occurs_in_formula_formula_list_iff_mem_formula_list_var_set
  (A : String)
  (FS : List Formula_) :
  var_occurs_in_formula_formula_list A FS ↔ A ∈ formula_list_var_set FS :=
  by
    unfold var_occurs_in_formula_formula_list
    constructor
    · intro a1
      obtain ⟨F, a1_left, a1_right⟩ := a1
      apply var_occurs_in_formula_formula_list_imp_mem_formula_list_var_set A FS F
      · exact a1_left
      · exact a1_right
    · apply mem_formula_list_var_set_imp_var_occurs_in_formula_formula_list


-------------------------------------------------------------------------------


lemma var_occurs_in_formula_formula_list_imp_mem_formula_list_var_list
  (A : String)
  (FS : List Formula_)
  (F : Formula_)
  (h1 : F ∈ FS)
  (h2 : var_occurs_in_formula A F) :
  A ∈ formula_list_var_list FS :=
  by
  unfold formula_list_var_list

  induction FS
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1

    simp only [List.foldr_cons, List.mem_append]

    cases h1
    case inl h1 =>
      rewrite [← h1]
      left
      simp only [← var_occurs_in_formula_iff_mem_var_list]
      exact h2
    case inr h1 =>
      right
      apply ih
      exact h1


lemma mem_formula_list_var_list_imp_var_occurs_in_formula_formula_list
  (A : String)
  (FS : List Formula_)
  (h1 : A ∈ formula_list_var_list FS) :
  var_occurs_in_formula_formula_list A FS :=
  by
  unfold formula_list_var_list at h1

  unfold var_occurs_in_formula_formula_list
  induction FS
  case nil =>
    simp only [List.foldr_nil, List.not_mem_nil] at h1
  case cons hd tl ih =>
    simp only [List.foldr_cons, List.mem_append] at h1

    simp only [List.mem_cons]
    cases h1
    case inl h1 =>
      apply Exists.intro hd
      constructor
      · left
        rfl
      · simp only [var_occurs_in_formula_iff_mem_var_list]
        exact h1
    case inr h1 =>
      specialize ih h1
      obtain ⟨F, ih_left, ih_right⟩ := ih

      apply Exists.intro F
      constructor
      · right
        exact ih_left
      · exact ih_right


lemma var_occurs_in_formula_formula_list_iff_mem_formula_list_var_list
  (A : String)
  (FS : List Formula_) :
  var_occurs_in_formula_formula_list A FS ↔ A ∈ formula_list_var_list FS :=
  by
    unfold var_occurs_in_formula_formula_list
    constructor
    · intro a1
      obtain ⟨F, a1_left, a1_right⟩ := a1
      apply var_occurs_in_formula_formula_list_imp_mem_formula_list_var_list A FS F
      · exact a1_left
      · exact a1_right
    · apply mem_formula_list_var_list_imp_var_occurs_in_formula_formula_list


#lint
