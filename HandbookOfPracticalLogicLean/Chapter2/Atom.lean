import HandbookOfPracticalLogicLean.Chapter2.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `Formula_.is_atom F` := True if and only if the formula `F` is an `atom_`.
-/
def Formula_.is_atom :
  Formula_ → Prop
| atom_ _ => True
| _ => False

instance
  (F : Formula_) :
  Decidable (is_atom F) :=
  by
  cases F
  all_goals
    unfold is_atom
    infer_instance


/--
  `Formula_.atom_set F` := The set of all of the atoms that have an occurrence in the formula `F`.
-/
def Formula_.atom_set :
  Formula_ → Finset String
  | false_ => ∅
  | true_ => ∅
  | atom_ X => {X}
  | not_ phi => phi.atom_set
  | and_ phi psi => phi.atom_set ∪ psi.atom_set
  | or_ phi psi => phi.atom_set ∪ psi.atom_set
  | imp_ phi psi => phi.atom_set ∪ psi.atom_set
  | iff_ phi psi => phi.atom_set ∪ psi.atom_set


/--
  `Formula_.atom_list F` := The list of all of the atoms that have an occurrence in the formula `F`.
-/
def Formula_.atom_list :
  Formula_ → List String
  | false_ => []
  | true_ => []
  | atom_ X => [X]
  | not_ phi => phi.atom_list
  | and_ phi psi => phi.atom_list ++ psi.atom_list
  | or_ phi psi => phi.atom_list ++ psi.atom_list
  | imp_ phi psi => phi.atom_list ++ psi.atom_list
  | iff_ phi psi => phi.atom_list ++ psi.atom_list


/--
  `atom_occurs_in A F` := True if and only if there is an occurrence of the atom `A` in the formula `F`.
-/
def atom_occurs_in
  (A : String) :
  Formula_ → Prop
  | false_ => False
  | true_ => False
  | atom_ X => A = X
  | not_ phi => atom_occurs_in A phi
  | and_ phi psi => atom_occurs_in A phi ∨ atom_occurs_in A psi
  | or_ phi psi => atom_occurs_in A phi ∨ atom_occurs_in A psi
  | imp_ phi psi => atom_occurs_in A phi ∨ atom_occurs_in A psi
  | iff_ phi psi => atom_occurs_in A phi ∨ atom_occurs_in A psi

instance
  (A : String)
  (F : Formula_) :
  Decidable (atom_occurs_in A F) :=
  by
  induction F
  all_goals
    unfold atom_occurs_in
    infer_instance


-------------------------------------------------------------------------------


lemma atom_occurs_in_iff_mem_atom_set
  (A : String)
  (F : Formula_) :
  atom_occurs_in A F ↔ A ∈ F.atom_set :=
  by
  induction F
  all_goals
    unfold atom_occurs_in
    unfold atom_set
  case true_ | false_ =>
    simp only [Finset.not_mem_empty]
  case atom_ X =>
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


lemma atom_occurs_in_iff_mem_atom_list
  (A : String)
  (F : Formula_) :
  atom_occurs_in A F ↔ A ∈ F.atom_list :=
  by
  induction F
  all_goals
    unfold atom_occurs_in
    unfold atom_list
  case true_ | false_ =>
    simp only [List.not_mem_nil]
  case atom_ X =>
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
  `formula_list_atom_set FS` := The set of all of the atoms that have an occurrence in the list of formulas `FS`.
-/
def formula_list_atom_set
  (FS : List Formula_) :
  Finset String :=
  List.foldr (fun (next : Formula_) (prev : Finset String) => next.atom_set ∪ prev) {} FS


/--
  `formula_list_atom_list FS` := The list of all of the atoms that have an occurrence in the list of formulas `FS`.
-/
def formula_list_atom_list
  (FS : List Formula_) :
  List String :=
  List.foldr (fun (next : Formula_) (prev : List String) => next.atom_list ++ prev) [] FS


/--
  `atom_occurs_in_formula_list A FS` := True if and only if there is an occurrence of the atom `A` in the list of formulas `FS`.
-/
def atom_occurs_in_formula_list
  (A : String)
  (FS : List Formula_) :
  Prop :=
  ∃ (F : Formula_), F ∈ FS ∧ atom_occurs_in A F

instance
  (A : String)
  (FS : List Formula_) :
  Decidable (atom_occurs_in_formula_list A FS) :=
  by
  unfold atom_occurs_in_formula_list
  infer_instance


-------------------------------------------------------------------------------


lemma atom_occurs_in_formula_list_imp_mem_formula_list_atom_set
  (A : String)
  (FS : List Formula_)
  (F : Formula_)
  (h1 : F ∈ FS)
  (h2 : atom_occurs_in A F) :
  A ∈ formula_list_atom_set FS :=
  by
  unfold formula_list_atom_set

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
      simp only [← atom_occurs_in_iff_mem_atom_set]
      exact h2
    case inr h1 =>
      right
      apply ih
      exact h1


lemma mem_formula_list_atom_set_imp_atom_occurs_in_formula_list
  (A : String)
  (FS : List Formula_)
  (h1 : A ∈ formula_list_atom_set FS) :
  atom_occurs_in_formula_list A FS :=
  by
  unfold formula_list_atom_set at h1

  unfold atom_occurs_in_formula_list
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
      · simp only [atom_occurs_in_iff_mem_atom_set]
        exact h1
    case inr h1 =>
      specialize ih h1
      obtain ⟨F, ih_left, ih_right⟩ := ih

      apply Exists.intro F
      constructor
      · right
        exact ih_left
      · exact ih_right


lemma atom_occurs_in_formula_list_iff_mem_formula_list_atom_set
  (A : String)
  (FS : List Formula_) :
  atom_occurs_in_formula_list A FS ↔ A ∈ formula_list_atom_set FS :=
  by
    unfold atom_occurs_in_formula_list
    constructor
    · intro a1
      obtain ⟨F, a1_left, a1_right⟩ := a1
      apply atom_occurs_in_formula_list_imp_mem_formula_list_atom_set A FS F
      · exact a1_left
      · exact a1_right
    · apply mem_formula_list_atom_set_imp_atom_occurs_in_formula_list


-------------------------------------------------------------------------------


lemma atom_occurs_in_formula_list_imp_mem_formula_list_atom_list
  (A : String)
  (FS : List Formula_)
  (F : Formula_)
  (h1 : F ∈ FS)
  (h2 : atom_occurs_in A F) :
  A ∈ formula_list_atom_list FS :=
  by
  unfold formula_list_atom_list

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
      simp only [← atom_occurs_in_iff_mem_atom_list]
      exact h2
    case inr h1 =>
      right
      apply ih
      exact h1


lemma mem_formula_list_atom_list_imp_atom_occurs_in_formula_list
  (A : String)
  (FS : List Formula_)
  (h1 : A ∈ formula_list_atom_list FS) :
  atom_occurs_in_formula_list A FS :=
  by
  unfold formula_list_atom_list at h1

  unfold atom_occurs_in_formula_list
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
      · simp only [atom_occurs_in_iff_mem_atom_list]
        exact h1
    case inr h1 =>
      specialize ih h1
      obtain ⟨F, ih_left, ih_right⟩ := ih

      apply Exists.intro F
      constructor
      · right
        exact ih_left
      · exact ih_right


lemma atom_occurs_in_formula_list_iff_mem_formula_list_atom_list
  (A : String)
  (FS : List Formula_) :
  atom_occurs_in_formula_list A FS ↔ A ∈ formula_list_atom_list FS :=
  by
    unfold atom_occurs_in_formula_list
    constructor
    · intro a1
      obtain ⟨F, a1_left, a1_right⟩ := a1
      apply atom_occurs_in_formula_list_imp_mem_formula_list_atom_list A FS F
      · exact a1_left
      · exact a1_right
    · apply mem_formula_list_atom_list_imp_atom_occurs_in_formula_list


#lint
