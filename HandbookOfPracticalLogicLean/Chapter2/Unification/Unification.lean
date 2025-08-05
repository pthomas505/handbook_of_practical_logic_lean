-- https://dl.acm.org/doi/10.1145/357162.357169

import HandbookOfPracticalLogicLean.Chapter2.Replace
import HandbookOfPracticalLogicLean.Chapter2.SubFormula


set_option autoImplicit false


open Formula_


def Substitution : Type := String → Formula_


structure Equation : Type where
  (lhs : Formula_)
  (rhs : Formula_)
  deriving Inhabited, DecidableEq, Repr


def equation_list_formula_list
  (L : List Equation) :
  List Formula_ :=
  List.foldr (fun (next : Equation) (prev : List Formula_) => next.lhs :: next.rhs :: prev) [] L

#eval equation_list_formula_list []
#eval equation_list_formula_list [⟨atom_ "P", atom_ "Q"⟩]
#eval equation_list_formula_list [⟨atom_ "P", atom_ "Q"⟩, ⟨atom_ "Q", atom_ "R"⟩]
#eval equation_list_formula_list [⟨atom_ "P", atom_ "Q"⟩, ⟨atom_ "R", atom_ "S"⟩]


/--
  `is_equation_unifier σ E` := True if and only if the substitution `σ` is a unifier of the equation `E`.
-/
def is_equation_unifier
  (σ : Substitution)
  (E : Equation) :
  Prop :=
  replace_atom_all_rec σ E.lhs = replace_atom_all_rec σ E.rhs


/--
  `is_equation_list_unifier σ L` := True if and only if the substitution `σ` is a unifier of the list of equations `L`.
-/
def is_equation_list_unifier
  (σ : Substitution)
  (L : List Equation) :
  Prop :=
  ∀ (E : Equation), E ∈ L → is_equation_unifier σ E


lemma is_equation_unifier_replace_atom_all_rec_compose
  (σ τ : Substitution)
  (E : Equation)
  (h1 : is_equation_unifier σ E) :
  is_equation_unifier ((replace_atom_all_rec τ) ∘ σ) E :=
  by
  unfold is_equation_unifier at h1

  unfold is_equation_unifier
  simp only [replace_atom_all_rec_compose]
  congr


example
  (σ τ : Substitution)
  (L : List Equation)
  (h1 : is_equation_list_unifier σ L) :
  is_equation_list_unifier ((replace_atom_all_rec τ) ∘ σ) L :=
  by
  unfold is_equation_list_unifier at h1

  unfold is_equation_list_unifier
  intro E a1
  apply is_equation_unifier_replace_atom_all_rec_compose
  apply h1
  exact a1


/--
  `is_more_general_substitution σ τ` := True if and only if the substitution `σ` is more general than the substitution `τ`.
  `σ ≤ τ`
-/
def is_more_general_substitution
  (σ τ : Substitution) :
  Prop :=
  ∃ (δ : Substitution), replace_atom_all_rec τ = (replace_atom_all_rec δ) ∘ (replace_atom_all_rec σ)


example
  (σ : Substitution) :
  is_more_general_substitution σ σ :=
  by
  unfold is_more_general_substitution
  apply Exists.intro atom_
  funext F
  simp only [Function.comp_apply]
  simp only [replace_atom_all_rec_id]


/--
  `is_most_general_equation_list_unifier σ L` := True if and only if the substitution `σ` is a most general unifier (MGU) of the list of equations `L`.
-/
def is_most_general_equation_list_unifier
  (σ : Substitution)
  (L : List Equation) :
  Prop :=
  is_equation_list_unifier σ L ∧ ∀ (τ : Substitution), is_equation_list_unifier τ L → is_more_general_substitution σ τ


def are_equivalent_equation_lists
  (L L' : List Equation) :
  Prop :=
  ∀ (σ : Substitution), (is_equation_list_unifier σ L ↔ is_equation_list_unifier σ L')


def reduce :
  Equation → Option (List (Equation))
  | ⟨not_ phi, not_ phi'⟩ => Option.some [⟨phi, phi'⟩]
  | ⟨and_ phi psi, and_ phi' psi'⟩
  | ⟨or_ phi psi, or_ phi' psi'⟩
  | ⟨imp_ phi psi, imp_ phi' psi'⟩
  | ⟨iff_ phi psi, iff_ phi' psi'⟩ => Option.some ([⟨phi, phi'⟩] ∪ [⟨psi, psi'⟩])
  | _ => Option.none


def is_reducible :
  Equation → Prop
  | ⟨not_ _, not_ _⟩
  | ⟨and_ _ _, and_ _ _⟩
  | ⟨or_ _ _, or_ _ _⟩
  | ⟨imp_ _ _, imp_ _ _⟩
  | ⟨iff_ _ _, iff_ _ _⟩ => True
  | _ => False


example
  (lhs rhs : Formula_)
  (h1 : (reduce ⟨lhs, rhs⟩).isSome) :
  are_equivalent_equation_lists [⟨lhs, rhs⟩] ((reduce ⟨lhs, rhs⟩).get h1) :=
  by
  unfold are_equivalent_equation_lists
  intro σ
  unfold is_equation_list_unifier
  simp only [List.mem_singleton]
  unfold is_equation_unifier

  cases lhs
  all_goals
    cases rhs
    any_goals
      simp only [reduce] at h1
      simp only [Option.isSome_none] at h1
      contradiction
  case not_ phi psi =>
    simp only [reduce]
    simp only [Option.get_some]
    simp only [List.mem_singleton]
    simp only [forall_eq]
    simp only [replace_atom_all_rec]
    constructor
    · intro a1
      injection a1
    · intro a1
      congr
  case
      and_ phi psi phi' psi'
    | or_ phi psi phi' psi'
    | imp_ phi psi phi' psi'
    | iff_ phi psi phi' psi' =>
    simp only [reduce]
    simp only [Option.get_some]
    simp only [List.cons_union]
    simp only [List.nil_union]
    simp only [List.mem_insert_iff]
    simp only [List.mem_singleton]
    simp only [forall_eq_or_imp]
    simp only [forall_eq]
    simp only [replace_atom_all_rec]
    constructor
    · intro a1
      injection a1 with a1_left a1_right
      exact ⟨a1_left, a1_right⟩
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1
      congr


-------------------------------------------------------------------------------


lemma is_equation_list_unifier_singleton
  (σ : Substitution)
  (E : Equation) :
  is_equation_list_unifier σ [E] ↔ is_equation_unifier σ E :=
  by
  unfold is_equation_list_unifier
  simp only [List.mem_singleton]
  constructor
  · intro a1
    apply a1
    rfl
  · intro a1 E' a2
    rewrite [a2]
    exact a1


lemma is_equation_list_unifier_append
  (σ : Substitution)
  (L L' : List Equation) :
  is_equation_list_unifier σ (L ++ L') ↔ (is_equation_list_unifier σ L ∧ is_equation_list_unifier σ L') :=
  by
  unfold is_equation_list_unifier
  unfold is_equation_unifier
  simp only [List.mem_append]
  constructor
  · intro a1
    constructor
    · intro E a2
      apply a1
      left
      exact a2
    · intro E a2
      apply a1
      right
      exact a2
  · intro a1 E a2
    obtain ⟨a1_left, a1_right⟩ := a1

    cases a2
    case inl a2 =>
      apply a1_left
      exact a2
    case inr a2 =>
      apply a1_right
      exact a2


-------------------------------------------------------------------------------


example
  (σ : Substitution)
  (E : Equation)
  (h1 : is_proper_subformula_v2 E.lhs E.rhs) :
  ¬ is_equation_unifier σ E :=
  by
  intro contra
  apply is_proper_subformula_v2_imp_replace_atom_all_rec_not_eq σ E.lhs E.rhs
  · exact h1
  · unfold is_equation_unifier at contra
    exact contra


-------------------------------------------------------------------------------


/-
  Let `X` be a variable, `F` be a formula, and `L : List (Formula_ × Formula_)` be a list of equations. If `(X, F) ∈ L` then every substitution that is a unifier of `L` is also a unifier of `(X, F)`. Hence every substitution that is a unifier of `L` maps `X` and `F` to the same formula. Let `L'` be the replacement of every occurrence of `X` in `L` by `F`. Then every substitution that is a unifier of `L` maps `X` and `F` in `L` to the same formula that it maps `F` in `L'` to. Therefore `L` and `L'` are equivalent equation lists.
-/


def var_elim
  (X : String)
  (F : Formula_)
  (L : List Equation) :
  List Equation :=
  L.map (fun (E : Equation) => ⟨replace_atom_one_rec X F E.lhs, replace_atom_one_rec X F E.rhs⟩)


example
  (σ : Substitution)
  (X : String)
  (F : Formula_)
  (L : List Equation)
  (h1 : is_equation_list_unifier σ (⟨atom_ X, F⟩ :: L)) :
  σ X = replace_atom_all_rec σ F :=
  by
  unfold is_equation_list_unifier at h1
  unfold is_equation_unifier at h1
  simp only [List.mem_cons] at h1
  specialize h1 ⟨atom_ X, F⟩
  simp only at h1
  simp only [replace_atom_all_rec] at h1
  apply h1
  left
  exact trivial


lemma replace_atom_all_rec_eq_replace_atom_all_rec_of_replace_atom_one_rec
  (σ : Substitution)
  (X' : String)
  (F' : Formula_)
  (F : Formula_)
  (h1 : σ X' = replace_atom_all_rec σ F') :
  replace_atom_all_rec σ F =
    replace_atom_all_rec σ (replace_atom_one_rec X' F' F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [replace_atom_all_rec]
  case atom_ X =>
    simp only [replace_atom_all_rec]
    unfold replace_atom_one_rec
    split_ifs
    case pos c1 =>
      rewrite [← c1]
      exact h1
    case neg c1 =>
      unfold replace_atom_all_rec
      rfl
  case not_ phi ih =>
    simp only [replace_atom_all_rec]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [replace_atom_all_rec]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


lemma is_equation_unifier_iff_is_equation_unifier_replace_atom_one_rec_singleton
  (σ : Substitution)
  (X : String)
  (F : Formula_)
  (lhs rhs : Formula_)
  (h1 : is_equation_unifier σ ⟨atom_ X, F⟩) :
  is_equation_unifier σ ⟨lhs, rhs⟩ ↔ is_equation_unifier σ ⟨replace_atom_one_rec X F lhs, replace_atom_one_rec X F rhs⟩ :=
  by
  unfold is_equation_unifier at h1
  simp only [replace_atom_all_rec] at h1

  unfold is_equation_unifier

  obtain s1 := replace_atom_all_rec_eq_replace_atom_all_rec_of_replace_atom_one_rec σ X F lhs h1
  rewrite [← s1]

  obtain s2 := replace_atom_all_rec_eq_replace_atom_all_rec_of_replace_atom_one_rec σ X F rhs h1
  rewrite [← s2]

  rfl


lemma is_equation_list_unifier_iff_is_equation_list_unifier_var_elim
  (σ : Substitution)
  (X : String)
  (F : Formula_)
  (L : List Equation)
  (h1 : is_equation_unifier σ ⟨atom_ X, F⟩) :
  is_equation_list_unifier σ L ↔ is_equation_list_unifier σ (var_elim X F L) :=
  by
  induction L
  case nil =>
    unfold var_elim
    simp only [List.map_nil]
  case cons hd tl ih =>
    unfold var_elim
    simp only [List.map_cons]
    rewrite [← List.singleton_append]
    rewrite [is_equation_list_unifier_append]
    conv => right; rewrite [← List.singleton_append]; rewrite [is_equation_list_unifier_append]

    obtain s1 := is_equation_unifier_iff_is_equation_unifier_replace_atom_one_rec_singleton σ X F hd.lhs hd.rhs h1
    simp only [is_equation_list_unifier_singleton]
    rewrite [← s1]

    rewrite [ih]
    unfold var_elim
    rfl


example
  (X : String)
  (F : Formula_)
  (L : List Equation) :
  are_equivalent_equation_lists (⟨atom_ X, F⟩ :: L) (⟨atom_ X, F⟩ :: var_elim X F L) :=
  by
  unfold are_equivalent_equation_lists
  intro σ
  rewrite [← List.singleton_append]
  rewrite [is_equation_list_unifier_append]
  conv => right; rewrite [← List.singleton_append]; rewrite [is_equation_list_unifier_append]
  simp only [is_equation_list_unifier_singleton]
  constructor
  · intro a1
    obtain ⟨a1_left, a1_right⟩ := a1
    constructor
    · exact a1_left
    · simp only [← is_equation_list_unifier_iff_is_equation_list_unifier_var_elim σ X F L a1_left]
      exact a1_right
  · intro a1
    obtain ⟨a1_left, a1_right⟩ := a1
    constructor
    · exact a1_left
    · simp only [is_equation_list_unifier_iff_is_equation_list_unifier_var_elim σ X F L a1_left]
      exact a1_right


-------------------------------------------------------------------------------


structure Multiequation : Type where
  (lhs : List Formula_)
  (rhs : List Formula_)
  (lhs_not_empty : ¬ lhs = [])
  (lhs_atom : ∀ (F : Formula_), F ∈ lhs → F.is_atom)
  (rhs_not_atom : ∀ (F : Formula_), F ∈ rhs → (¬ F = false_ ∧ ¬ F = true_ ∧ ¬ F.is_atom))


def multiequation_formula_list
  (M : Multiequation) :
  List Formula_ :=
  M.lhs ++ M.rhs


def is_multiequation_unifier
  (σ : Substitution)
  (M : Multiequation) :
  Prop :=
  ∀ (F_1 F_2 : Formula_),
    (F_1 ∈ multiequation_formula_list M ∧ F_2 ∈ multiequation_formula_list M) →
      is_equation_unifier σ ⟨F_1, F_2⟩


def multiequation_relation
  (L : List Equation) :
  Formula_ → Formula_ → Prop :=
  Relation.EqvGen (fun (lhs rhs : Formula_) => ⟨lhs, rhs⟩ ∈ L)


def corresponds
  (L : List Equation)
  (M : Multiequation) :
  Prop :=
  (∀ (F : Formula_), F ∈ (equation_list_formula_list L) → F ∈ multiequation_formula_list M) ∧
  (∀ (F_1 F_2 : Formula_), (F_1 ∈ multiequation_formula_list M ∧ F_2 ∈ multiequation_formula_list M) → multiequation_relation L F_1 F_2)


lemma multiequation_relation_is_unifier
  (σ : Substitution)
  (L : List Equation)
  (F_1 F_2 : Formula_)
  (h1 : is_equation_list_unifier σ L)
  (h2 : multiequation_relation L F_1 F_2) :
  is_equation_list_unifier σ [⟨F_1, F_2⟩] :=
  by
  unfold is_equation_list_unifier at h1

  unfold multiequation_relation at h2

  unfold is_equation_list_unifier
  intro E a1
  simp only [List.mem_singleton] at a1
  rewrite [a1]

  induction h2 generalizing E
  case rel P Q ih_1 =>
    apply h1
    exact ih_1
  case refl F =>
    unfold is_equation_unifier
    simp only
  case symm P Q ih_1 ih_2 =>
    unfold is_equation_unifier
    symm
    apply ih_2 ⟨P, Q⟩
    rfl
  case trans P Q R ih_1 ih_2 ih_3 ih_4 =>
    unfold is_equation_unifier
    simp only
    trans (replace_atom_all_rec σ Q)
    · apply ih_3 ⟨P, Q⟩
      rfl
    · apply ih_4 ⟨Q, R⟩
      rfl


example
  (σ : Substitution)
  (L : List Equation)
  (M : Multiequation)
  (h1 : corresponds L M)
  (h2 : is_equation_list_unifier σ L) :
  is_multiequation_unifier σ M :=
  by
  unfold corresponds at h1
  obtain ⟨h1_left, h1_right⟩ := h1

  unfold is_multiequation_unifier
  intro F_1 F_2 a1
  apply multiequation_relation_is_unifier σ L F_1 F_2
  · exact h2
  · apply h1_right
    exact a1
  · simp only [List.mem_singleton]


lemma mem_equation_list_imp_mem_equation_list_formula_list_left
  (E : Equation)
  (L : List Equation)
  (h1 : E ∈ L) :
  E.lhs ∈ equation_list_formula_list L :=
  by
  induction L
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
  (L : List Equation)
  (h1 : E ∈ L) :
  E.rhs ∈ equation_list_formula_list L :=
  by
  induction L
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


example
  (σ : Substitution)
  (L : List Equation)
  (M : Multiequation)
  (h1 : corresponds L M)
  (h2 : is_multiequation_unifier σ M) :
  is_equation_list_unifier σ L :=
  by
  unfold corresponds at h1
  obtain ⟨h1_left, h1_right⟩ := h1

  unfold is_multiequation_unifier at h2

  unfold is_equation_list_unifier
  intro E a1
  unfold is_equation_unifier at h2
  apply h2 E.lhs E.rhs
  · specialize h1_right E.lhs E.rhs
    constructor
    · apply h1_left
      apply mem_equation_list_imp_mem_equation_list_formula_list_left
      exact a1
    · apply h1_left
      apply mem_equation_list_imp_mem_equation_list_formula_list_right
      exact a1
