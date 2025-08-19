-- https://dl.acm.org/doi/10.1145/357162.357169

import HandbookOfPracticalLogicLean.Prop.Unification.Equation
import HandbookOfPracticalLogicLean.Prop.Replace.Var.All.Rec.Replace


set_option autoImplicit false


open Formula_


def Substitution : Type := String → Formula_


/--
  `is_equation_unifier σ E` := True if and only if the substitution `σ` is a unifier of the equation `E`.
-/
def is_equation_unifier
  (σ : Substitution)
  (E : Equation) :
  Prop :=
  replace_var_all_rec σ E.lhs = replace_var_all_rec σ E.rhs


/--
  `is_equation_list_unifier σ ES` := True if and only if the substitution `σ` is a unifier of the list of equations `ES`.
-/
def is_equation_list_unifier
  (σ : Substitution)
  (ES : List Equation) :
  Prop :=
  ∀ (E : Equation), E ∈ ES → is_equation_unifier σ E


lemma is_equation_unifier_replace_var_all_rec_compose
  (σ τ : Substitution)
  (E : Equation)
  (h1 : is_equation_unifier σ E) :
  is_equation_unifier ((replace_var_all_rec τ) ∘ σ) E :=
  by
  unfold is_equation_unifier at h1

  unfold is_equation_unifier
  simp only [replace_var_all_rec_compose]
  congr


example
  (σ τ : Substitution)
  (ES : List Equation)
  (h1 : is_equation_list_unifier σ ES) :
  is_equation_list_unifier ((replace_var_all_rec τ) ∘ σ) ES :=
  by
  unfold is_equation_list_unifier at h1

  unfold is_equation_list_unifier
  intro E a1
  apply is_equation_unifier_replace_var_all_rec_compose
  apply h1
  exact a1


/--
  `is_more_general_substitution σ τ` := True if and only if the substitution `σ` is more general than the substitution `τ`.
  `σ ≤ τ`
-/
def is_more_general_substitution
  (σ τ : Substitution) :
  Prop :=
  ∃ (μ : Substitution), replace_var_all_rec τ = (replace_var_all_rec μ) ∘ (replace_var_all_rec σ)


example
  (σ : Substitution) :
  is_more_general_substitution σ σ :=
  by
  unfold is_more_general_substitution
  apply Exists.intro var_
  funext F
  simp only [Function.comp_apply]
  simp only [replace_var_all_rec_id]


/--
  `is_most_general_equation_list_unifier σ ES` := True if and only if the substitution `σ` is a most general unifier (MGU) of the list of equations `ES`.
-/
def is_most_general_equation_list_unifier
  (σ : Substitution)
  (ES : List Equation) :
  Prop :=
  is_equation_list_unifier σ ES ∧
    ∀ (τ : Substitution), is_equation_list_unifier τ ES → is_more_general_substitution σ τ


def are_equivalent_equation_lists
  (ES ES' : List Equation) :
  Prop :=
  ∀ (σ : Substitution), is_equation_list_unifier σ ES ↔ is_equation_list_unifier σ ES'


def is_reducible :
  Equation → Prop
  | ⟨not_ _, not_ _⟩
  | ⟨and_ _ _, and_ _ _⟩
  | ⟨or_ _ _, or_ _ _⟩
  | ⟨imp_ _ _, imp_ _ _⟩
  | ⟨iff_ _ _, iff_ _ _⟩ => True
  | _ => False

instance :
  DecidablePred is_reducible :=
  by
  unfold DecidablePred
  intro E
  cases E
  case mk lhs rhs =>
    cases lhs
    all_goals
      cases rhs
      all_goals
        simp only [is_reducible]
        infer_instance


def reduce :
  Equation → Option (List Equation)
  | ⟨not_ phi, not_ phi'⟩ => Option.some [⟨phi, phi'⟩]
  | ⟨and_ phi psi, and_ phi' psi'⟩
  | ⟨or_ phi psi, or_ phi' psi'⟩
  | ⟨imp_ phi psi, imp_ phi' psi'⟩
  | ⟨iff_ phi psi, iff_ phi' psi'⟩ => Option.some ([⟨phi, phi'⟩] ∪ [⟨psi, psi'⟩])
  | _ => Option.none


def conflict :
  Equation → Prop
  | ⟨false_, false_⟩
  | ⟨true_, true_⟩
  | ⟨var_ _, _⟩
  | ⟨_, var_ _⟩
  | ⟨not_ _, not_ _⟩
  | ⟨and_ _ _, and_ _ _⟩
  | ⟨or_ _ _, or_ _ _⟩
  | ⟨imp_ _ _, imp_ _ _⟩
  | ⟨iff_ _ _, iff_ _ _⟩ => False
  | _ => True

instance :
  DecidablePred conflict :=
  by
  unfold DecidablePred
  intro E
  cases E
  case mk lhs rhs =>
    cases lhs
    all_goals
      cases rhs
      all_goals
        simp only [conflict]
        infer_instance


example
  (E : Equation)
  (h1 : (reduce E).isSome) :
  are_equivalent_equation_lists [E] ((reduce E).get h1) :=
  by
  unfold are_equivalent_equation_lists
  intro σ
  unfold is_equation_list_unifier
  simp only [List.mem_singleton]
  unfold is_equation_unifier

  cases E
  case mk lhs rhs =>
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
      simp only [replace_var_all_rec]
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
      simp only [replace_var_all_rec]
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
  (ES ES' : List Equation) :
  is_equation_list_unifier σ (ES ++ ES') ↔ (is_equation_list_unifier σ ES ∧ is_equation_list_unifier σ ES') :=
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
  apply is_proper_subformula_v2_imp_replace_var_all_rec_not_eq σ E.lhs E.rhs
  · exact h1
  · unfold is_equation_unifier at contra
    exact contra


-------------------------------------------------------------------------------


/-
  Let `X` be a string, let `F` be a formula, and let `ES` be a list of equations. If `⟨var_ X, F⟩ ∈ ES` then every substitution that is a unifier of `ES` is also a unifier of `⟨var_ X, F⟩`. Hence every substitution that is a unifier of `ES` maps `X` and `F` to the same formula. Let `ES'` be the replacement of every occurrence of `X` in `ES` by `F`. Then every substitution that is a unifier of `ES` maps `X` and `F` in `ES` to the same formula that it maps `F` in `ES'` to. Therefore `ES` and `ES'` are equivalent equation lists.
-/


example
  (σ : Substitution)
  (X : String)
  (F : Formula_)
  (ES : List Equation)
  (h1 : is_equation_list_unifier σ (⟨var_ X, F⟩ :: ES)) :
  is_equation_unifier σ ⟨var_ X, F⟩ :=
  by
  unfold is_equation_list_unifier at h1
  simp only [List.mem_cons] at h1

  apply h1
  left
  rfl


lemma is_equation_unifier_iff_is_equation_unifier_equation_replace_var_one_rec
  (σ : Substitution)
  (X : String)
  (F : Formula_)
  (E : Equation)
  (h1 : is_equation_unifier σ ⟨var_ X, F⟩) :
  is_equation_unifier σ E ↔
    is_equation_unifier σ (equation_replace_var_one_rec X F E) :=
  by
  unfold is_equation_unifier at h1
  simp only [replace_var_all_rec] at h1

  unfold equation_replace_var_one_rec
  unfold is_equation_unifier
  rewrite [← replace_var_all_rec_eq_replace_var_all_rec_of_replace_var_one_rec σ X F E.lhs h1]
  rewrite [← replace_var_all_rec_eq_replace_var_all_rec_of_replace_var_one_rec σ X F E.rhs h1]
  rfl


lemma is_equation_list_unifier_iff_is_equation_list_unifier_equation_list_replace_var_one_rec
  (σ : Substitution)
  (X : String)
  (F : Formula_)
  (ES : List Equation)
  (h1 : is_equation_unifier σ ⟨var_ X, F⟩) :
  is_equation_list_unifier σ ES ↔ is_equation_list_unifier σ (equation_list_replace_var_one_rec X F ES) :=
  by
  unfold equation_list_replace_var_one_rec
  induction ES
  case nil =>
    simp only [List.map_nil]
  case cons hd tl ih =>
    simp only [List.map_cons]
    rewrite [← List.singleton_append]
    rewrite [is_equation_list_unifier_append]
    conv => right; rewrite [← List.singleton_append]; rewrite [is_equation_list_unifier_append]
    simp only [is_equation_list_unifier_singleton]
    simp only [← is_equation_unifier_iff_is_equation_unifier_equation_replace_var_one_rec σ X F hd h1]
    rewrite [ih]
    rfl


example
  (X : String)
  (F : Formula_)
  (ES : List Equation) :
  are_equivalent_equation_lists (⟨var_ X, F⟩ :: ES) (⟨var_ X, F⟩ :: equation_list_replace_var_one_rec X F ES) :=
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
    · simp only [← is_equation_list_unifier_iff_is_equation_list_unifier_equation_list_replace_var_one_rec σ X F ES a1_left]
      exact a1_right
  · intro a1
    obtain ⟨a1_left, a1_right⟩ := a1
    constructor
    · exact a1_left
    · simp only [is_equation_list_unifier_iff_is_equation_list_unifier_equation_list_replace_var_one_rec σ X F ES a1_left]
      exact a1_right


-------------------------------------------------------------------------------


structure Multiequation : Type where
  (lhs : List Formula_)
  (rhs : List Formula_)
  (lhs_not_empty : ¬ lhs = [])
  (lhs_var : ∀ (F : Formula_), F ∈ lhs → F.is_var)
  (rhs_not_var : ∀ (F : Formula_), F ∈ rhs → (¬ F = false_ ∧ ¬ F = true_ ∧ ¬ F.is_var))


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


def mem_equation_list_eqv_relation
  (L : List Equation) :
  Formula_ → Formula_ → Prop :=
  Relation.EqvGen (fun (lhs rhs : Formula_) => ⟨lhs, rhs⟩ ∈ L)


def equation_list_corresponds_to_multiequation
  (L : List Equation)
  (M : Multiequation) :
  Prop :=
  (∀ (F : Formula_), F ∈ (equation_list_formula_list L) → F ∈ multiequation_formula_list M) ∧
  (∀ (F_1 F_2 : Formula_), (F_1 ∈ multiequation_formula_list M ∧ F_2 ∈ multiequation_formula_list M) → mem_equation_list_eqv_relation L F_1 F_2)


lemma mem_equation_list_eqv_relation_is_equation_unifier
  (σ : Substitution)
  (L : List Equation)
  (F_1 F_2 : Formula_)
  (h1 : is_equation_list_unifier σ L)
  (h2 : mem_equation_list_eqv_relation L F_1 F_2) :
  is_equation_unifier σ ⟨F_1, F_2⟩ :=
  by
  unfold is_equation_list_unifier at h1
  unfold is_equation_unifier at h1

  unfold mem_equation_list_eqv_relation at h2

  unfold is_equation_unifier

  induction h2
  case rel P Q ih_1 =>
    apply h1
    exact ih_1
  case refl F =>
    simp only
  case symm P Q ih_1 ih_2 =>
    simp only at ih_2

    simp only
    symm
    exact ih_2
  case trans P Q R ih_1 ih_2 ih_3 ih_4 =>
    simp only at ih_3

    simp only at ih_4

    simp only
    trans (replace_var_all_rec σ Q)
    · exact ih_3
    · exact ih_4


example
  (σ : Substitution)
  (L : List Equation)
  (M : Multiequation)
  (h1 : equation_list_corresponds_to_multiequation L M)
  (h2 : is_equation_list_unifier σ L) :
  is_multiequation_unifier σ M :=
  by
  unfold equation_list_corresponds_to_multiequation at h1
  obtain ⟨h1_left, h1_right⟩ := h1

  unfold is_multiequation_unifier
  intro F_1 F_2 a1
  apply mem_equation_list_eqv_relation_is_equation_unifier σ L F_1 F_2
  · exact h2
  · apply h1_right
    exact a1


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
  (h1 : equation_list_corresponds_to_multiequation L M)
  (h2 : is_multiequation_unifier σ M) :
  is_equation_list_unifier σ L :=
  by
  unfold equation_list_corresponds_to_multiequation at h1
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


def mem_multiequation_list_eqv_relation
  (L : List Multiequation) :
  Formula_ → Formula_ → Prop :=
  Relation.EqvGen (fun (lhs rhs : Formula_) => ∃ (M : Multiequation), M ∈ L ∧ lhs ∈ M.lhs ∧ rhs ∈ M.rhs)


-------------------------------------------------------------------------------


def is_in_solved_form :
  List (String × Formula_) → Prop
  | [] => True
  | (X, F) :: tl =>
    (¬ var_occurs_in_formula X F) ∧
      ∀ (pair : String × Formula_), pair ∈ tl →
        ((¬ X = pair.fst) ∧ (¬ var_occurs_in_formula X pair.snd))


inductive is_unification_step : List Equation → List Equation → Prop
| dec_not
  (phi phi' : Formula_)
  (Γ : List Equation) :
  is_unification_step (⟨not_ phi, not_ phi'⟩ :: Γ) (⟨phi, phi'⟩ :: Γ)

| triv
  (X X' : String)
  (Γ : List Equation) :
  X = X' →
  is_unification_step (⟨var_ X, var_ X'⟩ :: Γ) Γ

| var_lhs
  (X : String)
  (F : Formula_)
  (Γ : List Equation) :
  (∃ (E : Equation), E ∈ Γ ∧ (var_occurs_in_formula X E.lhs ∨ var_occurs_in_formula X E.rhs)) →
  (¬ var_occurs_in_formula X F) →
  is_unification_step (⟨var_ X, F⟩ :: Γ) (⟨var_ X, F⟩ :: var_elim X F Γ)

| var_rhs
  (X : String)
  (F : Formula_)
  (Γ : List Equation) :
  (∃ (E : Equation), E ∈ Γ ∧ (var_occurs_in_formula X E.lhs ∨ var_occurs_in_formula X E.rhs)) →
  (¬ var_occurs_in_formula X F) →
  is_unification_step (⟨F, var_ X⟩ :: Γ) (⟨F, var_ X⟩ :: var_elim X F Γ)


theorem extracted_1
  (X : String)
  (Γ : List Equation)
  (E : Equation)
  (h1 : E ∈ Γ)
  (h2 : X ∈ E.lhs.var_set ∨ X ∈ E.rhs.var_set) :
  X ∈ List.foldr (fun (next : Equation) (prev : Finset String) => next.lhs.var_set ∪ (next.rhs.var_set ∪ prev)) ∅ Γ :=
  by
  induction Γ
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1
    simp only [List.foldr_cons, Finset.mem_union]
    cases h1
    case inl h1 =>
      rewrite [h1] at h2
      cases h2
      case inl h2 =>
        left
        exact h2
      case inr h2 =>
        right
        left
        exact h2
    case inr h1 =>
      right
      right
      apply ih
      exact h1


theorem extracted_2
  (X : String)
  (Γ : List Equation)
  (h1 : ∀ (E : Equation), ¬ (E ∈ Γ ∧ (X ∈ E.lhs.var_set ∨ X ∈ E.rhs.var_set))) :
  X ∉ List.foldr (fun (next : Equation) (prev : Finset String) => next.lhs.var_set ∪ (next.rhs.var_set ∪ prev)) ∅ Γ :=
  by
  induction Γ
  case nil =>
    simp only [List.foldr_nil, Finset.not_mem_empty]
    intro contra
    exact contra
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1
    simp only [List.foldr_cons, Finset.mem_union]
    intro contra
    cases contra
    case inl contra =>
      apply h1 hd
      constructor
      · left
        rfl
      · left
        exact contra
    case inr contra =>
      cases contra
      case inl contra =>
        apply h1 hd
        constructor
        · left
          rfl
        · right
          exact contra
      case inr contra =>
        apply ih
        · intro E a1
          obtain ⟨a1_left, a1_right⟩ := a1
          apply h1 E
          constructor
          · right
            exact a1_left
          · exact a1_right
        · exact contra


lemma not_var_occurs_in_formula_imp_not_mem_var_elim_equation_list_var_set
  (X : String)
  (F : Formula_)
  (L : List Equation)
  (h1 : ¬ var_occurs_in_formula X F) :
  X ∉ equation_list_var_set (var_elim X F L) :=
  by
  unfold var_elim
  unfold equation_list_var_set
  simp only [Finset.union_assoc]
  induction L
  case nil =>
    simp only [List.map_nil, List.foldr_nil, Finset.not_mem_empty]
    intro contra
    exact contra
  case cons hd tl ih =>
    simp only [List.map_cons, List.foldr_cons, Finset.mem_union]
    intro contra
    cases contra
    case inl contra =>
      apply not_var_occurs_in_formula_imp_not_var_occurs_in_formula_replace_var_one_rec X F hd.lhs
      · exact h1
      · simp only [var_occurs_in_formula_iff_mem_formula_var_set]
        exact contra
    case inr contra =>
      cases contra
      case inl contra =>
        apply not_var_occurs_in_formula_imp_not_var_occurs_in_formula_replace_var_one_rec X F hd.rhs
        · exact h1
        · simp only [var_occurs_in_formula_iff_mem_formula_var_set]
          exact contra
      case inr contra =>
        contradiction


example
  (X : String)
  (F : Formula_)
  (Γ : List Equation) :
  (equation_list_var_set (var_elim X F Γ)) =  ((equation_list_var_set Γ) \ {X}) ∪ F.var_set :=
  by
  sorry


def unify :
  List Equation → Option (String → Formula_)
  | [] => Option.some var_
  | ⟨false_, false_⟩ :: Γ
  | ⟨true_, true_⟩ :: Γ => unify Γ
  | ⟨var_ X, F⟩ :: Γ
  | ⟨F, var_ X⟩ :: Γ =>
    if var_ X = F
    then unify Γ
    else
      if var_occurs_in_formula X F
      then Option.none
      else
        match unify (var_elim X F Γ) with
        | Option.none => Option.none
        | Option.some τ => Option.some (Function.updateITE τ X (replace_var_all_rec τ F))
  | ⟨not_ phi, not_ phi'⟩ :: Γ =>
      unify (⟨phi, phi'⟩ :: Γ)
  | ⟨and_ phi psi, and_ phi' psi'⟩ :: Γ
  | ⟨or_ phi psi, or_ phi' psi'⟩ :: Γ
  | ⟨imp_ phi psi, imp_ phi' psi'⟩ :: Γ
  | ⟨iff_ phi psi, iff_ phi' psi'⟩ :: Γ =>
      unify (⟨phi, phi'⟩ :: ⟨psi, psi'⟩ :: Γ)
  | _ => Option.none
  termination_by L => ((equation_list_var_set L).card, equation_list_size L)
  decreasing_by
  case _ | _ =>
    all_goals
    simp only [Prod.lex_def]
    right
    constructor
    · unfold equation_list_var_set
      simp only [Finset.union_assoc, List.foldr_cons, Finset.union_left_idem]
      simp only [var_set]
      simp only [Finset.empty_union]
    · unfold equation_list_size
      simp only [List.foldr_cons]
      simp only [Formula_.size]
      linarith
  case _ h1 =>
    rewrite [← h1]
    unfold equation_list_var_set
    simp only [Finset.union_assoc, List.foldr_cons, Finset.union_left_idem]
    simp only [var_set]

    simp only [Prod.lex_def]

    by_cases c1 : ∃ (E : Equation), E ∈ Γ ∧ (X ∈ E.lhs.var_set ∨ X ∈ E.rhs.var_set)
    case pos =>
      right
      constructor
      · obtain ⟨E, c1_left, c1_right⟩ := c1

        have s1 : {X} ∪ List.foldr (fun (next : Equation) (prev : Finset String) => next.lhs.var_set ∪ (next.rhs.var_set ∪ prev)) ∅ Γ =
          List.foldr (fun (next : Equation) (prev : Finset String) => next.lhs.var_set ∪ (next.rhs.var_set ∪ prev)) ∅ Γ :=
        by
          simp only [Finset.union_eq_right, Finset.singleton_subset_iff]
          apply extracted_1 X Γ E
          · exact c1_left
          · exact c1_right

        rewrite [s1]
        rfl
      · unfold equation_list_size
        simp only [List.foldr_cons]
        simp only [Formula_.size]
        linarith
    case neg =>
      simp only [not_exists] at c1

      have s1 : Disjoint {X} (List.foldr (fun next prev => next.lhs.var_set ∪ (next.rhs.var_set ∪ prev)) ∅ Γ) :=
      by
        simp only [Finset.disjoint_singleton_left]
        apply extracted_2
        intro E
        apply c1
      left
      simp only [Finset.card_union_of_disjoint s1]
      simp only [Finset.card_singleton]
      apply lt_one_add
  case _ h1 h2 =>
    apply Prod.Lex.left
    sorry
  all_goals
    sorry


def print_unify_list
  (L : List Equation) :
  Option (String → Formula_) → Option (Finset (Formula_ × Formula_))
  | Option.none => Option.none
  | Option.some σ => Option.some (Finset.image (fun (X : String) => (var_ X, σ X)) (equation_list_var_set L))

#eval! let L := [⟨var_ "P", var_ "Q"⟩]; print_unify_list L (unify L)

#eval! let L := [⟨var_ "X", not_ (var_ "X")⟩]; print_unify_list L (unify L)

#eval! let L := [⟨and_ (var_ "X") (var_ "Y"), and_ (var_ "Y") (var_ "Z")⟩]; print_unify_list L (unify L)

#eval! let L := [⟨or_ (and_ (var_ "X") (var_ "Y")) (var_ "Z"), or_ (and_ (var_ "Y") (var_ "Z")) (var_ "X")⟩]; print_unify_list L (unify L)
