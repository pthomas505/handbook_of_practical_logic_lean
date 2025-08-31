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
  (ES : List Equation) :
  Formula_ → Formula_ → Prop :=
  Relation.EqvGen (fun (lhs rhs : Formula_) => ⟨lhs, rhs⟩ ∈ ES)


def equation_list_corresponds_to_multiequation
  (ES : List Equation)
  (M : Multiequation) :
  Prop :=
  (∀ (F : Formula_), F ∈ (equation_list_formula_list ES) → F ∈ multiequation_formula_list M) ∧
  (∀ (F_1 F_2 : Formula_), (F_1 ∈ multiequation_formula_list M ∧ F_2 ∈ multiequation_formula_list M) → mem_equation_list_eqv_relation ES F_1 F_2)


lemma mem_equation_list_eqv_relation_is_equation_unifier
  (σ : Substitution)
  (ES : List Equation)
  (F_1 F_2 : Formula_)
  (h1 : is_equation_list_unifier σ ES)
  (h2 : mem_equation_list_eqv_relation ES F_1 F_2) :
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
  (ES : List Equation)
  (M : Multiequation)
  (h1 : equation_list_corresponds_to_multiequation ES M)
  (h2 : is_equation_list_unifier σ ES) :
  is_multiequation_unifier σ M :=
  by
  unfold equation_list_corresponds_to_multiequation at h1
  obtain ⟨h1_left, h1_right⟩ := h1

  unfold is_multiequation_unifier
  intro F_1 F_2 a1
  apply mem_equation_list_eqv_relation_is_equation_unifier σ ES F_1 F_2
  · exact h2
  · apply h1_right
    exact a1


example
  (σ : Substitution)
  (ES : List Equation)
  (M : Multiequation)
  (h1 : equation_list_corresponds_to_multiequation ES M)
  (h2 : is_multiequation_unifier σ M) :
  is_equation_list_unifier σ ES :=
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
  (MS : List Multiequation) :
  Formula_ → Formula_ → Prop :=
  Relation.EqvGen (fun (lhs rhs : Formula_) => ∃ (M : Multiequation), M ∈ MS ∧ lhs ∈ M.lhs ∧ rhs ∈ M.rhs)


-------------------------------------------------------------------------------


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
        match unify (equation_list_replace_var_one_rec X F Γ) with
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
  termination_by Γ => ((equation_list_var_set Γ).card, equation_list_size Γ)
  decreasing_by
  case _ | _ =>
    all_goals
    apply Prod.Lex.right'
    · apply Finset.card_le_card
      unfold equation_list_var_set
      simp only [List.foldr_cons, Finset.subset_union_right]
    · unfold equation_list_size
      unfold equation_list_formula_list
      unfold formula_list_size
      simp only [List.foldr_cons]
      simp only [Formula_.size]
      linarith

  case _ _ =>
    apply Prod.Lex.right'
    · apply Finset.card_le_card
      unfold equation_list_var_set
      simp only [List.foldr_cons, Finset.subset_union_right]
    · unfold equation_list_size
      unfold equation_list_formula_list
      unfold formula_list_size
      simp only [List.foldr_cons]
      simp only [Formula_.size]
      linarith
  case _ _ h2 =>
    apply Prod.Lex.left
    apply Finset.card_lt_card
    unfold equation_list_var_set
    simp only [List.foldr_cons]
    simp only [Equation.var_set]
    simp only [Formula_.var_set]
    apply extracted_1
    exact h2

  case _ _ =>
    apply Prod.Lex.right'
    · apply Finset.card_le_card
      unfold equation_list_var_set
      simp only [List.foldr_cons, Finset.subset_union_right]
    · unfold equation_list_size
      unfold equation_list_formula_list
      unfold formula_list_size
      simp only [List.foldr_cons]
      simp only [Formula_.size]
      linarith
  case _ _ h2 =>
    apply Prod.Lex.left
    apply Finset.card_lt_card
    unfold equation_list_var_set
    simp only [List.foldr_cons]
    simp only [Equation.var_set]
    simp only [Formula_.var_set]
    conv => right; left; rewrite [Finset.union_comm]
    apply extracted_1
    exact h2

  case _ =>
    apply Prod.Lex.right'
    · apply Finset.card_le_card
      unfold equation_list_var_set
      simp only [List.foldr_cons]
      simp only [Equation.var_set]
      simp only [Formula_.var_set]
      rfl
    · unfold equation_list_size
      unfold equation_list_formula_list
      unfold formula_list_size
      simp only [List.foldr_cons]
      simp only [Formula_.size]
      linarith

  all_goals
    apply Prod.Lex.right'
    · apply Finset.card_le_card
      unfold equation_list_var_set
      simp only [List.foldr_cons]
      simp only [Equation.var_set]
      simp only [Formula_.var_set]
      rewrite [← Finset.union_assoc]
      have s1 : phi.var_set ∪ phi'.var_set ∪ (psi.var_set ∪ psi'.var_set) = phi.var_set ∪ psi.var_set ∪ (phi'.var_set ∪ psi'.var_set) :=
      by
        rewrite [← Finset.union_assoc]
        conv => left; left; rewrite [Finset.union_assoc]; right; rewrite [Finset.union_comm]
        simp only [Finset.union_assoc]

      rewrite [s1]
      rfl
    · unfold equation_list_size
      unfold equation_list_formula_list
      unfold formula_list_size
      simp only [List.foldr_cons]
      simp only [Formula_.size]
      linarith


def print_unify_list
  (L : List Equation) :
  Option (String → Formula_) → Option (Finset (Formula_ × Formula_))
  | Option.none => Option.none
  | Option.some σ => Option.some (Finset.image (fun (X : String) => (var_ X, σ X)) (equation_list_var_set L))

#eval let L := [⟨var_ "P", var_ "Q"⟩]; print_unify_list L (unify L)

#eval let L := [⟨var_ "X", not_ (var_ "X")⟩]; print_unify_list L (unify L)

#eval let L := [⟨and_ (var_ "X") (var_ "Y"), and_ (var_ "Y") (var_ "Z")⟩]; print_unify_list L (unify L)

#eval let L := [⟨or_ (and_ (var_ "X") (var_ "Y")) (var_ "Z"), or_ (and_ (var_ "Y") (var_ "Z")) (var_ "X")⟩]; print_unify_list L (unify L)
