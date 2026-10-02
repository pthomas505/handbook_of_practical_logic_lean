import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Prop.Semantics

import Mathlib.Tactic


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


open Formula_


/--
  `replace_var_one_rec V P F` :=

  `V → P` in `F` for each occurrence of the variable `V` in the formula `F`

  The result of simultaneously replacing each occurrence of the variable `V` in the formula `F` by an occurrence of the formula `P`.
-/
@[nolint defsWithUnderscore]
def replace_var_one_rec
  (V : String)
  (P : Formula_) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | var_ X => if V = X then P else var_ X
  | not_ phi => not_ (replace_var_one_rec V P phi)
  | and_ phi psi => and_ (replace_var_one_rec V P phi) (replace_var_one_rec V P psi)
  | or_ phi psi => or_ (replace_var_one_rec V P phi) (replace_var_one_rec V P psi)
  | imp_ phi psi => imp_ (replace_var_one_rec V P phi) (replace_var_one_rec V P psi)
  | iff_ phi psi => iff_ (replace_var_one_rec V P phi) (replace_var_one_rec V P psi)


theorem theorem_2_3_one
  (σ : ValuationAsTotalFunction)
  (V : String)
  (P : Formula_)
  (F : Formula_) :
  eval σ (replace_var_one_rec V P F) = eval (Function.updateITE' σ V (eval σ P)) F :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec
    unfold eval
    apply Eq.refl
  case var_ X =>
    unfold replace_var_one_rec
    simp only [eval]
    unfold Function.updateITE'
    split
    case isTrue c1 =>
      apply Eq.refl
    case isFalse c1 =>
      unfold eval
      apply Eq.refl
  case not_ phi ih =>
    unfold replace_var_one_rec
    simp only [eval]
    rewrite [ih]
    apply Eq.refl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    apply Eq.refl


theorem corollary_2_4_one
  (V : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : F.is_tautology) :
  ((replace_var_one_rec V P F)).is_tautology :=
  by
  unfold is_tautology at h1
  unfold satisfies at h1

  unfold is_tautology
  unfold satisfies
  intro V
  simp only [theorem_2_3_one]
  apply h1


theorem theorem_2_5_one
  (σ : ValuationAsTotalFunction)
  (V : String)
  (P Q : Formula_)
  (F : Formula_)
  (h1 : eval σ P = eval σ Q) :
  eval σ (replace_var_one_rec V P F) = eval σ (replace_var_one_rec V Q F) :=
  by
  simp only [theorem_2_3_one]
  rewrite [h1]
  apply Eq.refl


theorem corollary_2_6_one
  (σ : ValuationAsTotalFunction)
  (V : String)
  (P Q : Formula_)
  (F : Formula_)
  (h1 : are_logically_equivalent P Q) :
  eval σ (replace_var_one_rec V P F) = eval σ (replace_var_one_rec V Q F) :=
  by
  simp only [are_logically_equivalent_iff_eval_eq] at h1

  apply theorem_2_5_one
  apply h1


-------------------------------------------------------------------------------


theorem not_var_occurs_in_formula_replace_var_one_rec
  (V : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : ¬ var_occurs_in_formula V F) :
  replace_var_one_rec V P F = F :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec
    apply Eq.refl
  case var_ X =>
    unfold var_occurs_in_formula at h1

    unfold replace_var_one_rec
    split
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      apply Eq.refl
  case not_ phi ih =>
    unfold var_occurs_in_formula at h1

    unfold replace_var_one_rec
    congr
    apply ih
    exact h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h1

    unfold replace_var_one_rec
    congr
    · apply phi_ih
      intro contra
      apply h1
      left
      exact contra
    · apply psi_ih
      intro contra
      apply h1
      right
      exact contra


-------------------------------------------------------------------------------


theorem var_occurs_in_formula_replace_var_one_rec_eq_1
  (V : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : var_occurs_in_formula V (replace_var_one_rec V P F)) :
  var_occurs_in_formula V P :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1
    contradiction
  case var_ X =>
    unfold replace_var_one_rec at h1

    split at h1
    case isTrue c1 =>
      exact h1
    case isFalse c1 =>
      unfold var_occurs_in_formula at h1
      contradiction
  case not_ phi ih =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1

    apply ih
    exact h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1

    cases h1
    case inl h1 =>
      apply phi_ih
      exact h1
    case inr h1 =>
      apply psi_ih
      exact h1


theorem var_occurs_in_formula_replace_var_one_rec_eq_2
  (V : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : var_occurs_in_formula V (replace_var_one_rec V P F)) :
  var_occurs_in_formula V F :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1
    contradiction
  case var_ X =>
    unfold replace_var_one_rec at h1

    split at h1
    case isTrue c1 =>
      unfold var_occurs_in_formula
      exact c1
    case isFalse c1 =>
      unfold var_occurs_in_formula at h1
      contradiction
  case not_ phi ih =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1

    unfold var_occurs_in_formula
    apply ih
    exact h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1

    unfold var_occurs_in_formula
    cases h1
    case inl h1 =>
      left
      apply phi_ih
      exact h1
    case inr h1 =>
      right
      apply psi_ih
      exact h1


theorem var_occurs_in_formula_replace_var_one_rec_eq_3
  (V : String)
  (P : Formula_)
  (F : Formula_)
  (Z : String)
  (h1 : var_occurs_in_formula Z P)
  (h2 : var_occurs_in_formula V F) :
  var_occurs_in_formula Z (replace_var_one_rec V P F) :=
  by
  induction F
  case false_ | true_ =>
    unfold var_occurs_in_formula at h2
    contradiction
  case var_ X =>
    unfold var_occurs_in_formula at h2

    unfold replace_var_one_rec
    split
    case isTrue c1 =>
      exact h1
    case isFalse c1 =>
      contradiction
  case not_ phi ih =>
    unfold var_occurs_in_formula at h2

    unfold replace_var_one_rec
    unfold var_occurs_in_formula
    apply ih
    exact h2
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h2

    unfold replace_var_one_rec
    unfold var_occurs_in_formula
    cases h2
    case inl h2 =>
      left
      apply phi_ih
      exact h2
    case inr h2 =>
      right
      apply psi_ih
      exact h2


-------------------------------------------------------------------------------


theorem var_occurs_in_formula_replace_var_one_rec_ne_1
  (V : String)
  (P : Formula_)
  (F : Formula_)
  (Z : String)
  (h1 : ¬ Z = V)
  (h2 : var_occurs_in_formula Z F) :
  var_occurs_in_formula Z (replace_var_one_rec V P F) :=
  by
  induction F
  case false_ | true_ =>
    unfold var_occurs_in_formula at h2
    contradiction
  case var_ X =>
    unfold var_occurs_in_formula at h2

    unfold replace_var_one_rec
    split
    case isTrue c1 =>
      rewrite [h2] at h1
      rewrite [c1] at h1
      contradiction
    case isFalse c1 =>
      unfold var_occurs_in_formula
      exact h2
  case not_ phi ih =>
    unfold var_occurs_in_formula at h2

    unfold replace_var_one_rec
    unfold var_occurs_in_formula
    apply ih
    exact h2
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h2

    unfold replace_var_one_rec
    unfold var_occurs_in_formula
    cases h2
    case inl h2 =>
      left
      apply phi_ih
      exact h2
    case inr h2 =>
      right
      apply psi_ih
      exact h2


theorem var_occurs_in_formula_replace_var_one_rec_ne_2
  (V : String)
  (P : Formula_)
  (F : Formula_)
  (Z : String)
  (h1 : var_occurs_in_formula Z (replace_var_one_rec V P F))
  (h2 : ¬ var_occurs_in_formula Z F) :
  var_occurs_in_formula Z P :=
  by
  induction F
  case false_ | true_ =>
    unfold var_occurs_in_formula at h2
    contradiction
  case var_ X =>
    unfold replace_var_one_rec at h1

    unfold var_occurs_in_formula at h2

    split at h1
    case isTrue c1 =>
      exact h1
    case isFalse c1 =>
      unfold var_occurs_in_formula at h1
      contradiction
  case not_ phi ih =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1

    unfold var_occurs_in_formula at h2

    exact ih h1 h2
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1

    unfold var_occurs_in_formula at h2
    rewrite [not_or] at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    cases h1
    case inl h1 =>
      exact phi_ih h1 h2_left
    case inr h1 =>
      exact psi_ih h1 h2_right


theorem var_occurs_in_formula_replace_var_one_rec_ne_3
  (V : String)
  (P : Formula_)
  (F : Formula_)
  (Z : String)
  (h1 : var_occurs_in_formula Z (replace_var_one_rec V P F))
  (h2 : ¬ var_occurs_in_formula Z F) :
  var_occurs_in_formula V F :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec at h1
    contradiction
  case var_ X =>
    unfold replace_var_one_rec at h1

    split at h1
    case isTrue c1 =>
      unfold var_occurs_in_formula
      exact c1
    case isFalse c1 =>
      unfold var_occurs_in_formula at h1
      unfold var_occurs_in_formula at h2
      contradiction
  case not_ phi ih =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1

    unfold var_occurs_in_formula at h2

    unfold var_occurs_in_formula
    exact ih h1 h2
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1

    unfold var_occurs_in_formula at h2
    rewrite [not_or] at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    unfold var_occurs_in_formula
    cases h1
    case inl h1 =>
      left
      exact phi_ih h1 h2_left
    case inr h1 =>
      right
      exact psi_ih h1 h2_right


-------------------------------------------------------------------------------


theorem replace_var_one_rec_eq
  (V : String)
  (F : Formula_) :
  replace_var_one_rec V (Formula_.var_ V) F = F :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec
    apply Eq.refl
  case var_ X =>
    unfold replace_var_one_rec

    split
    case isTrue c1 =>
      rewrite [c1]
      apply Eq.refl
    case isFalse c1 =>
      apply Eq.refl
  case not_ phi ih =>
    unfold replace_var_one_rec

    rewrite [ih]
    apply Eq.refl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec
    rewrite [phi_ih]
    rewrite [psi_ih]
    apply Eq.refl


-------------------------------------------------------------------------------


theorem var_occurs_in_formula_replace_var_one_rec_eq_var_1
  (V : String)
  (Z : String)
  (F : Formula_)
  (h1 : var_occurs_in_formula V (replace_var_one_rec V (Formula_.var_ Z) F)) :
  V = Z :=
  by
  obtain s1 := var_occurs_in_formula_replace_var_one_rec_eq_1 V (Formula_.var_ Z) F h1
  unfold var_occurs_in_formula at s1
  exact s1


theorem var_occurs_in_formula_replace_var_one_rec_eq_var_2
  (V : String)
  (Z : String)
  (F : Formula_)
  (h1 : var_occurs_in_formula V (replace_var_one_rec V (Formula_.var_ Z) F)) :
  var_occurs_in_formula V F :=
  by
  exact var_occurs_in_formula_replace_var_one_rec_eq_2 V (Formula_.var_ Z) F h1


theorem var_occurs_in_formula_replace_var_one_rec_ne_var_1
  (V : String)
  (Y : String)
  (F : Formula_)
  (Z : String)
  (h1 : ¬ Z = V)
  (h2 : var_occurs_in_formula Z F) :
  var_occurs_in_formula Z (replace_var_one_rec V (Formula_.var_ Y) F) :=
  by
  exact var_occurs_in_formula_replace_var_one_rec_ne_1 V (Formula_.var_ Y) F Z h1 h2


theorem var_occurs_in_formula_replace_var_one_rec_ne_var_2
  (V : String)
  (Y : String)
  (F : Formula_)
  (Z : String)
  (h1 : var_occurs_in_formula Z (replace_var_one_rec V (Formula_.var_ Y) F))
  (h2 : ¬ var_occurs_in_formula Z F) :
  Z = Y :=
  by
  obtain s1 := var_occurs_in_formula_replace_var_one_rec_ne_2 V (Formula_.var_ Y) F Z h1 h2
  unfold var_occurs_in_formula at s1
  exact s1


theorem var_occurs_in_formula_replace_var_one_rec_ne_var_3
  (V : String)
  (Y : String)
  (F : Formula_)
  (Z : String)
  (h1 : var_occurs_in_formula Z (replace_var_one_rec V (Formula_.var_ Y) F))
  (h2 : ¬ var_occurs_in_formula Z F) :
  var_occurs_in_formula V F :=
  by
  exact var_occurs_in_formula_replace_var_one_rec_ne_3 V (Formula_.var_ Y) F Z h1 h2


-------------------------------------------------------------------------------


example
  (V : String)
  (P : Formula_)
  (F : Formula_) :
  F.var_set \ {V} ⊆ (replace_var_one_rec V P F).var_set :=
  by
  simp only [Finset.subset_iff]
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  intro Z a1
  obtain ⟨a1_left, a1_right⟩ := a1
  rewrite [← var_occurs_in_formula_iff_mem_formula_var_set] at a1_left
  rewrite [← var_occurs_in_formula_iff_mem_formula_var_set]
  apply var_occurs_in_formula_replace_var_one_rec_ne_1
  · exact a1_right
  · exact a1_left


example
  (V : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : var_occurs_in_formula V F) :
  P.var_set ⊆ (replace_var_one_rec V P F).var_set :=
  by
  simp only [Finset.subset_iff]
  intro Z a1
  rewrite [← var_occurs_in_formula_iff_mem_formula_var_set] at a1
  rewrite [← var_occurs_in_formula_iff_mem_formula_var_set]
  apply var_occurs_in_formula_replace_var_one_rec_eq_3
  · exact a1
  · exact h1


theorem replace_var_one_rec_var_set_subset
  (V : String)
  (P : Formula_)
  (F : Formula_) :
  (replace_var_one_rec V P F).var_set ⊆ P.var_set ∪ F.var_set :=
  by
  simp only [Finset.subset_iff]
  intro Z a1
  rewrite [← var_occurs_in_formula_iff_mem_formula_var_set] at a1
  simp only [Finset.mem_union]
  simp only [← var_occurs_in_formula_iff_mem_formula_var_set]
  obtain s1 := var_occurs_in_formula_replace_var_one_rec_ne_2 V P F Z a1
  by_cases c1 : var_occurs_in_formula Z F
  · right
    exact c1
  · left
    exact var_occurs_in_formula_replace_var_one_rec_ne_2 V P F Z a1 c1


#lint
