import HandbookOfPracticalLogicLean.Prop.Replace.Var.One.Rec.Replace
import HandbookOfPracticalLogicLean.Prop.SubFormula

import Mathlib.Tactic


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


open Formula_


/--
  `replace_var_all_rec τ F` := The simultaneous replacement of each occurrence of any variable `V` in the formula `F` by `τ V`.
-/
@[nolint defsWithUnderscore]
def replace_var_all_rec
  (τ : String → Formula_) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | var_ X => τ X
  | not_ phi => not_ (replace_var_all_rec τ phi)
  | and_ phi psi => and_ (replace_var_all_rec τ phi) (replace_var_all_rec τ psi)
  | or_ phi psi => or_ (replace_var_all_rec τ phi) (replace_var_all_rec τ psi)
  | imp_ phi psi => imp_ (replace_var_all_rec τ phi) (replace_var_all_rec τ psi)
  | iff_ phi psi => iff_ (replace_var_all_rec τ phi) (replace_var_all_rec τ psi)


theorem replace_var_all_rec_id
  (F : Formula_) :
  replace_var_all_rec var_ F = F :=
  by
  induction F
  case false_ | true_ | var_ X =>
    unfold replace_var_all_rec
    apply Eq.refl
  case not_ phi ih =>
    unfold replace_var_all_rec
    rewrite [ih]
    apply Eq.refl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_all_rec
    rewrite [phi_ih]
    rewrite [psi_ih]
    apply Eq.refl


theorem replace_var_all_rec_compose
  (σ τ : String → Formula_)
  (F : Formula_) :
  replace_var_all_rec ((replace_var_all_rec τ) ∘ σ) F =
    replace_var_all_rec τ (replace_var_all_rec σ F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [replace_var_all_rec]
  case var_ X =>
    simp only [replace_var_all_rec]
    exact Function.comp_apply
  case not_ phi ih =>
    simp only [replace_var_all_rec]
    rewrite [ih]
    apply Eq.refl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [replace_var_all_rec]
    rewrite [phi_ih]
    rewrite [psi_ih]
    apply Eq.refl


theorem replace_var_all_rec_function_update_ite_not_occurs_in
  (σ : String → Formula_)
  (V : String)
  (F : Formula_)
  (H : Formula_)
  (h1 : ¬ var_occurs_in_formula V F) :
  replace_var_all_rec (Function.updateITE' σ V H) F =
    replace_var_all_rec σ F :=
  by
  induction F
  case false_ | true_ =>
    simp only [replace_var_all_rec]
  case var_ X =>
    simp only [var_occurs_in_formula] at h1

    simp only [replace_var_all_rec]
    unfold Function.updateITE'
    split
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      apply Eq.refl
  case not_ phi ih =>
    unfold var_occurs_in_formula at h1

    unfold replace_var_all_rec
    congr 1
    apply ih
    exact h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h1
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold replace_var_all_rec
    congr 1
    · exact phi_ih h1_left
    · exact psi_ih h1_right


theorem replace_var_all_rec_eq_replace_var_all_rec_of_replace_var_one_rec
  (σ : String → Formula_)
  (X' : String)
  (F' : Formula_)
  (F : Formula_)
  (h1 : σ X' = replace_var_all_rec σ F') :
  replace_var_all_rec σ F =
    replace_var_all_rec σ (replace_var_one_rec X' F' F) :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec
    apply Eq.refl
  case var_ X =>
    unfold replace_var_one_rec
    split
    case isTrue c1 =>
      simp only [replace_var_all_rec]
      rewrite [← c1]
      exact h1
    case isFalse c1 =>
      apply Eq.refl
  case not_ phi ih =>
    unfold replace_var_one_rec
    simp only [replace_var_all_rec]
    rewrite [ih]
    apply Eq.refl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec
    simp only [replace_var_all_rec]
    rewrite [phi_ih]
    rewrite [psi_ih]
    apply Eq.refl


-------------------------------------------------------------------------------


theorem theorem_2_3_all
  (σ : ValuationAsTotalFunction)
  (τ : String → Formula_)
  (F : Formula_) :
  eval σ (replace_var_all_rec τ F) = eval ((eval σ) ∘ τ) F :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_all_rec
    unfold eval
    apply Eq.refl
  case var_ X =>
    unfold replace_var_all_rec
    simp only [eval]
    simp only [Function.comp_apply]
  case not_ phi ih =>
    unfold replace_var_all_rec
    simp only [eval]
    rewrite [ih]
    apply Eq.refl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_all_rec
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    apply Eq.refl


theorem corollary_2_4_all
  (τ : String → Formula_)
  (F : Formula_)
  (h1 : F.is_tautology) :
  (replace_var_all_rec τ F).is_tautology :=
  by
  unfold is_tautology at h1
  unfold satisfies at h1

  unfold is_tautology
  unfold satisfies
  intro σ
  rewrite [theorem_2_3_all]
  apply h1


theorem theorem_2_5_all
  (σ : ValuationAsTotalFunction)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (V : String), var_occurs_in_formula V F → eval σ (τ1 V) = eval σ (τ2 V)) :
  eval σ (replace_var_all_rec τ1 F) = eval σ (replace_var_all_rec τ2 F) :=
  by
  simp only [theorem_2_3_all]
  apply theorem_2_2
  simp only [Function.comp_apply]
  exact h1


example
  (σ : ValuationAsTotalFunction)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (V : String), eval σ (τ1 V) = eval σ (τ2 V)) :
  eval σ (replace_var_all_rec τ1 F) = eval σ (replace_var_all_rec τ2 F) :=
  by
  apply theorem_2_5_all
  intro V a1
  apply h1


theorem corollary_2_6_all
  (σ : ValuationAsTotalFunction)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (V : String), var_occurs_in_formula V F → are_logically_equivalent (τ1 V) (τ2 V)) :
  eval σ (replace_var_all_rec τ1 F) = eval σ (replace_var_all_rec τ2 F) :=
  by
  simp only [are_logically_equivalent_iff_eval_eq] at h1

  apply theorem_2_5_all
  intro V a1
  apply h1
  exact a1


example
  (σ : ValuationAsTotalFunction)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (V : String), are_logically_equivalent (τ1 V) (τ2 V)) :
  eval σ (replace_var_all_rec τ1 F) = eval σ (replace_var_all_rec τ2 F) :=
  by
  apply corollary_2_6_all
  intro V a1
  apply h1


-------------------------------------------------------------------------------


theorem is_subformula_imp_is_subformula_replace_var_all_rec
  (σ : String → Formula_)
  (F F' : Formula_)
  (h1 : is_subformula F F') :
  is_subformula (replace_var_all_rec σ F) (replace_var_all_rec σ F') :=
  by
  induction F'
  case false_ | true_ | var_ X =>
    unfold is_subformula at h1
    rewrite [h1]
    apply is_subformula_refl
  case not_ phi ih =>
    unfold is_subformula at h1

    cases h1
    case inl h1 =>
      rewrite [h1]
      apply is_subformula_refl
    case inr h1 =>
      simp only [replace_var_all_rec]
      unfold is_subformula
      right
      apply ih
      exact h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold is_subformula at h1

    cases h1
    case inl h1 =>
      rewrite [h1]
      apply is_subformula_refl
    case inr h1 =>
      simp only [replace_var_all_rec]
      unfold is_subformula
      right

      cases h1
      case inl h1 =>
        left
        apply phi_ih
        exact h1
      case inr h1 =>
        right
        apply psi_ih
        exact h1


theorem is_proper_subformula_v2_imp_replace_var_all_rec_not_eq
  (σ : String → Formula_)
  (F F' : Formula_)
  (h1 : is_proper_subformula_v2 F F') :
  ¬ replace_var_all_rec σ F = replace_var_all_rec σ F' :=
  by
  cases F'
  case false_ | true_ | var_ X =>
    unfold is_proper_subformula_v2 at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    unfold is_subformula at h1_left
    contradiction
  case not_ phi =>
    unfold is_proper_subformula_v2 at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    unfold is_subformula at h1_left

    cases h1_left
    case inl h1_left =>
      contradiction
    case inr h1_left =>
      obtain s1 := is_subformula_imp_is_subformula_replace_var_all_rec σ F phi h1_left
      intro contra
      rewrite [contra] at s1
      simp only [replace_var_all_rec] at s1
      apply not_is_subformula_not (replace_var_all_rec σ phi)
      exact s1
  case
      and_ phi psi
    | or_ phi psi
    | imp_ phi psi
    | iff_ phi psi =>
    unfold is_proper_subformula_v2 at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    unfold is_subformula at h1_left

    cases h1_left
    case inl h1_left =>
      contradiction
    case inr h1_left =>
      cases h1_left
      case inl h1_left =>
        obtain s1 := is_subformula_imp_is_subformula_replace_var_all_rec σ F phi h1_left

        intro contra
        rewrite [contra] at s1
        simp only [replace_var_all_rec] at s1

        first
        | exact not_is_subformula_and_left (replace_var_all_rec σ phi) (replace_var_all_rec σ psi) s1
        | exact not_is_subformula_or_left (replace_var_all_rec σ phi) (replace_var_all_rec σ psi) s1
        | exact not_is_subformula_imp_left (replace_var_all_rec σ phi) (replace_var_all_rec σ psi) s1
        | exact not_is_subformula_iff_left (replace_var_all_rec σ phi) (replace_var_all_rec σ psi) s1
      case inr h1_left =>
        obtain s1 := is_subformula_imp_is_subformula_replace_var_all_rec σ F psi h1_left

        intro contra
        rewrite [contra] at s1
        simp only [replace_var_all_rec] at s1

        first
        | exact not_is_subformula_and_right (replace_var_all_rec σ phi) (replace_var_all_rec σ psi) s1
        | exact not_is_subformula_or_right (replace_var_all_rec σ phi) (replace_var_all_rec σ psi) s1
        | exact not_is_subformula_imp_right (replace_var_all_rec σ phi) (replace_var_all_rec σ psi) s1
        | exact not_is_subformula_iff_right (replace_var_all_rec σ phi) (replace_var_all_rec σ psi) s1


theorem is_proper_subformula_v2_imp_is_proper_subformula_v2_replace_var_all_rec
  (σ : String → Formula_)
  (F F' : Formula_)
  (h1 : is_proper_subformula_v2 F F') :
  is_proper_subformula_v2 (replace_var_all_rec σ F) (replace_var_all_rec σ F') :=
  by
  unfold is_proper_subformula_v2 at h1
  obtain ⟨h1_left, h1_right⟩ := h1

  unfold is_proper_subformula_v2
  constructor
  · apply is_subformula_imp_is_subformula_replace_var_all_rec
    exact h1_left
  · apply is_proper_subformula_v2_imp_replace_var_all_rec_not_eq
    unfold is_proper_subformula_v2
    exact ⟨h1_left, h1_right⟩


#lint
