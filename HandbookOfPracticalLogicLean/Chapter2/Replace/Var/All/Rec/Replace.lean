import HandbookOfPracticalLogicLean.Chapter2.Replace.Var.One.Rec.Replace
import HandbookOfPracticalLogicLean.Chapter2.SubFormula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `replace_atom_all_rec τ F` := The simultaneous replacement of each occurrence of any atom `A` in the formula `F` by `τ A`.
-/
def replace_atom_all_rec
  (τ : String → Formula_) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | atom_ X => τ X
  | not_ phi => not_ (replace_atom_all_rec τ phi)
  | and_ phi psi => and_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)
  | or_ phi psi => or_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)
  | imp_ phi psi => imp_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)
  | iff_ phi psi => iff_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)


lemma replace_atom_all_rec_id
  (F : Formula_) :
  replace_atom_all_rec (fun (X : String) => atom_ X) F = F :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold replace_atom_all_rec
    rfl
  case not_ phi ih =>
    unfold replace_atom_all_rec
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_atom_all_rec
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


lemma replace_atom_all_rec_compose
  (σ τ : String → Formula_)
  (F : Formula_) :
  replace_atom_all_rec ((replace_atom_all_rec τ) ∘ σ) F =
    replace_atom_all_rec τ (replace_atom_all_rec σ F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [replace_atom_all_rec]
  case atom_ X =>
    simp only [replace_atom_all_rec]
    exact Function.comp_apply
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


lemma replace_atom_all_rec_eq_replace_atom_all_rec_of_replace_atom_one_rec
  (σ : String → Formula_)
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


theorem theorem_2_3_all
  (V : ValuationAsTotalFunction)
  (τ : String → Formula_)
  (F : Formula_) :
  eval V (replace_atom_all_rec τ F) = eval ((eval V) ∘ τ) F :=
  by
  induction F
  case false_ | true_ =>
    simp only [eval]
  case atom_ X =>
    unfold replace_atom_all_rec
    simp only [eval]
    rfl
  case not_ phi ih =>
    simp only [eval]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


theorem corollary_2_4_all
  (τ : String → Formula_)
  (F : Formula_)
  (h1 : F.is_tautology) :
  (replace_atom_all_rec τ F).is_tautology :=
  by
  unfold is_tautology at h1
  unfold satisfies at h1

  unfold is_tautology
  unfold satisfies
  intro V
  rewrite [theorem_2_3_all]
  apply h1


theorem theorem_2_5_all
  (V : ValuationAsTotalFunction)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → eval V (τ1 A) = eval V (τ2 A)) :
  eval V (replace_atom_all_rec τ1 F) = eval V (replace_atom_all_rec τ2 F) :=
  by
  simp only [theorem_2_3_all]
  apply theorem_2_2
  simp only [Function.comp_apply]
  exact h1


example
  (V : ValuationAsTotalFunction)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (A : String), eval V (τ1 A) = eval V (τ2 A)) :
  eval V (replace_atom_all_rec τ1 F) = eval V (replace_atom_all_rec τ2 F) :=
  by
  apply theorem_2_5_all
  intro A a1
  apply h1


theorem corollary_2_6_all
  (V : ValuationAsTotalFunction)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → are_logically_equivalent (τ1 A) (τ2 A)) :
  eval V (replace_atom_all_rec τ1 F) = eval V (replace_atom_all_rec τ2 F) :=
  by
  simp only [are_logically_equivalent_iff_eval_eq] at h1

  apply theorem_2_5_all
  intro A a1
  apply h1
  exact a1


example
  (V : ValuationAsTotalFunction)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (A : String), are_logically_equivalent (τ1 A) (τ2 A)) :
  eval V (replace_atom_all_rec τ1 F) = eval V (replace_atom_all_rec τ2 F) :=
  by
  apply corollary_2_6_all
  intro A a1
  apply h1


-------------------------------------------------------------------------------


lemma is_subformula_imp_is_subformula_replace_atom_all_rec
  (σ : String → Formula_)
  (F F' : Formula_)
  (h1 : is_subformula F F') :
  is_subformula (replace_atom_all_rec σ F) (replace_atom_all_rec σ F') :=
  by
  induction F'
  case false_ | true_ | atom_ X =>
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
      simp only [replace_atom_all_rec]
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
      simp only [replace_atom_all_rec]
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


lemma is_proper_subformula_v2_imp_replace_atom_all_rec_not_eq
  (σ : String → Formula_)
  (F F' : Formula_)
  (h1 : is_proper_subformula_v2 F F') :
  ¬ replace_atom_all_rec σ F = replace_atom_all_rec σ F' :=
  by
  cases F'
  case false_ | true_ | atom_ X =>
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
      obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec σ F phi h1_left
      intro contra
      rewrite [contra] at s1
      simp only [replace_atom_all_rec] at s1
      apply not_is_subformula_not (replace_atom_all_rec σ phi)
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
        obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec σ F phi h1_left
        intro contra
        rewrite [contra] at s1
        simp only [replace_atom_all_rec] at s1
        first
        | exact not_is_subformula_and_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_or_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_imp_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_iff_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
      case inr h1_left =>
        obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec σ F psi h1_left
        intro contra
        rewrite [contra] at s1
        simp only [replace_atom_all_rec] at s1
        first
        | exact not_is_subformula_and_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_or_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_imp_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_iff_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1


lemma is_proper_subformula_v2_imp_is_proper_subformula_v2_replace_atom_all_rec
  (σ : String → Formula_)
  (F F' : Formula_)
  (h1 : is_proper_subformula_v2 F F') :
  is_proper_subformula_v2 (replace_atom_all_rec σ F) (replace_atom_all_rec σ F') :=
  by
  unfold is_proper_subformula_v2 at h1
  obtain ⟨h1_left, h1_right⟩ := h1

  unfold is_proper_subformula_v2
  constructor
  · apply is_subformula_imp_is_subformula_replace_atom_all_rec
    exact h1_left
  · apply is_proper_subformula_v2_imp_replace_atom_all_rec_not_eq
    unfold is_proper_subformula_v2
    exact ⟨h1_left, h1_right⟩


#lint
