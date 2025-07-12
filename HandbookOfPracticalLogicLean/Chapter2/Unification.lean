import HandbookOfPracticalLogicLean.Chapter2.Replace
import HandbookOfPracticalLogicLean.Chapter2.SubFormula

import Batteries.Data.HashMap


set_option autoImplicit false


open Formula_


def Instantiation : Type := String → Formula_


/--
  `is_unifier σ S` := True if and only if the instantiation `σ` is a unifier of the set of pairs of formulas `S`.
-/
def is_unifier
  (σ : Instantiation)
  (S : Set (Formula_ × Formula_)) :
  Prop :=
  ∀ (p : (Formula_ × Formula_)), p ∈ S →
    replace_atom_all_rec σ p.fst =
      replace_atom_all_rec σ p.snd


lemma replace_atom_all_rec_compose
  (F : Formula_)
  (σ τ : Instantiation) :
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


example
  (σ τ : Instantiation)
  (S : Set (Formula_ × Formula_))
  (h1 : is_unifier σ S) :
  is_unifier ((replace_atom_all_rec τ) ∘ σ) S :=
  by
  unfold is_unifier at h1
  unfold is_unifier
  intro p a1
  simp only [replace_atom_all_rec_compose]
  rewrite [h1 p a1]
  rfl


/--
  `is_more_general_instantiation σ τ` := True if and only if the instantiation `σ` is more general than the instantiation `τ`.
  `σ ≤ τ`
-/
def is_more_general_instantiation
  (σ τ : Instantiation) :
  Prop :=
  ∃ (δ : Instantiation), replace_atom_all_rec τ = (replace_atom_all_rec δ) ∘ (replace_atom_all_rec σ)


example
  (σ : Instantiation) :
  is_more_general_instantiation σ σ :=
  by
  unfold is_more_general_instantiation
  apply Exists.intro (fun (X : String) => (atom_ X))
  funext F
  simp only [Function.comp_apply]
  simp only [replace_atom_all_rec_id]


/--
  `is_most_general_unifier σ S` := True if and only if the instantiation `σ` is a most general unifier (MGU) of the set of pairs of formulas `S`.
-/
def is_most_general_unifier
  (σ : Instantiation)
  (S : Set (Formula_ × Formula_)) :
  Prop :=
  is_unifier σ S ∧ ∀ (τ : Instantiation), is_unifier τ S → is_more_general_instantiation σ τ


/-
def Environment : Type := Batteries.HashMap String Formula_

def is_small_step
  (E : Environment)
  (X Y : String) :
  Prop :=
  match E.find? X with
  | none => False
  | some F =>
    if atom_occurs_in Y F
    then True
    else False
-/


def Environment : Type := String → Formula_

def is_small_step
  (E : Environment)
  (X Y : String) :
  Prop :=
  atom_occurs_in Y (E X)

instance
  (E : Environment)
  (X Y : String) :
  Decidable (is_small_step E X Y) :=
  by
  unfold is_small_step
  infer_instance


def is_big_step
  (E : Environment)
  (X Y : String)
  (l : List String) :
  Prop :=
  List.Chain (is_small_step E) X (l ++ [Y])

instance
  (E : Environment)
  (X Y : String)
  (l : List String) :
  Decidable (is_big_step E X Y l) :=
  by
  unfold is_big_step
  infer_instance


def Environment.has_cycle
  (E : Environment) :
  Prop :=
  ∃ (X : String), ∃ (l : List String), is_big_step E X X l


lemma is_subformula_imp_is_subformula_replace_atom_all_rec
  (F F' : Formula_)
  (σ : Instantiation)
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
  (F F' : Formula_)
  (σ : Instantiation)
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
      obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec F phi σ h1_left
      intro contra
      rewrite [contra] at s1
      simp only [replace_atom_all_rec] at s1
      apply not_is_subformula_not (replace_atom_all_rec σ phi)
      exact s1
  case and_ phi psi =>
    unfold is_proper_subformula_v2 at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    unfold is_subformula at h1_left

    cases h1_left
    case inl h1_left =>
      contradiction
    case inr h1_left =>
      cases h1_left
      case inl h1_left =>
        obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec F phi σ h1_left
        intro contra
        rewrite [contra] at s1
        simp only [replace_atom_all_rec] at s1
        sorry
      case inr h1_left =>
        obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec F psi σ h1_left
        intro contra
        rewrite [contra] at s1
        simp only [replace_atom_all_rec] at s1
        sorry
  all_goals
    sorry


lemma is_proper_subformula_v2_imp_is_proper_subformula_v2_replace_atom_all_rec
  (F F' : Formula_)
  (σ : Instantiation)
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


example
  (F F' : Formula_)
  (σ : Instantiation)
  (h1 : is_proper_subformula_v2 F F') :
  ¬ is_unifier σ { (F, F') } :=
  by
  unfold is_unifier
  simp only [Set.mem_singleton_iff]
  intro contra
  apply is_proper_subformula_v2_imp_replace_atom_all_rec_not_eq F F' σ
  · exact h1
  · specialize contra (F, F')
    simp only at contra
    apply contra
    exact trivial
