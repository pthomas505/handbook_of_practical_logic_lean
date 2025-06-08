import HandbookOfPracticalLogicLean.Chapter2.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `Formula_.subformula_list F` := A list of all of the subformulas of the formula `F`.
-/
def Formula_.subformula_list :
  Formula_ → List Formula_
  | false_ => [false_]
  | true_ => [true_]
  | atom_ X => [atom_ X]
  | not_ phi => [not_ phi] ++ phi.subformula_list
  | and_ phi psi => [and_ phi psi] ++ (phi.subformula_list ++ psi.subformula_list)
  | or_ phi psi => [or_ phi psi] ++ (phi.subformula_list ++ psi.subformula_list)
  | imp_ phi psi => [imp_ phi psi] ++ (phi.subformula_list ++ psi.subformula_list)
  | iff_ phi psi => [iff_ phi psi] ++ (phi.subformula_list ++ psi.subformula_list)


/--
  `is_subformula F F'` := True if and only if `F` is a subformula of the formula `F'`.
-/
def is_subformula
  (F : Formula_) :
  Formula_ → Prop
  | false_ => F = false_
  | true_ => F = true_
  | atom_ X => F = atom_ X
  | not_ phi =>
    F = not_ phi ∨
    is_subformula F phi
  | and_ phi psi =>
    F = and_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi
  | or_ phi psi =>
    F = or_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi
  | imp_ phi psi =>
    F = imp_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi
  | iff_ phi psi =>
    F = iff_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi

instance
  (F F' : Formula_) :
  Decidable (is_subformula F F') :=
  by
  induction F'
  all_goals
    unfold is_subformula
    infer_instance


lemma is_subformula_iff_mem_subformula_list
  (F F' : Formula_) :
  is_subformula F F' ↔ F ∈ subformula_list F' :=
  by
  induction F'
  all_goals
    unfold is_subformula
    unfold subformula_list
  case false_ | true_ | atom_ X =>
    simp only [List.mem_singleton]
  case not_ phi ih =>
    simp only [List.singleton_append, List.mem_cons]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [List.mem_append, List.mem_singleton]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


lemma is_subformula_refl
  (F : Formula_) :
  is_subformula F F :=
  by
  cases F
  case false_ | true_ | atom_ X =>
    unfold is_subformula
    rfl
  all_goals
    unfold is_subformula
    left
    rfl


lemma is_subformula_trans
  (F F' F'' : Formula_)
  (h1 : is_subformula F F')
  (h2 : is_subformula F' F'') :
  is_subformula F F'' :=
  by
  induction F''
  case false_ | true_ | atom_ X =>
    unfold is_subformula at h2
    rewrite [← h2]
    exact h1
  case not_ phi ih =>
    unfold is_subformula at h2

    cases h2
    case inl h2 =>
      rewrite [← h2]
      exact h1
    case inr h2 =>
      unfold is_subformula
      right
      apply ih
      exact h2
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold is_subformula at h2

    cases h2
    case inl h2 =>
      rewrite [← h2]
      exact h1
    case inr h2 =>
      unfold is_subformula
      right
      cases h2
      case inl h2 =>
        left
        apply phi_ih
        exact h2
      case inr h2 =>
        right
        apply psi_ih
        exact h2


/--
  `is_proper_subformula F F'` := True if and only if `F` is a proper subformula of the formula `F'`.
-/
def is_proper_subformula
  (F F' : Formula_) :
  Prop :=
  is_subformula F F' ∧ ¬ F = F'

instance
  (F F' : Formula_) :
  Decidable (is_proper_subformula F F') :=
  by
  unfold is_proper_subformula
  infer_instance


example
  (F F' : Formula_)
  (h1 : ¬ is_subformula F F') :
  ¬ is_proper_subformula F F' :=
  by
  unfold is_proper_subformula
  intro contra
  obtain ⟨contra_left, contra_right⟩ := contra
  apply h1
  exact contra_left


#lint
