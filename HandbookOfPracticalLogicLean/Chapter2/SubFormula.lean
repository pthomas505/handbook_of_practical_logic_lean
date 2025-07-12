import HandbookOfPracticalLogicLean.Chapter2.Size

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


example
  (F : Formula_) :
  size F = (subformula_list F).length :=
  by
  induction F
  all_goals
    unfold size
    unfold subformula_list
  case false_ | true_ | atom_ X =>
    simp only [List.length_singleton]
  case not_ phi ih =>
    simp only [List.singleton_append, List.length_cons]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [List.singleton_append, List.length_cons, List.length_append]
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


lemma is_subformula_imp_le_size
  (F F' : Formula_)
  (h1 : is_subformula F F') :
  F.size ≤ F'.size :=
  by
  induction F'
  case false_ | true_ | atom_ X =>
    unfold is_subformula at h1
    rewrite [h1]
    apply le_refl
  case not_ phi ih =>
    unfold is_subformula at h1

    cases h1
    case inl h1 =>
      rewrite [h1]
      apply le_refl
    case inr h1 =>
      trans phi.size
      apply ih
      · exact h1
      · simp only [size]
        apply Nat.le_add_right
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold is_subformula at h1

    cases h1
    case inl h1 =>
      rewrite [h1]
      apply le_refl
    case inr h1 =>
      cases h1
      case inl h1 =>
        trans phi.size
        · apply phi_ih
          exact h1
        · simp only [size]
          linarith
      case inr h1 =>
        trans psi.size
        · apply psi_ih
          exact h1
        · simp only [size]
          linarith


lemma is_subformula_size_antisymm
  (F F' : Formula_)
  (h1 : is_subformula F F')
  (h2 : is_subformula F' F) :
  F.size = F'.size :=
  by
  apply Nat.le_antisymm
  · apply is_subformula_imp_le_size
    exact h1
  · apply is_subformula_imp_le_size
    exact h2


lemma is_subformula_and_eq_size_imp_eq
  (F F' : Formula_)
  (h1 : is_subformula F F')
  (h2 : size F = size F') :
  F = F' :=
  by
  cases F'
  case false_ | true_ | atom_ X =>
    unfold is_subformula at h1
    exact h1
  case not_ phi =>
    simp only [is_subformula] at h1

    cases h1
    case inl h1 =>
      exact h1
    case inr h1 =>
      obtain s1 := is_subformula_imp_le_size F phi h1
      rewrite [h2] at s1
      simp only [size] at s1
      linarith
  case
      and_ phi psi
    | or_ phi psi
    | imp_ phi psi
    | iff_ phi psi =>
    simp only [is_subformula] at h1

    cases h1
    case inl h1 =>
      exact h1
    case inr h1 =>
      cases h1
      case inl h1 =>
        obtain s1 := is_subformula_imp_le_size F phi h1
        rewrite [h2] at s1
        simp only [size] at s1
        linarith
      case inr h1 =>
        obtain s1 := is_subformula_imp_le_size F psi h1
        rewrite [h2] at s1
        simp only [size] at s1
        linarith


lemma is_subformula_antisymm
  (F F' : Formula_)
  (h1 : is_subformula F F')
  (h2 : is_subformula F' F) :
  F = F' :=
  by
  apply is_subformula_and_eq_size_imp_eq
  · exact h1
  · apply is_subformula_size_antisymm
    · exact h1
    · exact h2


lemma not_is_subformula_not
  (F : Formula_) :
  ¬ is_subformula (not_ F) F :=
  by
  intro contra
  obtain s1 := is_subformula_imp_le_size (not_ F) F contra
  simp only [size] at s1
  linarith


lemma not_is_subformula_and_left
  (P Q : Formula_) :
  ¬ is_subformula (and_ P Q) P :=
  by
  intro contra
  obtain s1 := is_subformula_imp_le_size (and_ P Q) P contra
  simp only [size] at s1
  linarith


-------------------------------------------------------------------------------


/--
  `is_proper_subformula_v1 F F'` := True if and only if the formula `F` is a proper subformula of the formula `F'`.
-/
def is_proper_subformula_v1
  (F : Formula_) :
  Formula_ → Prop
  | false_ => False
  | true_ => False
  | atom_ _ => False
  | not_ phi =>
    is_subformula F phi
  | and_ phi psi =>
    is_subformula F phi ∨
    is_subformula F psi
  | or_ phi psi =>
    is_subformula F phi ∨
    is_subformula F psi
  | imp_ phi psi =>
    is_subformula F phi ∨
    is_subformula F psi
  | iff_ phi psi =>
    is_subformula F phi ∨
    is_subformula F psi

instance
  (F F' : Formula_) :
  Decidable (is_proper_subformula_v1 F F') :=
  by
  induction F'
  all_goals
    simp only [is_proper_subformula_v1]
    infer_instance


/--
  `is_proper_subformula_v2 F F'` := True if and only if the formula `F` is a proper subformula of the formula `F'`.
-/
def is_proper_subformula_v2
  (F F' : Formula_) :
  Prop :=
  is_subformula F F' ∧ ¬ F = F'

instance
  (F F' : Formula_) :
  Decidable (is_proper_subformula_v2 F F') :=
  by
  unfold is_proper_subformula_v2
  infer_instance


example
  (F F' : Formula_)
  (h1 : ¬ is_subformula F F') :
  ¬ is_proper_subformula_v2 F F' :=
  by
  unfold is_proper_subformula_v2
  intro contra
  obtain ⟨contra_left, contra_right⟩ := contra
  apply h1
  exact contra_left


lemma is_proper_subformula_v1_imp_is_subformula
  (F F' : Formula_)
  (h1 : is_proper_subformula_v1 F F') :
  is_subformula F F' :=
  by
  cases F'
  case false_ | true_ | atom_ X =>
    simp only [is_proper_subformula_v1] at h1
  case not_ phi =>
    simp only [is_proper_subformula_v1] at h1

    unfold is_subformula
    right
    exact h1
  case
      and_ phi psi
    | or_ phi psi
    | imp_ phi psi
    | iff_ phi psi =>
    simp only [is_proper_subformula_v1] at h1

    unfold is_subformula
    cases h1
    case inl h1 =>
      right
      left
      exact h1
    case inr h1 =>
      right
      right
      exact h1


lemma is_proper_subformula_v1_imp_lt_size
  (F F' : Formula_)
  (h1 : is_proper_subformula_v1 F F') :
  F.size < F'.size :=
  by
  cases F'
  case false_ | true_ | atom_ X =>
    simp only [is_proper_subformula_v1] at h1
  case not_ phi =>
    simp only [is_proper_subformula_v1] at h1

    obtain s1 := is_subformula_imp_le_size F phi h1
    apply lt_of_le_of_lt s1
    simp only [size]
    apply lt_add_one
  case
      and_ phi psi
    | or_ phi psi
    | imp_ phi psi
    | iff_ phi psi =>
    simp only [is_proper_subformula_v1] at h1

    cases h1
    case inl h1 =>
      obtain s1 := is_subformula_imp_le_size F phi h1
      apply lt_of_le_of_lt s1
      simp only [size]
      linarith
    case inr h1 =>
      obtain s1 := is_subformula_imp_le_size F psi h1
      apply lt_of_le_of_lt s1
      simp only [size]
      linarith


lemma not_is_proper_subformula_v1_self
  (F : Formula_) :
  ¬ is_proper_subformula_v1 F F :=
  by
  intro contra
  obtain s1 := is_proper_subformula_v1_imp_lt_size F F contra
  simp only [lt_self_iff_false] at s1


lemma is_proper_subformula_v1_imp_neq
  (F F' : Formula_)
  (h1 : is_proper_subformula_v1 F F') :
  ¬ F = F' :=
  by
  intro contra
  rewrite [contra] at h1
  apply not_is_proper_subformula_v1_self F'
  exact h1


lemma is_proper_subformula_v1_imp_is_proper_subformula_v2
  (F F' : Formula_)
  (h1 : is_proper_subformula_v1 F F') :
  is_proper_subformula_v2 F F' :=
  by
  unfold is_proper_subformula_v2
  constructor
  · apply is_proper_subformula_v1_imp_is_subformula
    exact h1
  · apply is_proper_subformula_v1_imp_neq
    exact h1


lemma is_proper_subformula_v2_imp_is_proper_subformula_v1
  (F F' : Formula_)
  (h1 : is_proper_subformula_v2 F F') :
  is_proper_subformula_v1 F F' :=
  by
  cases F'
  case false_ | true_ | atom_ X =>
    unfold is_proper_subformula_v2 at h1
    unfold is_subformula at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    contradiction
  all_goals
    unfold is_proper_subformula_v2 at h1
    unfold is_subformula at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [is_proper_subformula_v1]
    cases h1_left
    case inl h1_left =>
      contradiction
    case inr h1_left =>
      exact h1_left


lemma is_proper_subformula_v1_iff_is_proper_subformula_v2
  (F F' : Formula_) :
  is_proper_subformula_v1 F F' ↔ is_proper_subformula_v2 F F' :=
  by
  constructor
  · apply is_proper_subformula_v1_imp_is_proper_subformula_v2
  · apply is_proper_subformula_v2_imp_is_proper_subformula_v1


-------------------------------------------------------------------------------


lemma is_proper_subformula_v2_left_right_imp_not_is_subformula_right_left
  (F F' : Formula_)
  (h1 : is_proper_subformula_v2 F F') :
  ¬ is_subformula F' F :=
  by
  unfold is_proper_subformula_v2 at h1
  obtain ⟨h1_left, h1_right⟩ := h1
  intro contra
  apply h1_right
  apply is_subformula_antisymm
  · exact h1_left
  · exact contra


-------------------------------------------------------------------------------


example
  (F F' F'' : Formula_)
  (h1 : is_subformula F F')
  (h2 : is_proper_subformula_v2 F' F'') :
  is_proper_subformula_v2 F F'' :=
  by
  unfold is_proper_subformula_v2 at h2
  obtain ⟨h2_left, h2_right⟩ := h2

  unfold is_proper_subformula_v2
  constructor
  · apply is_subformula_trans F F'
    · exact h1
    · exact h2_left
  · intro contra
    rewrite [contra] at h1
    apply h2_right
    apply is_subformula_antisymm
    · exact h2_left
    · exact h1


example
  (F F' F'' : Formula_)
  (h1 : is_proper_subformula_v2 F F')
  (h2 : is_subformula F' F'') :
  is_proper_subformula_v2 F F'' :=
  by
  unfold is_proper_subformula_v2 at h1
  obtain ⟨h1_left, h1_right⟩ := h1

  unfold is_proper_subformula_v2
  constructor
  · apply is_subformula_trans F F'
    · exact h1_left
    · exact h2
  · intro contra
    rewrite [← contra] at h2
    apply h1_right
    apply is_subformula_antisymm
    · exact h1_left
    · exact h2


#lint
