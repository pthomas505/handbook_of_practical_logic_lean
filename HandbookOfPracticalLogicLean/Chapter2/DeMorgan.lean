import Mathlib.Tactic


set_option autoImplicit false


theorem de_morgan_prop_1
  (P Q : Prop) :
  (¬ (P ∧ Q)) ↔ ((¬ P) ∨ (¬ Q)) :=
  by
  constructor
  · intro a1
    by_cases c1 : P
    case pos =>
      right
      intro contra
      apply a1
      exact ⟨c1, contra⟩
    case neg =>
      left
      intro contra
      apply c1
      exact contra
  · intro a1 contra
    obtain ⟨contra_left, contra_right⟩ := contra
    cases a1
    case inl a1 =>
      apply a1
      exact contra_left
    case inr a1 =>
      apply a1
      exact contra_right


theorem de_morgan_prop_2
  (P Q : Prop) :
  (¬ (P ∨ Q)) ↔ ((¬ P) ∧ (¬ Q)) :=
  by
  constructor
  · intro a1
    constructor
    · intro contra
      apply a1
      left
      exact contra
    · intro contra
      apply a1
      right
      exact contra
  · intro a1 contra
    obtain ⟨a1_left, a1_right⟩ := a1
    cases contra
    case inl contra =>
      apply a1_left
      exact contra
    case inr contra =>
      apply a1_right
      exact contra


#lint
