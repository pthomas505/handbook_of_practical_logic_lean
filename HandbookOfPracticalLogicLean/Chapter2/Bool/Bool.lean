import Mathlib.Tactic


set_option autoImplicit false


namespace Bool_


/--
  The truth table definition of boolean `not`.
-/
def b_not : Bool → Bool
| false => true
| true => false

/--
  The truth table definition of boolean `and`.
-/
def b_and : Bool → Bool → Bool
| false, false => false
| false, true => false
| true, false => false
| true, true => true

/--
  The truth table definition of boolean `or`.
-/
def b_or : Bool → Bool → Bool
| false, false => false
| false, true => true
| true, false => true
| true, true => true

/--
  The truth table definition of boolean `imp`.
-/
def b_imp : Bool → Bool → Bool
| false, false => true
| false, true => true
| true, false => false
| true, true => true

/--
  The truth table definition of boolean `iff`.
-/
def b_iff : Bool → Bool → Bool
| false, false => true
| false, true => false
| true, false => false
| true, true => true


-------------------------------------------------------------------------------


lemma bool_iff_prop_not
  (b : Bool) :
  (b_not b = true) ↔ ¬ (b = true) :=
  by
  cases b
  all_goals
    unfold b_not
    dsimp only
    decide


lemma bool_iff_prop_and
  (b1 b2 : Bool) :
  (b_and b1 b2 = true) ↔ ((b1 = true) ∧ (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      unfold b_and
      dsimp only
      decide


lemma bool_iff_prop_or
  (b1 b2 : Bool) :
  (b_or b1 b2 = true) ↔ ((b1 = true) ∨ (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      unfold b_or
      dsimp only
      decide


lemma bool_iff_prop_imp
  (b1 b2 : Bool) :
  (b_imp b1 b2 = true) ↔ ((b1 = true) → (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      unfold b_imp
      dsimp only
      decide


lemma bool_iff_prop_iff
  (b1 b2 : Bool) :
  (b_iff b1 b2 = true) ↔ ((b1 = true) ↔ (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      unfold b_iff
      dsimp only
    all_goals
      decide


-------------------------------------------------------------------------------


lemma b_iff_rfl
  (b : Bool) :
  b_iff b b = true :=
  by
  cases b
  · unfold b_iff
    dsimp only
  · unfold b_iff
    dsimp only


lemma b_not_eq_false
  (b : Bool) :
  (b_not b = false ↔ b = true) :=
  by
  constructor
  · intro a1
    cases b
    · unfold b_not at a1
      dsimp at a1
      contradiction
    · rfl
  · intro a1
    cases b
    · contradiction
    · unfold b_not
      dsimp only


lemma b_not_eq_true
  (b : Bool) :
  (b_not b = true ↔ b = false) :=
  by
  constructor
  · intro a1
    cases b
    · rfl
    · unfold b_not at a1
      dsimp only at a1
      contradiction
  · intro a1
    cases b
    · unfold b_not
      dsimp only
    · contradiction


lemma b_iff_eq_false
  (b1 b2 : Bool) :
  (b_iff b1 b2 = false) ↔ ¬ (b1 = b2) :=
  by
  constructor
  · intro a1
    cases b1
    · cases b2
      · unfold b_iff at a1
        dsimp only at a1
        contradiction
      · intro contra
        contradiction
    · cases b2
      · intro contra
        contradiction
      · unfold b_iff at a1
        dsimp only at a1
        contradiction
  · intro a1
    cases b1
    · cases b2
      · contradiction
      · unfold b_iff
        dsimp only
    · cases b2
      · unfold b_iff
        dsimp only
      · contradiction


lemma b_iff_eq_true
  (b1 b2 : Bool) :
  (b_iff b1 b2 = true) ↔ (b1 = b2) :=
  by
  constructor
  · intro a1
    cases b1
    · cases b2
      · rfl
      · unfold b_iff at a1
        dsimp only at a1
        contradiction
    · cases b2
      · unfold b_iff at a1
        dsimp only at a1
        contradiction
      · rfl
  · intro a1
    rewrite [a1]
    apply b_iff_rfl


-------------------------------------------------------------------------------


example
  (b : Bool)
  (h1 : ¬ b = true) :
  b = false :=
  by
  cases b
  · rfl
  · contradiction


example
  (b : Bool)
  (h1 : ¬ b = false) :
  b = true :=
  by
  cases b
  · contradiction
  · rfl


#lint
