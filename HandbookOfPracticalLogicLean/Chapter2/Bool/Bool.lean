import Mathlib.Tactic


set_option autoImplicit false


namespace Prop_


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


lemma bool_iff_prop_not
  (b : Bool) :
  (b_not b = true) ↔ ¬ (b = true) :=
  by
  cases b
  all_goals
    simp only [b_not]
    tauto


lemma bool_iff_prop_and
  (b1 b2 : Bool) :
  (b_and b1 b2 = true) ↔ ((b1 = true) ∧ (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      simp only [b_and]
      tauto


lemma bool_iff_prop_or
  (b1 b2 : Bool) :
  (b_or b1 b2 = true) ↔ ((b1 = true) ∨ (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      simp only [b_or]
      tauto


lemma bool_iff_prop_imp
  (b1 b2 : Bool) :
  (b_imp b1 b2 = true) ↔ ((b1 = true) → (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      simp only [b_imp]
      tauto


lemma bool_iff_prop_iff
  (b1 b2 : Bool) :
  (b_iff b1 b2 = true) ↔ ((b1 = true) ↔ (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      simp only [b_iff]
    all_goals
      tauto


-------------------------------------------------------------------------------


lemma b_iff_rfl
  (b : Bool) :
  b_iff b b = true :=
  by
  cases b
  · simp only [b_iff]
  · simp only [b_iff]


lemma b_not_eq_false
  (b : Bool) :
  (b_not b = false ↔ b = true) :=
  by
  constructor
  · intro a1
    cases b
    · simp only [b_not] at a1
      cases a1
    · rfl
  · intro a1
    cases b
    · cases a1
    · simp only [b_not]


lemma b_not_eq_true
  (b : Bool) :
  (b_not b = true ↔ b = false) :=
  by
  constructor
  · intro a1
    cases b
    · rfl
    · simp only [b_not] at a1
      cases a1
  · intro a1
    cases b
    · simp only [b_not]
    · cases a1


lemma b_iff_eq_false
  (b1 b2 : Bool) :
  (b_iff b1 b2 = false) ↔ ¬ (b1 = b2) :=
  by
  constructor
  · intro a1
    cases b1
    · cases b2
      · simp only [b_iff] at a1
        cases a1
      · intro contra
        cases contra
    · cases b2
      · intro contra
        cases contra
      · simp only [b_iff] at a1
        cases a1
  · intro a1
    cases b1
    · cases b2
      · exfalso
        apply a1
        rfl
      · simp only [b_iff]
    · cases b2
      · simp only [b_iff]
      · exfalso
        apply a1
        rfl


lemma b_iff_eq_true
  (b1 b2 : Bool) :
  (b_iff b1 b2 = true) ↔ (b1 = b2) :=
  by
  constructor
  · intro a1
    cases b1
    · cases b2
      · rfl
      · simp only [b_iff] at a1
        cases a1
    · cases b2
      · simp only [b_iff] at a1
        cases a1
      · rfl
  · intro a1
    rewrite [a1]
    apply b_iff_rfl


#lint
