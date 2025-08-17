import HandbookOfPracticalLogicLean.Chapter2.Semantics
import HandbookOfPracticalLogicLean.Chapter2.SubFormula

import HandbookOfPracticalLogicLean.Chapter2.NF.NF


import Mathlib.Tactic


set_option autoImplicit false


open Formula_


mutual
/--
  `to_nnf_v2 F` := Translates the formula `F` to a logically equivalent formula in negation normal form.
-/
def to_nnf_v2 :
  Formula_ → Formula_
  | not_ phi => to_nnf_neg_v2 phi
  | and_ phi psi => and_ (to_nnf_v2 phi) (to_nnf_v2 psi)
  | or_ phi psi => or_ (to_nnf_v2 phi) (to_nnf_v2 psi)
  | imp_ phi psi => or_ (to_nnf_neg_v2 phi) (to_nnf_v2 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v2 phi) (to_nnf_v2 psi)) (and_ (to_nnf_neg_v2 phi) (to_nnf_neg_v2 psi))
  | phi => phi

/--
  `to_nnf_neg_v2 F` := Translates the formula `not_ F` to a logically equivalent formula in negation normal form.
-/
def to_nnf_neg_v2 :
  Formula_ → Formula_
  | not_ phi => to_nnf_v2 phi
  | and_ phi psi => or_ (to_nnf_neg_v2 phi) (to_nnf_neg_v2 psi)
  | or_ phi psi => and_ (to_nnf_neg_v2 phi) (to_nnf_neg_v2 psi)
  | imp_ phi psi => and_ (to_nnf_v2 phi) (to_nnf_neg_v2 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v2 phi) (to_nnf_neg_v2 psi)) (and_ (to_nnf_neg_v2 phi) (to_nnf_v2 psi))
  | phi => not_ phi
end

#eval to_nnf_v2 false_
#eval to_nnf_v2 (not_ false_)
#eval to_nnf_v2 (not_ (not_ false_))
#eval to_nnf_v2 (not_ (not_ (not_ false_)))
#eval to_nnf_v2 (not_ (not_ (not_ (not_ false_))))


lemma eval_to_nnf_neg_v2_eq_not_eval_to_nnf_v2
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V (to_nnf_neg_v2 F) = b_not (eval V (to_nnf_v2 F)) :=
  by
  induction F
  case false_ | true_ =>
    unfold to_nnf_v2
    unfold to_nnf_neg_v2
    simp only [eval]
  case atom_ X =>
    unfold to_nnf_v2
    unfold to_nnf_neg_v2
    simp only [eval]
  case not_ phi ih =>
    unfold to_nnf_v2
    simp only [to_nnf_neg_v2]
    rewrite [ih]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v2
    simp only [to_nnf_neg_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or]
    tauto


lemma eval_eq_eval_to_nnf_v2
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = eval V (to_nnf_v2 F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    rfl
  case not_ phi ih =>
    unfold to_nnf_v2
    simp only [eval]
    rewrite [ih]
    rewrite [eval_to_nnf_neg_v2_eq_not_eval_to_nnf_v2 V phi]
    rfl
  case and_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v2
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case or_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v2
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case imp_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v2
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_v2_eq_not_eval_to_nnf_v2 V phi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_or, bool_iff_prop_imp]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v2
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_v2_eq_not_eval_to_nnf_v2 V phi]
    rewrite [eval_to_nnf_neg_v2_eq_not_eval_to_nnf_v2 V psi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_iff]
    tauto


-------------------------------------------------------------------------------


lemma to_nnf_neg_v2_is_nnf_rec_v2_iff_to_nnf_v2_is_nnf_rec_v2
  (F : Formula_) :
  (to_nnf_neg_v2 F).is_nnf_rec_v2 ↔ (to_nnf_v2 F).is_nnf_rec_v2 :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    unfold to_nnf_neg_v2
    unfold is_nnf_rec_v2
    rfl
  case not_ phi ih =>
    unfold to_nnf_v2
    simp only [to_nnf_neg_v2]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v2
    simp only [to_nnf_neg_v2]
    simp only [is_nnf_rec_v2]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


lemma to_nnf_v2_is_nnf_rec_v2
  (F : Formula_) :
  is_nnf_rec_v2 (to_nnf_v2 F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    unfold is_nnf_rec_v2
    exact trivial
  case not_ phi ih =>
    unfold to_nnf_v2
    simp only [to_nnf_neg_v2_is_nnf_rec_v2_iff_to_nnf_v2_is_nnf_rec_v2]
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v2
    simp only [is_nnf_rec_v2]
    exact ⟨phi_ih, psi_ih⟩
  case imp_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v2
    unfold is_nnf_rec_v2
    simp only [to_nnf_neg_v2_is_nnf_rec_v2_iff_to_nnf_v2_is_nnf_rec_v2]
    exact ⟨phi_ih, psi_ih⟩
  case iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v2
    simp only [is_nnf_rec_v2]
    simp only [to_nnf_neg_v2_is_nnf_rec_v2_iff_to_nnf_v2_is_nnf_rec_v2]
    exact ⟨⟨phi_ih, psi_ih⟩, ⟨phi_ih, psi_ih⟩⟩


-------------------------------------------------------------------------------


lemma to_nnf_neg_v2_is_nnf_rec_v1_iff_to_nnf_v2_is_nnf_rec_v1
  (F : Formula_)
  (h1 : ¬ is_subformula false_ F)
  (h2 : ¬ is_subformula true_ F) :
  (to_nnf_neg_v2 F).is_nnf_rec_v1 ↔ (to_nnf_v2 F).is_nnf_rec_v1 :=
  by
  induction F
  case false_ =>
    unfold is_subformula at h1
    contradiction
  case true_ =>
    unfold is_subformula at h2
    contradiction
  case atom_ X =>
    unfold to_nnf_v2
    simp only [to_nnf_neg_v2]
    simp only [is_nnf_rec_v1]
  case not_ phi ih =>
    unfold is_subformula at h1
    simp only [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold is_subformula at h2
    simp only [not_or] at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    unfold to_nnf_v2
    simp only [to_nnf_neg_v2]
    rewrite [ih h1_right h2_right]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold is_subformula at h1
    simp only [not_or] at h1
    obtain ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩ := h1

    unfold is_subformula at h2
    simp only [not_or] at h2
    obtain ⟨h2_left, ⟨h2_right_left, h2_right_right⟩⟩ := h2

    unfold to_nnf_v2
    simp only [to_nnf_neg_v2]
    simp only [is_nnf_rec_v1]
    rewrite [phi_ih h1_right_left h2_right_left]
    rewrite [psi_ih h1_right_right h2_right_right]
    rfl


lemma to_nnf_v2_is_nnf_rec_v1
  (F : Formula_)
  (h1 : ¬ is_proper_subformula_v2 false_ F)
  (h2 : ¬ is_proper_subformula_v2 true_ F) :
  (to_nnf_v2 F).is_nnf_rec_v1 :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    unfold is_nnf_rec_v1
    exact trivial
  all_goals
    unfold is_proper_subformula_v2 at h1
    unfold is_subformula at h1

    unfold is_proper_subformula_v2 at h2
    unfold is_subformula at h2

    unfold to_nnf_v2
  case not_ phi ih =>
    rewrite [to_nnf_neg_v2_is_nnf_rec_v1_iff_to_nnf_v2_is_nnf_rec_v1]
    apply ih
    · unfold is_proper_subformula_v2
      tauto
    · unfold is_proper_subformula_v2
      tauto
    · tauto
    · tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    unfold is_proper_subformula_v2 at phi_ih
    unfold is_proper_subformula_v2 at psi_ih

    unfold is_nnf_rec_v1
    tauto
  case imp_ phi psi phi_ih psi_ih =>
    unfold is_proper_subformula_v2 at phi_ih
    unfold is_proper_subformula_v2 at psi_ih

    unfold is_nnf_rec_v1
    rewrite [to_nnf_neg_v2_is_nnf_rec_v1_iff_to_nnf_v2_is_nnf_rec_v1]
    all_goals
      tauto
  case iff_ phi psi phi_ih psi_ih =>
    unfold is_proper_subformula_v2 at phi_ih
    unfold is_proper_subformula_v2 at psi_ih

    simp only [is_nnf_rec_v1]
    rewrite [to_nnf_neg_v2_is_nnf_rec_v1_iff_to_nnf_v2_is_nnf_rec_v1]
    rewrite [to_nnf_neg_v2_is_nnf_rec_v1_iff_to_nnf_v2_is_nnf_rec_v1]
    all_goals
      tauto


#lint
