import HandbookOfPracticalLogicLean.Chapter2.Replace
import HandbookOfPracticalLogicLean.Chapter2.Semantics

import HandbookOfPracticalLogicLean.Chapter2.NF.NF


import Mathlib.Tactic


set_option autoImplicit false


open Formula_


mutual
/--
  `to_nnf_v1 F` := The result of translating the formula `F` to a logically equivalent formula in negation normal form.
-/
def to_nnf_v1 :
  Formula_ → Formula_
  | not_ phi => to_nnf_neg_v1 phi
  | and_ phi psi => and_ (to_nnf_v1 phi) (to_nnf_v1 psi)
  | or_ phi psi => or_ (to_nnf_v1 phi) (to_nnf_v1 psi)
  | imp_ phi psi => or_ (to_nnf_neg_v1 phi) (to_nnf_v1 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v1 phi) (to_nnf_v1 psi)) (and_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi))
  | phi => phi

/--
  `to_nnf_neg_v1 F` := The result of translating the formula `not_ F` to a logically equivalent formula in negation normal form.
-/
def to_nnf_neg_v1 :
  Formula_ → Formula_
  | false_ => true_
  | true_ => false_
  | not_ phi => to_nnf_v1 phi
  | and_ phi psi => or_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi)
  | or_ phi psi => and_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi)
  | imp_ phi psi => and_ (to_nnf_v1 phi) (to_nnf_neg_v1 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v1 phi) (to_nnf_neg_v1 psi)) (and_ (to_nnf_neg_v1 phi) (to_nnf_v1 psi))
  | phi => not_ phi
end

#eval to_nnf_v1 false_
#eval to_nnf_v1 (not_ false_)
#eval to_nnf_v1 (not_ (not_ false_))
#eval to_nnf_v1 (not_ (not_ (not_ false_)))
#eval to_nnf_v1 (not_ (not_ (not_ (not_ false_))))


lemma eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V (to_nnf_neg_v1 F) = b_not (eval V (to_nnf_v1 F)) :=
  by
  induction F
  case false_ | true_ =>
    unfold to_nnf_v1
    unfold to_nnf_neg_v1
    unfold eval
    simp only [b_not]
  case atom_ X =>
    unfold to_nnf_v1
    unfold to_nnf_neg_v1
    simp only [eval]
  case not_ phi ih =>
    unfold to_nnf_v1
    simp only [to_nnf_neg_v1]
    rewrite [ih]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    simp only [to_nnf_neg_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto


lemma eval_eq_eval_to_nnf_v1
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = eval V (to_nnf_v1 F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v1
    rfl
  case not_ phi ih =>
    unfold to_nnf_v1
    simp only [eval]
    rewrite [ih]
    rewrite [eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1 V phi]
    rfl
  case and_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    unfold eval
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case or_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    unfold eval
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case imp_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    unfold eval
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1 V phi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1 V phi]
    rewrite [eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1 V psi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto


-------------------------------------------------------------------------------


lemma to_nnf_neg_v1_is_nnf_rec_v1_iff_to_nnf_v1_is_nnf_rec_v1
  (F : Formula_) :
  (to_nnf_neg_v1 F).is_nnf_rec_v1 ↔ (to_nnf_v1 F).is_nnf_rec_v1 :=
  by
  induction F
  case true_ | false_ | atom_ X =>
    unfold to_nnf_v1
    unfold to_nnf_neg_v1
    unfold is_nnf_rec_v1
    rfl
  case not_ phi ih =>
    unfold to_nnf_v1
    simp only [to_nnf_neg_v1]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    simp only [to_nnf_neg_v1]
    simp only [is_nnf_rec_v1]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


lemma to_nnf_v1_is_nnf_rec_v1
  (F : Formula_) :
  (to_nnf_v1 F).is_nnf_rec_v1 :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v1
    unfold is_nnf_rec_v1
    exact trivial
  case not_ phi ih =>
    unfold to_nnf_v1
    rewrite [to_nnf_neg_v1_is_nnf_rec_v1_iff_to_nnf_v1_is_nnf_rec_v1]
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    simp only [is_nnf_rec_v1]
    exact ⟨phi_ih, psi_ih⟩
  case imp_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    simp only [is_nnf_rec_v1]
    rewrite [to_nnf_neg_v1_is_nnf_rec_v1_iff_to_nnf_v1_is_nnf_rec_v1]
    exact ⟨phi_ih, psi_ih⟩
  case iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    simp only [is_nnf_rec_v1]
    simp only [to_nnf_neg_v1_is_nnf_rec_v1_iff_to_nnf_v1_is_nnf_rec_v1]
    exact ⟨⟨phi_ih, psi_ih⟩, ⟨phi_ih, psi_ih⟩⟩


-------------------------------------------------------------------------------


example
  (A A' : String)
  (F : Formula_)
  (h1 : is_nnf_rec_v1 F)
  (h2 : ¬ is_neg_literal_in_rec A F) :
  ∀ (V : ValuationAsTotalFunction), eval V (((atom_ A).imp_ (atom_ A')).imp_ (F.imp_ (replace_atom_one_rec A (atom_ A') F))) :=
  by
  intro V
  induction F
  case false_ | true_ =>
    unfold replace_atom_one_rec
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case atom_ X =>
    unfold replace_atom_one_rec
    simp only [eval]
    split_ifs
    case pos c1 =>
      rewrite [c1]
      unfold eval
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
      tauto
    case neg c1 =>
      unfold eval
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
      tauto
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      unfold is_neg_literal_in_rec at h2

      simp only [replace_atom_one_rec]
      split_ifs
      simp only [eval]
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
      tauto
    all_goals
      unfold is_nnf_rec_v1 at h1
      contradiction
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    unfold is_nnf_rec_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold is_neg_literal_in_rec at h2
    simp only [not_or] at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    simp only [eval] at phi_ih
    simp only [eval] at psi_ih

    simp only [replace_atom_one_rec]
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff] at *
    tauto
  all_goals
    unfold is_nnf_rec_v1 at h1
    contradiction


example
  (A A' : String)
  (F : Formula_)
  (h1 : is_nnf_rec_v1 F)
  (h2 : ¬ is_pos_literal_in_rec A F) :
  ∀ (V : ValuationAsTotalFunction), eval V (((atom_ A).imp_ (atom_ A')).imp_ ((replace_atom_one_rec A (atom_ A') F).imp_ F)) = true :=
  by
  intro V
  induction F
  case false_ | true_ =>
    unfold replace_atom_one_rec
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case atom_ X =>
    unfold is_pos_literal_in_rec at h2

    unfold replace_atom_one_rec
    split_ifs
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      simp only [replace_atom_one_rec]
      split_ifs
      case pos c1 =>
        simp only [eval]
        rewrite [c1]
        rewrite [Bool.eq_iff_iff]
        simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
        tauto
      case neg c1 =>
        simp only [eval]
        rewrite [Bool.eq_iff_iff]
        simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
        tauto
    all_goals
      unfold is_nnf_rec_v1 at h1
      contradiction
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    unfold is_nnf_rec_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold is_pos_literal_in_rec at h2
    simp only [not_or] at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    simp only [eval] at phi_ih
    simp only [eval] at psi_ih

    simp only [replace_atom_one_rec]
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff] at *
    tauto
  all_goals
    unfold is_nnf_rec_v1 at h1
    contradiction
