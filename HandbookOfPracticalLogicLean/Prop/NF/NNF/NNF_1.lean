import HandbookOfPracticalLogicLean.Prop.Replace.Var.One.Rec.Replace
import HandbookOfPracticalLogicLean.Prop.Semantics

import HandbookOfPracticalLogicLean.Prop.NF.NF


import Mathlib.Tactic


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


open Formula_


mutual
/--
  `to_nnf_v1 F` := Translates the formula `F` to a logically equivalent formula in negation normal form.
-/
@[nolint defsWithUnderscore]
def to_nnf_v1 :
  Formula_ → Formula_
  | not_ phi => to_nnf_neg_v1 phi
  | and_ phi psi => and_ (to_nnf_v1 phi) (to_nnf_v1 psi)
  | or_ phi psi => or_ (to_nnf_v1 phi) (to_nnf_v1 psi)
  | imp_ phi psi => or_ (to_nnf_neg_v1 phi) (to_nnf_v1 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v1 phi) (to_nnf_v1 psi)) (and_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi))
  | phi => phi

/--
  `to_nnf_neg_v1 F` := Translates the formula `not_ F` to a logically equivalent formula in negation normal form.
-/
@[nolint defsWithUnderscore]
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


theorem eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1
  (σ : ValuationAsTotalFunction)
  (F : Formula_) :
  eval σ (to_nnf_neg_v1 F) = b_not (eval σ (to_nnf_v1 F)) :=
  by
  induction F
  case false_ | true_ =>
    unfold to_nnf_v1
    unfold to_nnf_neg_v1
    unfold eval
    simp only [b_not]
  case var_ X =>
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
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or]
    tauto


theorem eval_eq_eval_to_nnf_v1
  (σ : ValuationAsTotalFunction)
  (F : Formula_) :
  eval σ F = eval σ (to_nnf_v1 F) :=
  by
  induction F
  case false_ | true_ | var_ X =>
    unfold to_nnf_v1
    apply Eq.refl
  case not_ phi ih =>
    unfold to_nnf_v1
    simp only [eval]
    rewrite [ih]
    rewrite [eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1 σ phi]
    apply Eq.refl
  case and_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    unfold eval
    rewrite [phi_ih]
    rewrite [psi_ih]
    apply Eq.refl
  case or_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    unfold eval
    rewrite [phi_ih]
    rewrite [psi_ih]
    apply Eq.refl
  case imp_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    unfold eval
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1 σ phi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_or, bool_iff_prop_imp]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1 σ phi]
    rewrite [eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1 σ psi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_iff]
    tauto


-------------------------------------------------------------------------------


theorem to_nnf_neg_v1_is_nnf_rec_v1_iff_to_nnf_v1_is_nnf_rec_v1
  (F : Formula_) :
  (to_nnf_neg_v1 F).is_nnf_rec_v1 ↔ (to_nnf_v1 F).is_nnf_rec_v1 :=
  by
  induction F
  case true_ | false_ | var_ X =>
    unfold to_nnf_v1
    unfold to_nnf_neg_v1
    unfold is_nnf_rec_v1
    apply Iff.refl
  case not_ phi ih =>
    unfold to_nnf_v1
    simp only [to_nnf_neg_v1]
    rewrite [ih]
    apply Iff.refl
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
    apply Iff.refl


theorem to_nnf_v1_is_nnf_rec_v1
  (F : Formula_) :
  (to_nnf_v1 F).is_nnf_rec_v1 :=
  by
  induction F
  case false_ | true_ | var_ X =>
    unfold to_nnf_v1
    unfold is_nnf_rec_v1
    exact True.intro
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
  (V V' : String)
  (F : Formula_)
  (h1 : is_nnf_rec_v1 F)
  (h2 : ¬ is_neg_literal_in_rec V F) :
  ∀ (σ : ValuationAsTotalFunction), eval σ (((var_ V).imp_ (var_ V')).imp_ (F.imp_ (replace_var_one_rec V (var_ V') F))) :=
  by
  intro σ
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_imp]
    tauto
  case var_ X =>
    unfold replace_var_one_rec
    simp only [eval]
    split
    case isTrue c1 =>
      rewrite [c1]
      unfold eval
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_imp]
      tauto
    case isFalse c1 =>
      unfold eval
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_imp]
      tauto
  case not_ phi ih =>
    cases phi
    case var_ X =>
      unfold is_neg_literal_in_rec at h2

      simp only [replace_var_one_rec]
      split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        simp only [eval]
        rewrite [Bool.eq_iff_iff]
        simp only [bool_iff_prop_not, bool_iff_prop_imp]
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
    simp only [bool_iff_prop_imp] at phi_ih

    simp only [eval] at psi_ih
    simp only [bool_iff_prop_imp] at psi_ih

    simp only [replace_var_one_rec]
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp]
    tauto
  all_goals
    unfold is_nnf_rec_v1 at h1
    contradiction


example
  (V V' : String)
  (F : Formula_)
  (h1 : is_nnf_rec_v1 F)
  (h2 : ¬ is_pos_literal_in_rec V F) :
  ∀ (σ : ValuationAsTotalFunction), eval σ (((var_ V).imp_ (var_ V')).imp_ ((replace_var_one_rec V (var_ V') F).imp_ F)) = true :=
  by
  intro σ
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_imp]
    tauto
  case var_ X =>
    unfold is_pos_literal_in_rec at h2

    unfold replace_var_one_rec
    split
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      simp only [eval]
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_imp]
      tauto
  case not_ phi ih =>
    cases phi
    case var_ X =>
      simp only [replace_var_one_rec]
      split
      case isTrue c1 =>
        simp only [eval]
        rewrite [c1]
        rewrite [Bool.eq_iff_iff]
        simp only [bool_iff_prop_not, bool_iff_prop_imp]
        tauto
      case isFalse c1 =>
        simp only [eval]
        rewrite [Bool.eq_iff_iff]
        simp only [bool_iff_prop_not, bool_iff_prop_imp]
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
    simp only [bool_iff_prop_imp] at phi_ih

    simp only [eval] at psi_ih
    simp only [bool_iff_prop_imp] at psi_ih

    simp only [replace_var_one_rec]
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp]
    tauto
  all_goals
    unfold is_nnf_rec_v1 at h1
    contradiction


#lint
