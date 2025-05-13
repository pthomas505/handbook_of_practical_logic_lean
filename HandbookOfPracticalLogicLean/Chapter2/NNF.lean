import HandbookOfPracticalLogicLean.Chapter2.NF
import HandbookOfPracticalLogicLean.Chapter2.Replace
import HandbookOfPracticalLogicLean.Chapter2.Semantics
import HandbookOfPracticalLogicLean.Chapter2.SubFormula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `negate_literal F` := The result of negating the formula `F` if `F` is a literal.
-/
def negate_literal :
  Formula_ → Formula_
  | atom_ X => not_ (atom_ X)
  | not_ (atom_ X) => atom_ X
  | phi => phi


lemma negate_literal_not_eq_self
  (F : Formula_)
  (h1 : is_literal F) :
  ¬ negate_literal F = F :=
  by
  cases F
  case atom_ X =>
    simp only [negate_literal]
    intro contra
    contradiction
  case not_ phi =>
    cases phi
    case atom_ X =>
      simp only [negate_literal]
      intro contra
      contradiction
    all_goals
      simp only [is_literal] at h1
  all_goals
    simp only [is_literal] at h1


lemma eval_negate_literal
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : F.is_literal) :
  eval V (negate_literal F) = b_not (eval V F) :=
  by
  cases F
  case atom_ X =>
    simp only [negate_literal]
    simp only [eval]
  case not_ phi =>
    cases phi
    case atom_ X =>
      simp only [negate_literal]
      simp only [eval]

      cases c1 : V X
      case false =>
        simp only [b_not]
      case true =>
        simp only [b_not]
    all_goals
      simp only [is_literal] at h1
  all_goals
    simp only [is_literal] at h1


-------------------------------------------------------------------------------


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


theorem eval_to_nnf_neg_v1_eq_not_eval_to_nnf_v1
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


lemma to_nnf_neg_v1_is_nnf_v1_iff_to_nnf_v1_is_nnf_v1
  (F : Formula_) :
  (to_nnf_neg_v1 F).is_nnf_v1 ↔ (to_nnf_v1 F).is_nnf_v1 :=
  by
  induction F
  case true_ | false_ | atom_ X =>
    unfold to_nnf_v1
    unfold to_nnf_neg_v1
    unfold is_nnf_v1
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
    simp only [is_nnf_v1]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


lemma to_nnf_v1_is_nnf_v1
  (F : Formula_) :
  (to_nnf_v1 F).is_nnf_v1 :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v1
    unfold is_nnf_v1
    exact trivial
  case not_ phi ih =>
    unfold to_nnf_v1
    rewrite [to_nnf_neg_v1_is_nnf_v1_iff_to_nnf_v1_is_nnf_v1]
    apply ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    simp only [is_nnf_v1]
    exact ⟨phi_ih, psi_ih⟩
  case imp_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    simp only [is_nnf_v1]
    rewrite [to_nnf_neg_v1_is_nnf_v1_iff_to_nnf_v1_is_nnf_v1]
    exact ⟨phi_ih, psi_ih⟩
  case iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v1
    simp only [is_nnf_v1]
    simp only [to_nnf_neg_v1_is_nnf_v1_iff_to_nnf_v1_is_nnf_v1]
    exact ⟨⟨phi_ih, psi_ih⟩, ⟨phi_ih, psi_ih⟩⟩


-------------------------------------------------------------------------------


mutual
/--
  `to_nnf_v2 F` := The result of translating the formula `F` to a logically equivalent formula in negation normal form.
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
  `to_nnf_neg_v2 F` := The result of translating the formula `not_ F` to a logically equivalent formula in negation normal form.
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


theorem eval_to_nnf_neg_v2_eq_not_eval_to_nnf_v2
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
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
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
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto


example
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
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    unfold to_nnf_v2
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_v2_eq_not_eval_to_nnf_v2 V phi]
    rewrite [eval_to_nnf_neg_v2_eq_not_eval_to_nnf_v2 V psi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto


lemma to_nnf_neg_v2_is_nnf_v1_iff_to_nnf_v2_is_nnf_v1
  (F : Formula_)
  (h1 : ¬ is_subformula false_ F)
  (h2 : ¬ is_subformula true_ F) :
  (to_nnf_neg_v2 F).is_nnf_v1 ↔ (to_nnf_v2 F).is_nnf_v1 :=
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
    simp only [is_nnf_v1]
  case not_ phi ih =>
    unfold is_subformula at h1
    unfold is_subformula at h2

    unfold to_nnf_v2
    simp only [to_nnf_neg_v2]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold is_subformula at h1
    unfold is_subformula at h2

    unfold to_nnf_v2
    simp only [to_nnf_neg_v2]
    simp only [is_nnf_v1]
    tauto


example
  (F : Formula_)
  (h2 : ¬ is_proper_subformula false_ F)
  (h3 : ¬ is_proper_subformula true_ F) :
  (to_nnf_v2 F).is_nnf_v1 :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    unfold is_nnf_v1
    exact trivial
  all_goals
    unfold is_proper_subformula at h2
    unfold is_subformula at h2

    unfold is_proper_subformula at h3
    unfold is_subformula at h3

    unfold to_nnf_v2
  case not_ phi ih =>
    rewrite [to_nnf_neg_v2_is_nnf_v1_iff_to_nnf_v2_is_nnf_v1]
    apply ih
    · unfold is_proper_subformula
      tauto
    · unfold is_proper_subformula
      tauto
    · tauto
    · tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    unfold is_proper_subformula at phi_ih
    unfold is_proper_subformula at psi_ih

    unfold is_nnf_v1
    tauto
  case imp_ phi psi phi_ih psi_ih =>
    unfold is_proper_subformula at phi_ih
    unfold is_proper_subformula at psi_ih

    unfold is_nnf_v1
    rewrite [to_nnf_neg_v2_is_nnf_v1_iff_to_nnf_v2_is_nnf_v1]
    all_goals
      tauto
  case iff_ phi psi phi_ih psi_ih =>
    unfold is_proper_subformula at phi_ih
    unfold is_proper_subformula at psi_ih

    simp only [is_nnf_v1]
    rewrite [to_nnf_neg_v2_is_nnf_v1_iff_to_nnf_v2_is_nnf_v1]
    rewrite [to_nnf_neg_v2_is_nnf_v1_iff_to_nnf_v2_is_nnf_v1]
    all_goals
      tauto


-------------------------------------------------------------------------------






-------------------------------------------------------------------------------




example
  (A A' : String)
  (F : Formula_)
  (h1 : F.is_nnf_v1)
  (h2 : ¬ is_neg_literal_in A F) :
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
      unfold is_neg_literal_in at h2

      simp only [replace_atom_one_rec]
      split_ifs
      simp only [eval]
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
      tauto
    all_goals
      unfold is_nnf_v1 at h1
      contradiction
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    unfold is_nnf_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold is_neg_literal_in at h2
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
    unfold is_nnf_v1 at h1
    contradiction


example
  (A A' : String)
  (F : Formula_)
  (h1 : F.is_nnf_v1)
  (h2 : ¬ is_pos_literal_in A F) :
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
    unfold is_pos_literal_in at h2

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
      unfold is_nnf_v1 at h1
      contradiction
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    unfold is_nnf_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold is_pos_literal_in at h2
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
    unfold is_nnf_v1 at h1
    contradiction


#lint
