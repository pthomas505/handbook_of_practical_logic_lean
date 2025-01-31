import HandbookOfPracticalLogicLean.Chapter2.Semantics
import HandbookOfPracticalLogicLean.Chapter2.SubFormula

import Mathlib.Tactic


set_option autoImplicit false


namespace Prop_


open Formula_


def Formula_.is_literal :
  Formula_ → Prop
  | atom_ _ => True
  | not_ (atom_ _) => True
  | _ => False


def Formula_.is_negative_literal :
  Formula_ → Prop
  | not_ (atom_ _) => True
  | _ => False


def Formula_.is_positive_literal :
  Formula_ → Prop
  | atom_ _ => True
  | _ => False


def negate_literal :
  Formula_ → Formula_
  | atom_ X => not_ (atom_ X)
  | not_ (atom_ X) => atom_ X
  | phi => phi


def Formula_.is_nnf :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_nnf ∧ psi.is_nnf
  | or_ phi psi => phi.is_nnf ∧ psi.is_nnf
  | _ => False


-------------------------------------------------------------------------------


mutual
def to_nnf_v1 :
  Formula_ → Formula_
  | not_ phi => to_nnf_neg_v1 phi
  | and_ phi psi => and_ (to_nnf_v1 phi) (to_nnf_v1 psi)
  | or_ phi psi => or_ (to_nnf_v1 phi) (to_nnf_v1 psi)
  | imp_ phi psi => or_ (to_nnf_neg_v1 phi) (to_nnf_v1 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v1 phi) (to_nnf_v1 psi)) (and_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi))
  | phi => phi

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


theorem eval_to_nnf_neg_iff_not_eval_to_nnf_v1
  (V : Valuation)
  (F : Formula_) :
  eval V (to_nnf_neg_v1 F) ↔ ¬ eval V (to_nnf_v1 F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [eval]
    tauto
  case atom_ X =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [eval]
  case not_ phi ih =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    rewrite [ih]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    tauto


example
  (V : Valuation)
  (F : Formula_) :
  eval V F ↔ eval V (to_nnf_v1 F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v1
    rfl
  case not_ phi ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V phi]
    rfl
  case and_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case or_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case imp_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V phi]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V phi]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V psi]
    tauto


lemma to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1
  (F : Formula_) :
  (to_nnf_neg_v1 F).is_nnf ↔ (to_nnf_v1 F).is_nnf :=
  by
  induction F
  case true_ | false_ | atom_ X =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [is_nnf]
  case not_ phi ih =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [is_nnf]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


example
  (F : Formula_) :
  (to_nnf_v1 F).is_nnf :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v1
    unfold is_nnf
    exact trivial
  case not_ phi ih =>
    simp only [to_nnf_v1]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1]
    apply ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [is_nnf]
    tauto
  case imp_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [is_nnf]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [is_nnf]
    simp only [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1]
    tauto


-------------------------------------------------------------------------------


mutual
def to_nnf_v2 :
  Formula_ → Formula_
  | not_ phi => to_nnf_neg_v2 phi
  | and_ phi psi => and_ (to_nnf_v2 phi) (to_nnf_v2 psi)
  | or_ phi psi => or_ (to_nnf_v2 phi) (to_nnf_v2 psi)
  | imp_ phi psi => or_ (to_nnf_neg_v2 phi) (to_nnf_v2 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v2 phi) (to_nnf_v2 psi)) (and_ (to_nnf_neg_v2 phi) (to_nnf_neg_v2 psi))
  | phi => phi

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


theorem eval_to_nnf_neg_iff_not_eval_to_nnf_v2
  (V : Valuation)
  (F : Formula_) :
  eval V (to_nnf_neg_v2 F) ↔ ¬ eval V (to_nnf_v2 F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [eval]
  case atom_ X =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [eval]
  case not_ phi ih =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    rewrite [ih]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    tauto


example
  (V : Valuation)
  (F : Formula_) :
  eval V F ↔ eval V (to_nnf_v2 F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    rfl
  case not_ phi ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V phi]
    rfl
  case and_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case or_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case imp_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V phi]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V phi]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V psi]
    tauto


lemma to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2
  (F : Formula_)
  (h1 : ¬ is_subformula false_ F)
  (h2 : ¬ is_subformula true_ F) :
  (to_nnf_neg_v2 F).is_nnf ↔ (to_nnf_v2 F).is_nnf :=
  by
  induction F
  case false_ =>
    simp only [is_subformula] at h1
    contradiction
  case true_ =>
    simp only [is_subformula] at h2
    contradiction
  case atom_ X =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [is_nnf]
  case not_ phi ih =>
    simp only [is_subformula] at h1
    simp only [is_subformula] at h2

    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [is_subformula] at h1
    simp only [is_subformula] at h2

    simp only [is_nnf]
    tauto


example
  (F : Formula_)
  (h2 : ¬ is_proper_subformula false_ F)
  (h3 : ¬ is_proper_subformula true_ F) :
  (to_nnf_v2 F).is_nnf :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    unfold is_nnf
    exact trivial
  case not_ phi ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [to_nnf_v2]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    apply ih
    · simp only [is_proper_subformula]
      tauto
    · simp only [is_proper_subformula]
      tauto
    · tauto
    · tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [is_proper_subformula] at phi_ih
    simp only [is_proper_subformula] at psi_ih

    simp only [to_nnf_v2]
    simp only [is_nnf]
    tauto
  case imp_ phi psi phi_ih psi_ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [is_proper_subformula] at phi_ih
    simp only [is_proper_subformula] at psi_ih

    simp only [to_nnf_v2]
    simp only [is_nnf]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    all_goals
      tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [is_proper_subformula] at phi_ih
    simp only [is_proper_subformula] at psi_ih

    simp only [to_nnf_v2]
    simp only [is_nnf]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    all_goals
      tauto


-------------------------------------------------------------------------------
