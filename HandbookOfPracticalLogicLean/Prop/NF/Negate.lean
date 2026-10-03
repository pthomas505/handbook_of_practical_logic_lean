import HandbookOfPracticalLogicLean.Prop.Semantics

import HandbookOfPracticalLogicLean.Prop.NF.NF


import Mathlib.Tactic


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


open Formula_


/--
  `negate_literal F` := The result of negating the formula `F` if `F` is a literal.
-/
@[nolint defsWithUnderscore]
def negate_literal :
  Formula_ → Formula_
  | var_ X => not_ (var_ X)
  | not_ (var_ X) => var_ X
  | phi => phi


theorem negate_literal_not_eq_self
  (F : Formula_)
  (h1 : is_literal_rec F) :
  ¬ negate_literal F = F :=
  by
  cases F
  case var_ X =>
    simp only [negate_literal]
    intro contra
    contradiction
  case not_ phi =>
    cases phi
    case var_ X =>
      simp only [negate_literal]
      intro contra
      contradiction
    all_goals
      simp only [is_literal_rec] at h1
  all_goals
    simp only [is_literal_rec] at h1


theorem eval_negate_literal_eq_not_eval_literal
  (σ : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : is_literal_rec F) :
  eval σ (negate_literal F) = b_not (eval σ F) :=
  by
  cases F
  case var_ X =>
    simp only [negate_literal]
    simp only [eval]
  case not_ phi =>
    cases phi
    case var_ X =>
      simp only [negate_literal]
      simp only [eval]

      cases c1 : σ X
      case false =>
        simp only [b_not]
      case true =>
        simp only [b_not]
    all_goals
      simp only [is_literal_rec] at h1
  all_goals
    simp only [is_literal_rec] at h1


#lint
