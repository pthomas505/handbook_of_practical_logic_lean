import HandbookOfPracticalLogicLean.Chapter2.Semantics

import HandbookOfPracticalLogicLean.Chapter2.NF.NF


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
  (h1 : is_literal_rec F) :
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
      simp only [is_literal_rec] at h1
  all_goals
    simp only [is_literal_rec] at h1


lemma eval_negate_literal_eq_not_eval_literal
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : is_literal_rec F) :
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
      simp only [is_literal_rec] at h1
  all_goals
    simp only [is_literal_rec] at h1
