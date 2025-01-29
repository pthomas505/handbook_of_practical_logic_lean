import HandbookOfPracticalLogicLean.Chapter2.Semantics
import HandbookOfPracticalLogicLean.Chapter2.SubFormula

import Mathlib.Tactic


set_option autoImplicit false


namespace Prop_


open Formula_


def simplify_aux :
  Formula_ → Formula_
  | not_ false_ => true_
  | not_ true_ => false_
  | not_ (not_ phi) => phi
  | and_ _ false_ => false_
  | and_ false_ _ => false_
  | and_ phi true_ => phi
  | and_ true_ phi => phi
  | or_ phi false_ => phi
  | or_ false_ phi => phi
  | or_ _ true_ => true_
  | or_ true_ _ => true_
  | imp_ false_ _ => true_
  | imp_ _ true_ => true_
  | imp_ true_ phi => phi
  | imp_ phi false_ => not_ phi
  | iff_ phi true_ => phi
  | iff_ true_ phi => phi
  | iff_ phi false_ => not_ phi
  | iff_ false_ phi => not_ phi
  | phi => phi


def simplify_aux_and :
  Formula_ → Formula_
  | and_ _ false_ => false_
  | and_ false_ _ => false_
  | and_ phi true_ => phi
  | and_ true_ phi => phi
  | phi => phi


example
  (F : Formula_) :
  simplify_aux_and (and_ F false_) = false_ :=
  by
  simp only [simplify_aux_and]


example
  (F : Formula_) :
  simplify_aux_and (and_ false_ F) = false_ :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi h1 =>
    rfl
  case _ phi psi h1 h2 =>
    rfl
  case _ phi psi h1 h2 =>
    cases h2
    rfl
  case _ phi psi h1 h2 h3 =>
    cases h3
  · tauto


example
  (F : Formula_) :
  simplify_aux_and (and_ true_ F) = F :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi h1 =>
    cases h1
    rfl
  case _ phi psi h1 h2 =>
    cases h2
  case _ phi psi h1 h2 =>
    cases h2
    rfl
  case _ phi psi h1 h2 h3 =>
    cases h3
    rfl
  · tauto


example
  (F : Formula_) :
  simplify_aux_and (and_ F true_) = F :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi h1 =>
    cases h1
  case _ phi psi h1 h2 =>
    cases h2
    rfl
  case _ phi psi h1 h2 =>
    cases h2
    rfl
  case _ phi psi h1 h2 h3 =>
    cases h3
    rfl
  · tauto


example
  (P Q : Formula_)
  (h1 : ¬ P = false_)
  (h2 : ¬ P = true_)
  (h3 : ¬ Q = false_)
  (h4 : ¬ Q = true_) :
  simplify_aux_and (and_ P Q) = and_ P Q :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi ih_1 =>
    cases ih_1
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    contradiction
  · tauto


lemma simplify_aux_is_logically_equivalent
  (V : Valuation)
  (F : Formula_) :
  eval V F ↔ eval V (simplify_aux F) :=
  by
  cases F
  case false_ | true_ | atom_ X =>
    simp only [simplify_aux]
  case not_ phi =>
    cases phi
    all_goals
      simp only [simplify_aux]
    all_goals
      simp only [eval]
      tauto
  case
      and_ phi psi
    | or_ phi psi
    | imp_ phi psi
    | iff_ phi psi =>
    cases phi
    all_goals
      cases psi
      all_goals
        simp only [simplify_aux]
      all_goals
        simp only [eval]
      all_goals
        tauto


def simplify :
  Formula_ → Formula_
  | not_ phi => simplify_aux (not_ (simplify phi))
  | and_ phi psi => simplify_aux (and_ (simplify phi) (simplify psi))
  | or_ phi psi => simplify_aux (or_ (simplify phi) (simplify psi))
  | imp_ phi psi => simplify_aux (imp_ (simplify phi) (simplify psi))
  | iff_ phi psi => simplify_aux (iff_ (simplify phi) (simplify psi))
  | phi => phi


lemma simplify_is_logically_equivalent
  (V : Valuation)
  (F : Formula_) :
  eval V F ↔ eval V (simplify F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    rfl
  case not_ phi ih =>
    simp only [simplify]
    rewrite [← simplify_aux_is_logically_equivalent]
    simp only [eval]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [simplify]
    rewrite [← simplify_aux_is_logically_equivalent]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


example
  (F : Formula_) :
  are_logically_equivalent F (simplify F) :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  intro V
  unfold satisfies
  unfold eval
  apply simplify_is_logically_equivalent


example
  (F : Formula_) :
  ¬ is_proper_subformula false_ (simplify F) ∧
  ¬ is_proper_subformula true_ (simplify F) :=
  by
  induction F
  case and_ phi psi phi_ih psi_ih =>
    simp only [simplify]
    simp only [is_proper_subformula] at phi_ih

    have s1 : simplify phi = true_ ∨ ¬ is_subformula true_ (simplify phi) :=
    by
      tauto

    have s2 : simplify phi = false_ ∨ ¬ is_subformula false_ (simplify phi) :=
    by
      tauto

    clear phi_ih

    simp only [is_proper_subformula] at psi_ih

    have s3 : simplify psi = true_ ∨ ¬ is_subformula true_ (simplify psi) :=
    by
      tauto

    have s4 : simplify psi = false_ ∨ ¬ is_subformula false_ (simplify psi) :=
    by
      tauto

    clear psi_ih

    constructor
    · cases s1
      case _ s1 =>
        cases s2
        case _ s2 =>
          rewrite [s1] at s2
          contradiction
        case _ s2 =>
          rewrite [s1]
          cases s3
          case _ s3 =>
            rewrite [s3]
            simp only [simplify_aux]
            simp only [is_proper_subformula]
            simp only [is_subformula]
            tauto
          case _ s3 =>
            cases s4
            case _ s4 =>
              rewrite [s4]
              simp only [simplify_aux]
              simp only [is_proper_subformula]
              simp only [is_subformula]
              tauto
            case _ s4 =>
              have s5 : ¬ simplify psi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s3

              have s6 : ¬ simplify psi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s4

              simp only [simplify_aux]
              simp only [is_proper_subformula]
              tauto
      case _ s1 =>
        cases s2
        case _ s2 =>
          rewrite [s2]
          cases s3
          case _ s3 =>
            rewrite [s3]
            simp only [simplify_aux]
            simp only [is_proper_subformula]
            tauto
          case _ s3 =>
            cases s4
            case _ s4 =>
              rewrite [s4]
              simp only [simplify_aux]
              simp only [is_proper_subformula]
              tauto
            case _ s4 =>
              have s5 : ¬ simplify psi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s3

              have s6 : ¬ simplify psi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s4

              simp only [simplify_aux]
              simp only [is_proper_subformula]
              tauto
        case _ s2 =>
          cases s3
          case _ s3 =>
            rewrite [s3]
            cases s4
            case _ s4 =>
              rewrite [s3] at s4
              contradiction
            case _ s4 =>
              have s5 : ¬ simplify phi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s1

              have s6 : ¬ simplify phi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s2

              simp only [simplify_aux]
              simp only [is_proper_subformula]
              tauto
          case _ s3 =>
            cases s4
            case _ s4 =>
              rewrite [s4]

              have s5 : ¬ simplify phi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s1

              have s6 : ¬ simplify phi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s2

              simp only [simplify_aux]
              simp only [is_proper_subformula]
              tauto
            case _ s4 =>
              have s5 : ¬ simplify phi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s1

              have s6 : ¬ simplify phi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s2

              have s7 : ¬ simplify psi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s3

              have s8 : ¬ simplify psi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s4

              simp only [simplify_aux]
              simp_all only [and_.injEq, and_false, implies_true, false_and]
              simp only [is_proper_subformula]
              simp only [is_subformula]
              tauto
    · sorry
  all_goals
    sorry
