import HandbookOfPracticalLogicLean.Chapter2.Bool.Semantics

import Mathlib.Tactic


set_option autoImplicit false


namespace Prop_


open Formula_


/--
  `Formula_.has_dual F` := True if and only if there exists a dual of the formula `F`.
-/
def Formula_.has_dual :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ phi => phi.has_dual
  | and_ phi psi => phi.has_dual ∧ psi.has_dual
  | or_ phi psi => phi.has_dual ∧ psi.has_dual
  | _ => False

instance
  (F : Formula_) :
  Decidable (has_dual F) :=
  by
  induction F
  all_goals
    simp only [has_dual]
    infer_instance


/--
  `Formula_.dual F` := The result of simultaneously exchanging `true_` for `false_`, `false_` for `true_`, `or_` for `and_`, and `and_` for `or_`,  in the formula `F`.
-/
def Formula_.dual :
  Formula_ → Formula_
  | false_ => true_
  | true_ => false_
  | atom_ X => atom_ X
  | not_ phi => not_ phi.dual
  | and_ phi psi => or_ phi.dual psi.dual
  | or_ phi psi => and_ phi.dual psi.dual
  | imp_ phi psi => imp_ phi.dual psi.dual
  | iff_ phi psi => iff_ phi.dual psi.dual


example
  (F : Formula_) :
  dual (dual F) = F :=
  by
  induction F
  all_goals
    simp only [dual]
  case not_ phi ih =>
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


theorem theorem_2_7
  (V : Valuation)
  (F : Formula_)
  (h1 : has_dual F) :
  eval V (dual F) = b_not (eval (b_not ∘ V) F) :=
  by
  induction F
  all_goals
    unfold dual
    unfold eval
  case false_ | true_ =>
    simp only [b_not]
  case atom_ X =>
    simp only [Function.comp_apply]
    cases V X
    all_goals
      simp only [b_not]
  case not_ phi ih =>
    unfold has_dual at h1

    rewrite [ih h1]
    rfl
  case and_ phi psi phi_ih psi_ih =>
    unfold has_dual at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    rewrite [phi_ih h1_left]
    rewrite [psi_ih h1_right]

    bool_eq_to_prop
    tauto
  case or_ phi psi phi_ih psi_ih =>
    unfold has_dual at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    rewrite [phi_ih h1_left]
    rewrite [psi_ih h1_right]

    bool_eq_to_prop
    tauto
  all_goals
    unfold has_dual at h1
    contradiction


theorem corollary_2_8_a
  (P Q : Formula_)
  (h1 : are_logically_equivalent P Q)
  (h2 : has_dual P)
  (h3 : has_dual Q) :
  are_logically_equivalent (dual P) (dual Q) :=
  by
  simp only [are_logically_equivalent_iff_eval_eq_all_val] at h1

  simp only [are_logically_equivalent_iff_eval_eq_all_val]
  intro V
  rewrite [theorem_2_7 V P h2]
  rewrite [theorem_2_7 V Q h3]
  congr! 1
  apply h1


lemma is_tautology_iff_logically_equivalent_to_true
  (F : Formula_) :
  F.is_tautology ↔ are_logically_equivalent F true_ :=
  by
  simp only [are_logically_equivalent_iff_eval_eq_all_val]
  unfold is_tautology
  unfold satisfies
  simp only [eval]


example
  (F : Formula_) :
  are_logically_equivalent F false_ ↔ are_logically_equivalent (not_ F) true_ :=
  by
  simp only [are_logically_equivalent_iff_eval_eq_all_val]
  simp only [eval]
  congr! 1
  case _ V =>
    simp only [b_not]
    cases eval V F
    all_goals
      tauto


theorem corollary_2_8_b
  (F : Formula_)
  (h1 : F.is_tautology)
  (h2 : has_dual F) :
  (not_ (dual F)).is_tautology :=
  by
  rewrite [is_tautology_iff_logically_equivalent_to_true] at h1

  obtain s1 := corollary_2_8_a F true_ h1 h2
  simp only [has_dual] at s1
  simp only [dual] at s1
  simp at s1
  simp only [are_logically_equivalent_iff_eval_eq_all_val] at s1

  unfold is_tautology
  unfold satisfies
  unfold eval
  intro V
  rewrite [s1]
  simp only [eval]
  simp only [b_not]


#lint
