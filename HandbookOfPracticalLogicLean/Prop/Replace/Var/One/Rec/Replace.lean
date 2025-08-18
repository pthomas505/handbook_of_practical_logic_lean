import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Prop.Semantics

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `replace_var_one_rec A F P` :=

  `A → F` in `P` for each occurrence of the variable `A` in the formula `P`

  The result of simultaneously replacing each occurrence of the variable `A` in the formula `P` by an occurrence of the formula `F`.
-/
def replace_var_one_rec
  (A : String)
  (F : Formula_ ) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | var_ X => if A = X then F else var_ X
  | not_ phi => not_ (replace_var_one_rec A F phi)
  | and_ phi psi => and_ (replace_var_one_rec A F phi) (replace_var_one_rec A F psi)
  | or_ phi psi => or_ (replace_var_one_rec A F phi) (replace_var_one_rec A F psi)
  | imp_ phi psi => imp_ (replace_var_one_rec A F phi) (replace_var_one_rec A F psi)
  | iff_ phi psi => iff_ (replace_var_one_rec A F phi) (replace_var_one_rec A F psi)


theorem theorem_2_3_one
  (V : ValuationAsTotalFunction)
  (A : String)
  (P : Formula_)
  (F : Formula_) :
  eval V (replace_var_one_rec A P F) = eval (Function.updateITE' V A (eval V P)) F :=
  by
  induction F
  case false_ | true_ =>
    simp only [eval]
  case var_ X =>
    simp only [eval]
    unfold replace_var_one_rec
    unfold Function.updateITE'
    split_ifs
    · rfl
    · unfold eval
      rfl
  case not_ phi ih =>
    simp only [eval]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


theorem corollary_2_4_one
  (A : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : F.is_tautology) :
  ((replace_var_one_rec A P F)).is_tautology :=
  by
  unfold is_tautology at h1
  unfold satisfies at h1

  unfold is_tautology
  unfold satisfies
  intro V
  rewrite [theorem_2_3_one]
  apply h1


theorem theorem_2_5_one
  (V : ValuationAsTotalFunction)
  (A : String)
  (P Q : Formula_)
  (R : Formula_)
  (h1 : eval V P = eval V Q) :
  eval V (replace_var_one_rec A P R) = eval V (replace_var_one_rec A Q R) :=
  by
  simp only [theorem_2_3_one]
  rewrite [h1]
  rfl


theorem corollary_2_6_one
  (V : ValuationAsTotalFunction)
  (A : String)
  (P Q : Formula_)
  (R : Formula_)
  (h1 : are_logically_equivalent P Q) :
  eval V (replace_var_one_rec A P R) = eval V (replace_var_one_rec A Q R) :=
  by
  simp only [are_logically_equivalent_iff_eval_eq] at h1

  apply theorem_2_5_one
  apply h1


-------------------------------------------------------------------------------


lemma not_var_occurs_in_formula_imp_not_var_occurs_in_formula_replace_var_one_rec
  (A : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : ¬ var_occurs_in_formula A P) :
  ¬ var_occurs_in_formula A (replace_var_one_rec A P F) :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec
    unfold var_occurs_in_formula
    intro contra
    exact contra
  case var_ X =>
    unfold replace_var_one_rec
    split_ifs
    case pos c1 =>
      exact h1
    case neg c1 =>
      unfold var_occurs_in_formula
      exact c1
  case not_ phi ih =>
    unfold replace_var_one_rec
    unfold var_occurs_in_formula
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec
    unfold var_occurs_in_formula
    intro contra
    cases contra
    case inl contra =>
      contradiction
    case inr contra =>
      contradiction


#lint
