import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.Semantics

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `replace_atom_one_rec A F P` :=

  `A → F` in `P` for each occurrence of the atom `A` in the formula `P`

  The result of simultaneously replacing each occurrence of the atom `A` in the formula `P` by an occurrence of the formula `F`.
-/
def replace_atom_one_rec
  (A : String)
  (F : Formula_ ) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | atom_ X => if A = X then F else atom_ X
  | not_ phi => not_ (replace_atom_one_rec A F phi)
  | and_ phi psi => and_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)
  | or_ phi psi => or_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)
  | imp_ phi psi => imp_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)
  | iff_ phi psi => iff_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)


theorem theorem_2_3_one
  (V : ValuationAsTotalFunction)
  (A : String)
  (P : Formula_)
  (F : Formula_) :
  eval V (replace_atom_one_rec A P F) = eval (Function.updateITE' V A (eval V P)) F :=
  by
  induction F
  case false_ | true_ =>
    simp only [eval]
  case atom_ X =>
    simp only [eval]
    unfold replace_atom_one_rec
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
  ((replace_atom_one_rec A P F)).is_tautology :=
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
  eval V (replace_atom_one_rec A P R) = eval V (replace_atom_one_rec A Q R) :=
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
  eval V (replace_atom_one_rec A P R) = eval V (replace_atom_one_rec A Q R) :=
  by
  simp only [are_logically_equivalent_iff_eval_eq] at h1

  apply theorem_2_5_one
  apply h1


-------------------------------------------------------------------------------


lemma not_atom_occurs_in_imp_not_atom_occurs_in_replace_atom_one_rec
  (A : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : ¬ atom_occurs_in A P) :
  ¬ atom_occurs_in A (replace_atom_one_rec A P F) :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_atom_one_rec
    unfold atom_occurs_in
    intro contra
    exact contra
  case atom_ X =>
    unfold replace_atom_one_rec
    split_ifs
    case pos c1 =>
      exact h1
    case neg c1 =>
      unfold atom_occurs_in
      exact c1
  case not_ phi ih =>
    unfold replace_atom_one_rec
    unfold atom_occurs_in
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_atom_one_rec
    unfold atom_occurs_in
    intro contra
    cases contra
    case inl contra =>
      contradiction
    case inr contra =>
      contradiction


#lint
