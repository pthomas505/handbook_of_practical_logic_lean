import HandbookOfPracticalLogicLean.Chapter2.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `Formula_.subformula_list F` := The list of all of the subformulas of a formula `F`.
-/
def Formula_.subformula_list :
  Formula_ → List Formula_
  | false_ => [false_]
  | true_ => [true_]
  | atom_ X => [atom_ X]
  | not_ phi => [not_ phi] ++ phi.subformula_list
  | and_ phi psi => [and_ phi psi] ++ phi.subformula_list ++ psi.subformula_list
  | or_ phi psi => [or_ phi psi] ++ phi.subformula_list ++ psi.subformula_list
  | imp_ phi psi => [imp_ phi psi] ++ phi.subformula_list ++ psi.subformula_list
  | iff_ phi psi => [iff_ phi psi] ++ phi.subformula_list ++ psi.subformula_list


/--
  `is_subformula F F'` := True if and only if `F` is a subformula of the formula `F'`.
-/
def is_subformula
  (F : Formula_) :
  Formula_ → Prop
  | false_ => F = false_
  | true_ => F = true_
  | atom_ X => F = atom_ X
  | not_ phi =>
    F = not_ phi ∨
    is_subformula F phi
  | and_ phi psi =>
    F = and_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi
  | or_ phi psi =>
    F = or_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi
  | imp_ phi psi =>
    F = imp_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi
  | iff_ phi psi =>
    F = iff_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi

instance
  (F F' : Formula_) :
  Decidable (is_subformula F F') :=
  by
  induction F'
  all_goals
    unfold is_subformula
    infer_instance


lemma not_is_subformula_imp_not_equal
  (F F' : Formula_)
  (h1 : ¬ is_subformula F F') :
  ¬ F = F' :=
  by
  cases F'
  all_goals
    intro contra
    apply h1
    unfold is_subformula
  case false_ | true_ | atom_ X =>
    exact contra
  all_goals
    left
    exact contra


/--
  `is_proper_subformula F F'` := True if and only if `F` is a proper subformula of the formula `F'`.
-/
def is_proper_subformula
  (F F' : Formula_) :
  Prop :=
  is_subformula F F' ∧ ¬ F = F'

instance
  (F F' : Formula_) :
  Decidable (is_proper_subformula F F') :=
  by
  unfold is_proper_subformula
  infer_instance


#lint
