import HandbookOfPracticalLogicLean.Chapter2.SubFormula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `Formula_.size F` := The number of subformulas in the formula `F`.
-/
def Formula_.size :
  Formula_ → Nat
  | false_ => 1
  | true_ => 1
  | atom_ _ => 1
  | not_ phi => phi.size + 1
  | and_ phi psi => phi.size + psi.size + 1
  | or_ phi psi => phi.size + psi.size + 1
  | imp_ phi psi => phi.size + psi.size + 1
  | iff_ phi psi => phi.size + psi.size + 1


example
  (F : Formula_) :
  size F = (subformula_list F).length :=
  by
  induction F
  all_goals
    unfold size
    unfold subformula_list
  case false_ | true_ | atom_ X =>
    simp only [List.length_singleton]
  case not_ phi ih =>
    simp only [List.singleton_append, List.length_cons]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [List.singleton_append, List.length_cons, List.length_append]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


#lint
