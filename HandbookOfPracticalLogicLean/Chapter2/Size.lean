import HandbookOfPracticalLogicLean.Chapter2.Formula

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


#lint
