import HandbookOfPracticalLogicLean.Prop.Semantics

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `replace_var_all_rec_opt τ F` := The simultaneous replacement of each var in the formula `F` using the hashmap from strings to formulas `τ`.
-/
def replace_var_all_rec_opt
  (τ : Std.HashMap String Formula_) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | var_ X =>
    match Std.HashMap.get? τ X with
    | none => var_ X
    | some F => F
  | not_ phi => not_ (replace_var_all_rec_opt τ phi)
  | and_ phi psi => and_ (replace_var_all_rec_opt τ phi) (replace_var_all_rec_opt τ psi)
  | or_ phi psi => or_ (replace_var_all_rec_opt τ phi) (replace_var_all_rec_opt τ psi)
  | imp_ phi psi => imp_ (replace_var_all_rec_opt τ phi) (replace_var_all_rec_opt τ psi)
  | iff_ phi psi => iff_ (replace_var_all_rec_opt τ phi) (replace_var_all_rec_opt τ psi)


#lint
