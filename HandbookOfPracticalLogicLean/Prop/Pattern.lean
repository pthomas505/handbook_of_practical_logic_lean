import HandbookOfPracticalLogicLean.Prop.Formula

import Batteries.Data.HashMap


set_option autoImplicit false


open Formula_


def pattern_match_aux
  (σ : Batteries.HashMap String Formula_) :
  Formula_ → Formula_ → Option (Batteries.HashMap String Formula_)
  | false_, false_ => some σ
  | true_, true_ => some σ
  | atom_ X, F =>
    match Batteries.HashMap.find? σ X with
    | none => Batteries.HashMap.insert σ X F
    | some F' => if F' = F then some σ else none
  | not_ phi, not_ phi' => pattern_match_aux σ phi phi'
  | and_ phi psi, and_ phi' psi' =>
    match pattern_match_aux σ phi phi' with
    | none => none
    | some σ' => pattern_match_aux σ' psi psi'
  | or_ phi psi, or_ phi' psi' =>
    match pattern_match_aux σ phi phi' with
    | none => none
    | some σ' => pattern_match_aux σ' psi psi'
  | imp_ phi psi, imp_ phi' psi' =>
    match pattern_match_aux σ phi phi' with
    | none => none
    | some σ' => pattern_match_aux σ' psi psi'
  | iff_ phi psi, iff_ phi' psi' =>
    match pattern_match_aux σ phi phi' with
    | none => none
    | some σ' => pattern_match_aux σ' psi psi'
  | _, _ => none


def pattern_match
  (P Q : Formula_) :
  Option (Batteries.HashMap String Formula_) :=
  pattern_match_aux {} P Q


instance : ToString (Batteries.HashMap String Formula_) :=
  { toString := fun (M : Batteries.HashMap String Formula_) => M.toList.toString }


#eval pattern_match (and_ (atom_ "P") (atom_ "Q")) (atom_ "R")
#eval pattern_match (atom_ "R") (and_ (atom_ "P") (atom_ "Q"))
#eval pattern_match (and_ (atom_ "R") (atom_ "S")) (and_ (atom_ "P") (or_ (atom_ "Q") (atom_ "R")))
