import HandbookOfPracticalLogicLean.Prop.Formula


set_option autoImplicit false


open Formula_


def pattern_match_aux
  (σ : Std.HashMap String Formula_) :
  Formula_ → Formula_ → Option (Std.HashMap String Formula_)
  | false_, false_ => some σ
  | true_, true_ => some σ
  | var_ X, F =>
    match Std.HashMap.get? σ X with
    | none => Std.HashMap.insert σ X F
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
  Option (Std.HashMap String Formula_) :=
  pattern_match_aux {} P Q


instance : ToString (Std.HashMap String Formula_) :=
  { toString := fun (M : Std.HashMap String Formula_) => M.toList.toString }


#eval pattern_match (and_ (var_ "P") (var_ "Q")) (var_ "R")
#eval pattern_match (var_ "R") (and_ (var_ "P") (var_ "Q"))
#eval pattern_match (and_ (var_ "R") (var_ "S")) (and_ (var_ "P") (or_ (var_ "Q") (var_ "R")))
