import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.Replace


set_option autoImplicit false


open Formula_


structure Equation : Type where
  (lhs : Formula_)
  (rhs : Formula_)
  deriving Inhabited, DecidableEq, Repr


def unify
  (E : Equation) :
  Option (String → Formula_) :=
  match E with
  | ⟨false_, false_⟩
  | ⟨true_, true_⟩ => Option.some atom_
  | ⟨atom_ X, F⟩ =>
    if atom_ X = F
    then Option.some atom_
    else
      if atom_occurs_in X F
      then Option.none
      else Option.some (Function.updateITE atom_ X F)
  | ⟨F, atom_ X⟩ =>
    if F = atom_ X
    then Option.some atom_
    else
      if atom_occurs_in X F
      then Option.none
      else Option.some (Function.updateITE atom_ X F)
  | ⟨not_ phi, not_ phi'⟩ => unify ⟨phi, phi'⟩
  | ⟨and_ phi psi, and_ phi' psi'⟩
  | ⟨or_ phi psi, or_ phi' psi'⟩
  | ⟨imp_ phi psi, imp_ phi' psi'⟩
  | ⟨iff_ phi psi, iff_ phi' psi'⟩ => do
    match unify ⟨phi, phi'⟩ with
    | Option.some σ_1 =>
      match unify ⟨replace_atom_all_rec σ_1 psi, replace_atom_all_rec σ_1 psi'⟩ with
      | Option.some σ_2 => Option.some ((replace_atom_all_rec σ_2) ∘ σ_1)
      | Option.none => Option.none
    | Option.none => Option.none
  | _ => Option.none
