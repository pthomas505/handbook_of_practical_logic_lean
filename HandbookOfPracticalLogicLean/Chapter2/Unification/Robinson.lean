import MathlibExtraLean.FunctionUpdateITE
import MathlibExtraLean.FunctionUpdateFromListOfPairsITE

import HandbookOfPracticalLogicLean.Chapter2.Replace


set_option autoImplicit false


open Formula_


structure Equation : Type where
  (lhs : Formula_)
  (rhs : Formula_)
  deriving Inhabited, DecidableEq, Repr


def Equation.atom_list
  (E : Equation) :
  List String :=
  E.lhs.atom_list ∪ E.rhs.atom_list


/--
  `List.dup_count_aux acc L` := Helper function for `List.dup_count`.
-/
def List.dup_count_aux
  {α : Type}
  [DecidableEq α]
  (acc : Finset α) :
  List α → Nat
  | [] => 0
  | hd :: tl =>
    if hd ∈ tl ∧ hd ∉ acc
    then 1 + List.dup_count_aux (acc ∪ {hd}) tl
    else List.dup_count_aux acc tl

/--
  `List.dup_count L` := The number of elements that occur more than once in the list `L`.
-/
def List.dup_count
  {α : Type}
  [DecidableEq α]
  (L : List α) :
  Nat :=
  List.dup_count_aux {} L

#eval [0].dup_count
#eval [0, 0].dup_count
#eval [0, 0, 0].dup_count
#eval [0, 0, 1].dup_count
#eval [0, 0, 1, 1].dup_count
#eval [1, 0, 0, 1].dup_count
#eval [0, 1, 0, 1].dup_count


partial
def unify
  (E : Equation) :
  Option (String → Formula_) :=
  match E with
  | ⟨false_, false_⟩
  | ⟨true_, true_⟩ => Option.some atom_
  | ⟨atom_ X, F⟩
  | ⟨F, atom_ X⟩ =>
    if atom_ X = F
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
    let σ_1 ← unify ⟨phi, phi'⟩
    let σ_2 ← unify ⟨replace_atom_all_rec σ_1 psi, replace_atom_all_rec σ_1 psi'⟩
    (replace_atom_all_rec σ_2) ∘ σ_1
  | _ => Option.none


def print_unify
  (E : Equation) :
  Option (String → Formula_) → Option (List (Formula_ × Formula_))
  | Option.none => Option.none
  | Option.some σ => Option.some (List.map (fun (X : String) => (atom_ X, σ X)) E.atom_list)


#eval! let E : Equation := ⟨atom_ "P", atom_ "Q"⟩; print_unify E (unify E)

#eval! let E : Equation := ⟨atom_ "X", not_ (atom_ "X")⟩; print_unify E (unify E)

#eval! let E : Equation := ⟨and_ (atom_ "X") (atom_ "Y"), and_ (atom_ "Y") (atom_ "Z")⟩; print_unify E (unify E)

#eval! let E : Equation := ⟨or_ (and_ (atom_ "X") (atom_ "Y")) (atom_ "Z"), or_ (and_ (atom_ "Y") (atom_ "Z")) (atom_ "X")⟩; print_unify E (unify E)


partial
def unify_list
  (E : Equation) :
  Option (List (String × Formula_)) :=
  match E with
  | ⟨false_, false_⟩
  | ⟨true_, true_⟩ => Option.some []
  | ⟨atom_ X, F⟩
  | ⟨F, atom_ X⟩ =>
    if atom_ X = F
    then Option.some []
    else
      if atom_occurs_in X F
      then Option.none
      else Option.some [(X, F)]
  | ⟨not_ phi, not_ phi'⟩ =>
      unify_list ⟨phi, phi'⟩
  | ⟨and_ phi psi, and_ phi' psi'⟩
  | ⟨or_ phi psi, or_ phi' psi'⟩
  | ⟨imp_ phi psi, imp_ phi' psi'⟩
  | ⟨iff_ phi psi, iff_ phi' psi'⟩ => do
      let σ_1 ← unify_list ⟨phi, phi'⟩
      let σ_1' : String → Formula_ := Function.updateFromListOfPairsITE atom_ σ_1
      let σ_2 ← unify_list ⟨replace_atom_all_rec σ_1' psi, replace_atom_all_rec σ_1' psi'⟩
      σ_1 ++ σ_2
  | _ => Option.none


#eval! unify_list ⟨atom_ "P", atom_ "Q"⟩

#eval! unify_list ⟨atom_ "X", not_ (atom_ "X")⟩

#eval! unify_list ⟨and_ (atom_ "X") (atom_ "Y"), and_ (atom_ "Y") (atom_ "Z")⟩
