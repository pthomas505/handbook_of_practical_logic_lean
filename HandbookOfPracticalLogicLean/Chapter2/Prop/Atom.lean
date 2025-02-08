import HandbookOfPracticalLogicLean.Chapter2.Prop.Formula

import Mathlib.Tactic


set_option autoImplicit false


namespace Prop_


open Formula_


/--
  `Formula_.atom_set F` := The set of all of the atoms that have an occurrence in the formula `F`.
-/
def Formula_.atom_set :
  Formula_ → Finset String
  | false_ => ∅
  | true_ => ∅
  | atom_ X => {X}
  | not_ phi => phi.atom_set
  | and_ phi psi => phi.atom_set ∪ psi.atom_set
  | or_ phi psi => phi.atom_set ∪ psi.atom_set
  | imp_ phi psi => phi.atom_set ∪ psi.atom_set
  | iff_ phi psi => phi.atom_set ∪ psi.atom_set


/--
  `atom_occurs_in A F` := True if and only if there is an occurrence of the atom `A` in the formula `F`.
-/
def atom_occurs_in
  (A : String) :
  Formula_ → Prop
  | false_ => False
  | true_ => False
  | atom_ X => A = X
  | not_ phi => atom_occurs_in A phi
  | and_ phi psi => atom_occurs_in A phi ∨ atom_occurs_in A psi
  | or_ phi psi => atom_occurs_in A phi ∨ atom_occurs_in A psi
  | imp_ phi psi => atom_occurs_in A phi ∨ atom_occurs_in A psi
  | iff_ phi psi => atom_occurs_in A phi ∨ atom_occurs_in A psi

instance
  (A : String)
  (F : Formula_) :
  Decidable (atom_occurs_in A F) :=
  by
  induction F
  all_goals
    simp only [atom_occurs_in]
    infer_instance


example
  (A : String)
  (F : Formula_) :
  atom_occurs_in A F ↔ A ∈ F.atom_set :=
  by
  induction F
  all_goals
    unfold atom_occurs_in
    unfold atom_set
  case true_ | false_ =>
    simp
  case atom_ X =>
    simp
  case not_ phi ih =>
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


#lint
