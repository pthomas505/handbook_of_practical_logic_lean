import HandbookOfPracticalLogicLean.Chapter2.Semantics

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


theorem theorem_2_2
  (V V' : Valuation)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → (V A ↔ V' A)) :
  eval V F ↔ eval V' F :=
  by
  induction F
  all_goals
    unfold eval
  case false_ | true_ =>
    rfl
  case atom_ X =>
    apply h1
    unfold atom_occurs_in
    rfl
  case not_ phi ih =>
    congr! 1
    apply ih
    intro X a1
    apply h1
    unfold atom_occurs_in
    exact a1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    congr! 1
    · apply phi_ih
      intro X a1
      apply h1
      unfold atom_occurs_in
      left
      exact a1
    · apply psi_ih
      intro X a1
      apply h1
      unfold atom_occurs_in
      right
      exact a1
