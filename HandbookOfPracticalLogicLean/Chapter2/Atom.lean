import HandbookOfPracticalLogicLean.Chapter2.Formula

import Mathlib.Tactic


set_option autoImplicit false


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
  `Formula_.atom_list F` := The list of all of the atoms that have an occurrence in the formula `F`.
-/
def Formula_.atom_list :
  Formula_ → List String
  | false_ => []
  | true_ => []
  | atom_ X => [X]
  | not_ phi => phi.atom_list
  | and_ phi psi => phi.atom_list ++ psi.atom_list
  | or_ phi psi => phi.atom_list ++ psi.atom_list
  | imp_ phi psi => phi.atom_list ++ psi.atom_list
  | iff_ phi psi => phi.atom_list ++ psi.atom_list


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
    unfold atom_occurs_in
    infer_instance


lemma atom_occurs_in_iff_mem_atom_set
  (A : String)
  (F : Formula_) :
  atom_occurs_in A F ↔ A ∈ F.atom_set :=
  by
  induction F
  all_goals
    unfold atom_occurs_in
    unfold atom_set
  case true_ | false_ =>
    simp only [Finset.not_mem_empty]
  case atom_ X =>
    simp only [Finset.mem_singleton]
  case not_ phi ih =>
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [Finset.mem_union]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


lemma atom_occurs_in_iff_mem_atom_list
  (A : String)
  (F : Formula_) :
  atom_occurs_in A F ↔ A ∈ F.atom_list :=
  by
  induction F
  all_goals
    unfold atom_occurs_in
    unfold atom_list
  case true_ | false_ =>
    simp only [List.not_mem_nil]
  case atom_ X =>
    simp only [List.mem_singleton]
  case not_ phi ih =>
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [List.mem_append]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


#lint
