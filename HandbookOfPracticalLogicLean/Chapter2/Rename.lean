import HandbookOfPracticalLogicLean.Chapter2.Atom

import Batteries.Data.HashMap


set_option autoImplicit false


open Formula_


def Formula_.rename_atom_all_rec
  (σ : Batteries.HashMap String String) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | atom_ X =>
      match Batteries.HashMap.find? σ X with
      | some A => atom_ A
      | none => atom_ X
  | not_ phi => not_ (phi.rename_atom_all_rec σ)
  | and_ phi psi => and_ (phi.rename_atom_all_rec σ) (psi.rename_atom_all_rec σ)
  | or_ phi psi => or_ (phi.rename_atom_all_rec σ) (psi.rename_atom_all_rec σ)
  | imp_ phi psi => imp_ (phi.rename_atom_all_rec σ) (psi.rename_atom_all_rec σ)
  | iff_ phi psi => iff_ (phi.rename_atom_all_rec σ) (psi.rename_atom_all_rec σ)


def Formula_.atom_strings_to_nat_strings
  (F : Formula_)
  (start : Nat) :
  Formula_ :=
  let dedup_atom_list := F.atom_list.dedup

  let nat_list : List Nat := List.range' start dedup_atom_list.length
  let nat_string_list : List String := List.map Nat.repr nat_list

  let atom_string_nat_string_pair_list : List (String × String) := List.zip dedup_atom_list nat_string_list
  let atom_string_to_nat_string_map : Batteries.HashMap String String := Batteries.HashMap.ofList atom_string_nat_string_pair_list

  F.rename_atom_all_rec atom_string_to_nat_string_map

#eval (Formula_.atom_strings_to_nat_strings (Formula_| ((P -> Q) -> P)) 1).toString


def formula_list_to_disjoint_formula_list
  (start : Nat) :
  List Formula_ → List Formula_
  | [] => []
  | hd :: tl =>
    hd.atom_strings_to_nat_strings start ::
      formula_list_to_disjoint_formula_list (start + hd.atom_list.dedup.length) tl

  #eval let F := (Formula_| ((P -> Q) -> P)); (formula_list_to_disjoint_formula_list 1 [F, F, F]).map toString


lemma formula_list_to_disjoint_formula_list_length
  (start : Nat)
  (FS : List Formula_) :
  (formula_list_to_disjoint_formula_list start FS).length = FS.length :=
  by
  induction FS generalizing start
  case nil =>
    unfold formula_list_to_disjoint_formula_list
    rfl
  case cons hd tl ih =>
    unfold formula_list_to_disjoint_formula_list
    simp only [List.length_cons]
    rewrite [ih]
    rfl
