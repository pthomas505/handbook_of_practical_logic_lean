import HandbookOfPracticalLogicLean.Chapter2.Replace

import Init.Data.List
import Batteries.Data.HashMap


set_option autoImplicit false


open Formula_


def is_unifier
  (σ : String → Formula_)
  (pairs : List (Formula_ × Formula_)) :
  Prop :=
  ∀ (p : (Formula_ × Formula_)), p ∈ pairs →
    replace_atom_all_rec σ p.fst =
      replace_atom_all_rec σ p.snd


lemma replace_atom_all_rec_compose
  (F : Formula_)
  (σ τ : String → Formula_) :
  replace_atom_all_rec ((replace_atom_all_rec τ) ∘ σ) F =
    replace_atom_all_rec τ (replace_atom_all_rec σ F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [replace_atom_all_rec]
  case atom_ X =>
    simp only [replace_atom_all_rec]
    exact Function.comp_apply
  case not_ phi ih =>
    simp only [replace_atom_all_rec]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [replace_atom_all_rec]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


example
  (σ τ : String → Formula_)
  (pairs : List (Formula_ × Formula_))
  (h1 : is_unifier σ pairs) :
  is_unifier ((replace_atom_all_rec τ) ∘ σ) pairs :=
  by
  unfold is_unifier at h1
  unfold is_unifier
  intro p a1
  simp only [replace_atom_all_rec_compose]
  rewrite [h1 p a1]
  rfl


def pattern_match_aux
  (σ : List (String × Formula_)) :
  Formula_ → Formula_ → Option (List (String × Formula_))
  | false_, false_ => some σ
  | true_, true_ => some σ
  | atom_ X, F =>
    match List.find? (fun (e : String × Formula_) => e.fst = X) σ with
    | none => some ((X, F) :: σ)
    | some e => if e.snd = F then some σ else none
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
  Option (List (String × Formula_)) :=
  pattern_match_aux [] P Q

#eval pattern_match (and_ (atom_ "P") (atom_ "Q")) (atom_ "R")
#eval pattern_match (atom_ "R") (and_ (atom_ "P") (atom_ "Q"))
#eval pattern_match (and_ (atom_ "R") (atom_ "S")) (and_ (atom_ "P") (or_ (atom_ "Q") (atom_ "R")))


-------------------------------------------------------------------------------


def Formula_.rename_atoms
  (σ : Batteries.HashMap String String) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | atom_ X =>
      match Batteries.HashMap.find? σ X with
      | some Y => atom_ Y
      | none => atom_ X
  | not_ phi => not_ (phi.rename_atoms σ)
  | and_ phi psi => and_ (phi.rename_atoms σ) (psi.rename_atoms σ)
  | or_ phi psi => or_ (phi.rename_atoms σ) (psi.rename_atoms σ)
  | imp_ phi psi => imp_ (phi.rename_atoms σ) (psi.rename_atoms σ)
  | iff_ phi psi => iff_ (phi.rename_atoms σ) (psi.rename_atoms σ)


def Formula_.rename_atoms_to_nat
  (F : Formula_)
  (start : Nat) :
  Formula_ :=
  let dedup_atom_list := F.atom_list.dedup
  let index_list : List Nat := List.range' start dedup_atom_list.length
  let index_as_string_list : List String := List.map Nat.repr index_list
  let atom_index_as_string_pair_list : List (String × String) := List.zip dedup_atom_list index_as_string_list
  let string_to_index_string_map := Batteries.HashMap.ofList atom_index_as_string_pair_list
  F.rename_atoms string_to_index_string_map

#eval Formula_.rename_atoms_to_nat (Formula_| ((P -> Q) -> P)) 1


def mk_formula_list_atoms_disjoint
  (start : Nat) :
  List Formula_ → List Formula_
  | [] => []
  | hd :: tl => (hd.rename_atoms_to_nat start) :: mk_formula_list_atoms_disjoint (start + hd.atom_list.dedup.length) tl

  #eval let F := (Formula_| ((P -> Q) -> P)); (mk_formula_list_atoms_disjoint 1 [F, F, F, F]).map toString


lemma mk_formula_list_atoms_disjoint_length
  (start : Nat)
  (FS : List Formula_) :
  (mk_formula_list_atoms_disjoint start FS).length = FS.length :=
  by
  induction FS generalizing start
  case nil =>
    unfold mk_formula_list_atoms_disjoint
    rfl
  case cons hd tl ih =>
    unfold mk_formula_list_atoms_disjoint
    simp only [List.length_cons]
    rewrite [ih]
    rfl


def Unifier : Type := Batteries.HashMap String String


def unify_formulas
  (P Q : Formula_) :
  Option Unifier :=
  sorry


structure unified_mp : Type where
  (major : Formula_)
  (minor : Formula_)
  (consequent : Formula_)


def unify_formulas_mp
  (major minor : Formula_) :
  Option unified_mp :=
  let renamed := mk_formula_list_atoms_disjoint 1 [major, minor]
  have : 0 < renamed.length :=
  by
    unfold renamed
    rewrite [mk_formula_list_atoms_disjoint_length]
    simp only [List.length_cons, List.length_singleton, List.length_nil]
    simp only [zero_add, Nat.reduceAdd, Nat.ofNat_pos]
  let major_renamed : Formula_ := renamed[0]

  have : 1 < renamed.length :=
  by
    unfold renamed
    rewrite [mk_formula_list_atoms_disjoint_length]
    simp only [List.length_cons, List.length_singleton, List.length_nil]
    simp only [zero_add, Nat.reduceAdd, Nat.one_lt_ofNat]
  let minor_renamed : Formula_ := renamed[1]

  let consequent : Formula_ := atom_ Nat.zero.repr

  match unify_formulas major_renamed (imp_ minor_renamed consequent) with
  | some σ =>
      let major_unified := major_renamed.rename_atoms σ
      let minor_unified := minor_renamed.rename_atoms σ
      let consequent_unified := consequent.rename_atoms σ
      some ⟨major_unified, minor_unified, consequent_unified⟩
  | none => none


inductive Proof : Type
  | ax_1 : Proof
  | ax_2 : Proof
  | ax_3 : Proof
  | mp : Proof → Formula_ → Proof → Formula_ → Formula_ → Proof

open Proof


def schema_1 : Formula_ := (Formula_| (phi -> (psi -> phi)))
def schema_2 : Formula_ := (Formula_| ((phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))))
def schema_3 : Formula_ := (Formula_| ((~ phi -> ~ psi) -> (psi -> phi)))

def Proof.formula :
  Proof → Formula_
  | ax_1 => schema_1
  | ax_2 => schema_2
  | ax_3 => schema_3
  | mp _ _ _ _ F => F


def unify_proofs_mp
  (major_proof minor_proof : Proof) :
  Option Proof :=
  match unify_formulas_mp major_proof.formula minor_proof.formula with
  | some result =>
      some (mp major_proof result.major minor_proof result.minor result.consequent)
  | none => none


def init : List Proof := [ax_1, ax_2, ax_3]


/-
  For every pair of proofs taken from `init` call `unify_proofs_mp`. If for a given pair there is a resulting proof and it can be unified with the proof goal then halt and return the proof. If there is a resulting proof and it can not be unified with the proof goal then add the proof into a new list of proofs.

  If the new list of proofs is empty after calling `unify_proofs_mp` on every pair in `init` then halt. Otherwise append the new list to `init` and recursively repeat using the appended list in place of `init`.
-/


/-
all ways to choose a fixed number of elements from a list

Is there a function available that takes a list of `l` and a natural number `n` and returns all unique lists of length `n` where every element of each these lists is taken from `l`? Selecting the same element from `l` more than once is allowed, and lists are the same if they have the same elements in same order. For example, for `l = [1, 2, 3]` and `n = 2` we would have `[1, 1], [2, 2], [3, 3], [1, 2], [2, 1], [1,3], [3,1], [2, 3], [3, 2]`.
-/
