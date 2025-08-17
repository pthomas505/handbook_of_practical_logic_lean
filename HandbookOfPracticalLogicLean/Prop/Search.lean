import HandbookOfPracticalLogicLean.Chapter2.Rename

import Batteries.Data.HashMap


set_option autoImplicit false


open Formula_


def Unifier : Type := Batteries.HashMap String String


def unify_formulas
  (P Q : Formula_) :
  Option Unifier :=
  sorry


structure mp_formulas : Type where
  (major : Formula_)
  (minor : Formula_)
  (consequent : Formula_)


def unify_formulas_mp
  (major minor : Formula_) :
  Option mp_formulas :=
  let major_minor_disjoint := formula_list_to_disjoint_formula_list 1 [major, minor]
  have : 0 < major_minor_disjoint.length :=
  by
    unfold major_minor_disjoint
    rewrite [formula_list_to_disjoint_formula_list_length]
    simp only [List.length_cons, List.length_singleton, List.length_nil]
    simp only [zero_add, Nat.reduceAdd, Nat.ofNat_pos]
  let major_disjoint : Formula_ := major_minor_disjoint[0]

  have : 1 < major_minor_disjoint.length :=
  by
    unfold major_minor_disjoint
    rewrite [formula_list_to_disjoint_formula_list_length]
    simp only [List.length_cons, List.length_singleton, List.length_nil]
    simp only [zero_add, Nat.reduceAdd, Nat.one_lt_ofNat]
  let minor_disjoint : Formula_ := major_minor_disjoint[1]

  let consequent : Formula_ := atom_ Nat.zero.repr

  match unify_formulas major_disjoint (imp_ minor_disjoint consequent) with
  | some σ =>
      let major_instantiated := major_disjoint.rename_atom_all_rec σ
      let minor_instantiated := minor_disjoint.rename_atom_all_rec σ
      let consequent_instantiated := consequent.rename_atom_all_rec σ
      some ⟨major_instantiated, minor_instantiated, consequent_instantiated⟩
  | none => none


inductive Proof : Type
  | ax_1 : Proof
  | ax_2 : Proof
  | ax_3 : Proof
  | mp : Proof → Proof → Formula_ → Proof
  | sub : Proof → Formula_ → Proof

open Proof


def schema_1 : Formula_ := (Formula_| (phi -> (psi -> phi)))
def schema_2 : Formula_ := (Formula_| ((phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))))
def schema_3 : Formula_ := (Formula_| ((~ phi -> ~ psi) -> (psi -> phi)))

def Proof.formula :
  Proof → Formula_
  | ax_1 => schema_1
  | ax_2 => schema_2
  | ax_3 => schema_3
  | mp _ _ F => F
  | sub _ F => F


def unify_proofs_mp
  (major_proof minor_proof : Proof) :
  Option Proof :=
  match unify_formulas_mp major_proof.formula minor_proof.formula with
  | some result =>
      some (mp
              (sub major_proof result.major)
              (sub minor_proof result.minor)
              result.consequent)
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
