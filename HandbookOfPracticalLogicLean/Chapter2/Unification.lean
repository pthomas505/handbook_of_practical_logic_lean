import HandbookOfPracticalLogicLean.Chapter2.Replace

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


def Unifier : Type := List (String × Formula_)


def unify_formulas
  (P Q : Formula_) :
  Option Unifier :=
  sorry


structure unified_mp : Type where
  (sigma : Unifier)
  (major : Formula_)
  (minor : Formula_)
  (consequent : Formula_)


def unify_formulas_mp
  (major minor : Formula_) :
  Option unified_mp :=
  sorry
  /-
  Let `major_renamed` be the result of consistently renaming the meta variables in `major` to ensure that none of the names in `major_renamed` occur in `minor`.

  Let `M` be a meta variable with a name that does not occur in `major_renamed` or `minor`.

  Call `unify_formulas` with `major_renamed` and `minor -> M` to obtain a substitution mapping `σ` or `none`.

  If `σ` then return `{σ, (σ major_renamed), (σ minor), (σ M) }`.
  If `none` then return `none`.
  -/


inductive Proof : Type
    -- axiom scheme 1
  | ax_1 : Proof
    -- axiom scheme 2
  | ax_2 : Proof
    -- axiom scheme 3
  | ax_3 : Proof
    -- modus ponens
  | mp : Proof → Proof → Formula_ → Proof
    -- substitution
  | sub : Proof → Unifier → Formula_ → Proof

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
  | sub _ _ F => F


def Proof.depth :
  Proof → Nat
  | ax_1 => 1
  | ax_2 => 1
  | ax_3 => 1
  | mp major minor _ =>
      (max major.depth minor.depth) + 1
  | sub child _ _ => child.depth + 1


def unify_proofs_mp
  (major_proof minor_proof : Proof) :
  Option Proof :=
  match unify_formulas_mp major_proof.formula minor_proof.formula with
  | some result =>
      let major_sigma := List.filter (fun (p : String × Formula_) => p.fst ∈ result.major.atom_list) result.sigma
      let minor_sigma := List.filter (fun (p : String × Formula_) => p.fst ∈ result.minor.atom_list) result.sigma
      some (mp
              (sub major_proof major_sigma result.major)
              (sub minor_proof minor_sigma result.minor)
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
