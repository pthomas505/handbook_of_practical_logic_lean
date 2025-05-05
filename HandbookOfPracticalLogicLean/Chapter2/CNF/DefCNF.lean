import HandbookOfPracticalLogicLean.Chapter2.Replace
import HandbookOfPracticalLogicLean.Chapter2.Semantics
import HandbookOfPracticalLogicLean.Chapter2.SubFormula
import HandbookOfPracticalLogicLean.Chapter2.TruthTable
import HandbookOfPracticalLogicLean.Chapter2.DNF.ListConj

import Mathlib.Tactic

import Init.Data.List.Basic
import Batteries.Data.HashMap

set_option autoImplicit false


open Formula_


theorem theorem_2_10
  (X : String)
  (P Q : Formula_)
  (h1 : ¬ atom_occurs_in X Q) :
  are_equisatisfiable (replace_atom_one_rec X Q P) (and_ (iff_ (atom_ X) Q) P) :=
  by
  unfold are_equisatisfiable
  unfold is_satisfiable
  unfold satisfies
  simp only [theorem_2_3_one]
  simp only [eval]
  simp only [bool_iff_prop_and]
  simp only [b_iff_eq_true]
  constructor
  · intro a1
    obtain ⟨V, a1⟩ := a1
    apply Exists.intro (Function.updateITE' V X (eval V Q))
    constructor
    · simp only [Function.updateITE']
      simp only [if_pos]
      apply theorem_2_2
      intro A a2
      unfold Function.updateITE'
      split_ifs
      case pos c2 =>
        rewrite [c2] at h1
        contradiction
      case neg c2 =>
        rfl
    · exact a1
  · intro a1
    obtain ⟨V, a1_left, a1_right⟩ := a1
    apply Exists.intro V
    simp only [← Function.updateITE_eq_Function.updateITE']
    simp only [Function.updateITE_same V X (eval V Q) a1_left]
    exact a1_right


-- https://avigad.github.io/lamr/decision_procedures_for_propositional_logic.html#the-tseitin-transformation

def mk_defs_aux
  (acc : Array Formula_) :
  Formula_ → (Formula_ × Array Formula_)
  | false_ => (false_, acc)
  | true_ => (true_, acc)
  | atom_ X =>
      (atom_ X, acc)
/-
      match acc.findIdx? (· = (atom_ X)) with
      | some n => (atom_ s!"def_{n}", acc)
      | none => (atom_ s!"def_{acc.size}", acc.push (atom_ X))
-/
  | not_ (atom_ X) =>
      (not_ (atom_ X), acc)
/-
      match acc.findIdx? (· = (atom_ X)) with
      | some n => (not_ (atom_ s!"def_{n}"), acc)
      | none => (not_ (atom_ s!"def_{acc.size}"), acc.push (atom_ X))
-/
  | and_ phi psi =>
      let (phi_def, phi_acc) := mk_defs_aux acc phi
      let (psi_def, psi_acc) := mk_defs_aux phi_acc psi
      match psi_acc.findIdx? (· = and_ phi_def psi_def) with
      | some n => (atom_ s!"def_{n}", psi_acc)
      | none => (atom_ s!"def_{psi_acc.size.repr}", psi_acc.push (and_ phi_def psi_def))
  | or_ phi psi =>
      let (phi_def, phi_acc) := mk_defs_aux acc phi
      let (psi_def, psi_acc) := mk_defs_aux phi_acc psi
      match psi_acc.findIdx? (· = or_ phi_def psi_def) with
      | some n => (atom_ s!"def_{n}", psi_acc)
      | none => (atom_ s!"def_{psi_acc.size.repr}", psi_acc.push (or_ phi_def psi_def))
  | F => (F, acc)


def mk_defs
  (F : Formula_) :
  (Formula_ × Array Formula_) :=
  mk_defs_aux #[] F


def print_defs
  (F : Formula_) :
  IO Unit := do
  let ⟨last, defs⟩ := mk_defs F
  IO.println s!"{last}, where"
  for i in [:defs.size] do
    IO.println s!"def_{i} := {defs[i]!}"


#eval print_defs (Formula_| ((((p /\ q) /\ ~ r) \/ (r /\ (~ p \/ ~ q))) /\ (~ s \/ (p /\ t))))


def defs_to_cnf_aux :
  List Formula_ → Nat → List Formula_
  | [], _ => []
  | hd :: tl, n => (or_ hd (not_ (atom_ s!"def_{n}"))) :: defs_to_cnf_aux tl (n + 1)


def to_cnf
  (F : Formula_) :
  Formula_ :=
  let ⟨last, defs⟩ := mk_defs F
  list_conj (last :: defs_to_cnf_aux defs.toList 0)


#eval (to_cnf (Formula_| ((((p /\ q) /\ ~ r) \/ (r /\ (~ p \/ ~ q))) /\ (~ s \/ (p /\ t))))).toString
