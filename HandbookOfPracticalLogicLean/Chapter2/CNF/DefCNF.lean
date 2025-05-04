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


def mk_defs
  (acc : Array Formula_) :
  Formula_ → (Formula_ × Array Formula_)
  | false_ => (false_, acc)
  | true_ => (true_, acc)
  | atom_ X => (atom_ X, acc)
/-
      match acc.findIdx? (· = (atom_ X)) with
      | some n => (atom_ n.repr, acc)
      | none => (atom_ acc.size.repr, acc.push (atom_ X))
-/
  | not_ (atom_ X) => (not_ (atom_ X), acc)
/-
      match acc.findIdx? (· = (atom_ X)) with
      | some n => (not_ (atom_ n.repr), acc)
      | none => (not_ (atom_ acc.size.repr), acc.push (atom_ X))
-/
  | and_ phi psi =>
      let (phi_def, phi_acc) := mk_defs acc phi
      let (psi_def, psi_acc) := mk_defs phi_acc psi
      match psi_acc.findIdx? (· = and_ phi_def psi_def) with
      | some n => (atom_ n.repr, psi_acc)
      | none => (atom_ psi_acc.size.repr, psi_acc.push (and_ phi_def psi_def))
  | or_ phi psi =>
      let (phi_def, phi_acc) := mk_defs acc phi
      let (psi_def, psi_acc) := mk_defs phi_acc psi
      match psi_acc.findIdx? (· = or_ phi_def psi_def) with
      | some n => (atom_ n.repr, psi_acc)
      | none => (atom_ psi_acc.size.repr, psi_acc.push (or_ phi_def psi_def))
  | F => (F, acc)


#eval (mk_defs #[] (Formula_| ((((p /\ q) /\ ~ r) \/ (r /\ (~ p \/ ~ q))) /\ (~ s \/ (p /\ t))))).snd
