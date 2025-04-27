import HandbookOfPracticalLogicLean.Chapter2.Replace
import HandbookOfPracticalLogicLean.Chapter2.Semantics
import HandbookOfPracticalLogicLean.Chapter2.SubFormula
import HandbookOfPracticalLogicLean.Chapter2.DNF.ListConj
import HandbookOfPracticalLogicLean.Chapter2.DNF.GenAllValuations

import Mathlib.Tactic

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



def er
  (index : Nat)
  (map : Batteries.HashMap Formula_ Formula_) :
  List Formula_ → (Nat × Batteries.HashMap Formula_ Formula_)
  | [] => (index, map)
  | hd :: tl =>
    match hd with
    | false_ => (index, map.insert false_ false_)
    | true_ => (index, map.insert true_ true_)
    | atom_ X => er index (map.insert (atom_ X) (atom_ X)) tl
    | F => er (index + 1) (map.insert F (atom_ index.repr)) tl


#eval (er 1 (Batteries.mkHashMap) [atom_ "a", atom_ "b"]).snd.toList

#eval let F : Formula_ := (and_ (or_ (atom_ "p") (and_ (atom_ "q") (not_ (atom_ "r")) )) (atom_ "s")); (er 1 (Batteries.mkHashMap) (List.filter (fun (P : Formula_) => (¬ P.is_constant)) F.subformula_list)).snd.toList.toString


def meh
  (map : Batteries.HashMap Formula_ Formula_) :
  Formula_ → Option (List (List (Formula_)))
  | false_ => Option.some [[false_]]
  | true_ => Option.some [[true_]]
  | atom_ X => Option.some []
  | not_ phi => do
    let phi_atom ← map.find? phi
    let current_atom ← map.find? (not_ phi)
    let disj_1 := or_ phi_atom current_atom
    let disj_2 := or_ (not_ current_atom) (not_ phi_atom)
    let phi_result ← meh map phi
    Option.some ([[disj_1, disj_2]] ++ phi_result)
  | and_ phi psi => do
    let phi_atom ← map.find? phi
    let psi_atom ← map.find? psi
    let current_atom ← map.find? (and_ phi psi)
    let disj_1 := or_ (not_ phi_atom) (or_ (not_ psi_atom) current_atom)
    let disj_2 := or_ (not_ current_atom) phi_atom
    let disj_3 := or_ (not_ current_atom) psi_atom
    let phi_result ← meh map phi
    let psi_result ← meh map psi
    Option.some ([[disj_1, disj_2, disj_3]] ++ phi_result ++ psi_result)
  | or_ phi psi => do
    let phi_atom ← map.find? phi
    let psi_atom ← map.find? psi
    let current_atom ← map.find? (or_ phi psi)
    let disj_1 := or_ (not_ phi_atom) current_atom
    let disj_2 := or_ (not_ psi_atom) current_atom
    let disj_3 := or_ (not_ current_atom) (or_ (phi_atom) psi_atom)
    let phi_result ← meh map phi
    let psi_result ← meh map psi
    Option.some ([[disj_1, disj_2, disj_3]] ++ phi_result ++ psi_result)
  | _ => Option.none


def hmm
  (F : Formula_) :
  String :=
  let map := er 1 Batteries.mkHashMap (List.filter (fun (P : Formula_) => (¬ P.is_constant)) F.subformula_list)
  match meh map.snd F with
  | Option.some P => P.toString
  | Option.none => "error"

#eval let F : Formula_ := (not_ (and_ (atom_ "p") (or_ (atom_ "q") (not_ (atom_ "r"))))); hmm F

#eval let F : Formula_ := (and_ (or_ (atom_ "p") (and_ (atom_ "q") (not_ (atom_ "r")) )) (atom_ "s")); hmm F
