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


-------------------------------------------------------------------------------


example
  (V_opt : Prop_.Option_.Valuation)
  (V : Prop_.Valuation)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → V_opt A = Option.some (V A)) :
  Prop_.Option_.eval V_opt F = Option.some (Prop_.eval V F) :=
  by
  induction F
  case false_ | true_ =>
    unfold Option_.eval
    unfold eval
    rfl
  case atom_ X =>
    unfold Option_.eval
    unfold eval
    apply h1
    unfold atom_occurs_in
    rfl
  case not_ phi ih =>
    unfold atom_occurs_in at h1

    unfold Option_.eval
    unfold eval
    rewrite [ih h1]
    simp
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold atom_occurs_in at h1

    have s1 : (∀ (A : String), atom_occurs_in A phi → V_opt A = some (V A)) :=
    by
      intro A a1
      apply h1
      tauto

    have s2 : (∀ (A : String), atom_occurs_in A psi → V_opt A = some (V A)) :=
    by
      intro A a1
      apply h1
      tauto

    unfold Option_.eval
    unfold eval
    rewrite [phi_ih s1]
    rewrite [psi_ih s2]
    simp


def option_bool_to_option_prop :
  Option Bool → Option Prop
  | some false => some False
  | some true => some True
  | none => none


example
  (V_bool : Prop_.Bool_.Valuation)
  (V_prop : Prop_.Valuation)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → ((V_bool A = true) ↔ V_prop A)) :
  (Prop_.Bool_.eval V_bool F = true) ↔ Prop_.eval V_prop F :=
  by
  induction F
  case false_ | true_ =>
    unfold Bool_.eval
    unfold eval
    tauto
  case atom_ X =>
    unfold Bool_.eval
    unfold eval
    apply h1
    unfold atom_occurs_in
    rfl
  case not_ phi ih =>
    unfold atom_occurs_in at h1

    unfold Bool_.eval
    unfold eval
    rewrite [← ih h1]
    cases c1 : Bool_.eval V_bool phi
    case false =>
      simp only [Bool_.b_not]
      tauto
    case true =>
      simp only [Bool_.b_not]
      tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold atom_occurs_in at h1

    have s1 : (∀ (A : String), atom_occurs_in A phi → (V_bool A = true ↔ V_prop A)) :=
    by
      intro A a1
      apply h1
      tauto

    specialize phi_ih s1

    have s2 : (∀ (A : String), atom_occurs_in A psi → (V_bool A = true ↔ V_prop A)) :=
    by
      intro A a1
      apply h1
      tauto

    specialize psi_ih s2

    unfold Bool_.eval
    unfold eval
    rewrite [← phi_ih]
    rewrite [← psi_ih]

    cases c1 : Bool_.eval V_bool phi
    case false =>
      cases c2 : Bool_.eval V_bool psi
      case false =>
        first | simp only [Bool_.b_and] | simp only [Bool_.b_or] | simp only [Bool_.b_imp]
        tauto
      case true =>
        first | simp only [Bool_.b_and]
        tauto
    case true =>
      cases c2 : Bool_.eval V_bool psi
      case false =>
        first | simp only [Bool_.b_and]
        tauto
      case true =>
        first | simp only [Bool_.b_and]
        tauto


--#lint
