import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.Prop.Atom

import Mathlib.Tactic


set_option autoImplicit false


namespace Prop_


open Formula_


/--
  A function from the set of atoms to the set of truth values `{False, True}`.
-/
def Valuation : Type := String → Prop
  deriving Inhabited


/--
  `eval V F` := True if and only if the formula `F` evaluates to `True` given the valuation `V`.
-/
def eval
  (V : Valuation) :
  Formula_ → Prop
  | false_ => False
  | true_ => True
  | atom_ X => V X
  | not_ phi => ¬ eval V phi
  | and_ phi psi => eval V phi ∧ eval V psi
  | or_ phi psi => eval V phi ∨ eval V psi
  | imp_ phi psi => eval V phi → eval V psi
  | iff_ phi psi => eval V phi ↔ eval V psi

instance
  (V : Valuation)
  [DecidablePred V]
  (F : Formula_) :
  Decidable (eval V F) :=
  by
  induction F
  all_goals
    simp only [eval]
    infer_instance


/--
  `satisfies V F` := True if and only if the valuation `V` satisfies the formula `F`.
-/
def satisfies
  (V : Valuation)
  (F : Formula_) :
  Prop :=
  eval V F

instance
  (V : Valuation)
  [DecidablePred V]
  (F : Formula_) :
  Decidable (satisfies V F) :=
  by
  unfold satisfies
  infer_instance


/--
  `Formula_.is_tautology F` := True if and only if the formula `F` is a tautology.
-/
def Formula_.is_tautology
  (F : Formula_) :
  Prop :=
  ∀ (V : Valuation), satisfies V F


/--
  `Formula_.is_satisfiable F` := True if and only if the formula `F` is satisfiable.
-/
def Formula_.is_satisfiable
  (F : Formula_) :
  Prop :=
  ∃ (V : Valuation), satisfies V F


/--
  `Formula_.is_unsatisfiable F` := True if and only if the formula `F` is not satisfiable.
-/
def Formula_.is_unsatisfiable
  (F : Formula_) :
  Prop :=
  ¬ ∃ (V : Valuation), satisfies V F


/--
  `set_is_satisfiable Γ` := True if and only if there exists a valuation that simultaneously satisfies every formula in the set of formulas `Γ`.
-/
def set_is_satisfiable
  (Γ : Set Formula_) :
  Prop :=
  ∃ (V : Valuation), ∀ (F : Formula_), F ∈ Γ → satisfies V F


/--
  `is_logical_consequence P Q` := True if and only if `Q` is a logical consequence of `P`.
-/
def is_logical_consequence
  (P Q : Formula_) :
  Prop :=
  (P.imp_ Q).is_tautology


/--
  `are_logically_equivalent P Q` := True if and only if `P` and `Q` are logically equivalent.
-/
def are_logically_equivalent
  (P Q : Formula_) :
  Prop :=
  (P.iff_ Q).is_tautology


example
  (F : Formula_)
  (h1 : F.is_tautology) :
  F.is_satisfiable :=
  by
  unfold is_tautology at h1

  unfold is_satisfiable
  apply Exists.intro default
  apply h1


example
  (F : Formula_) :
  (not_ F).is_unsatisfiable ↔ F.is_tautology :=
  by
  unfold is_tautology
  unfold is_unsatisfiable
  unfold satisfies
  simp only [eval]
  exact not_exists_not


example
  (F : Formula_) :
  F.is_unsatisfiable ↔ (not_ F).is_tautology :=
  by
  unfold is_unsatisfiable
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  exact not_exists


example
  (F : Formula_) :
  ¬ F.is_unsatisfiable ↔ F.is_satisfiable :=
  by
  unfold is_satisfiable
  unfold is_unsatisfiable
  exact not_not


lemma are_logically_equivalent_iff_eval_eq_all_val
  (P Q : Formula_) :
  are_logically_equivalent P Q ↔ ∀ (V : Valuation), eval V P ↔ eval V Q :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]


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


namespace Option_


def Valuation : Type := String → Option Prop
  deriving Inhabited


def eval
  (V : Valuation) :
  Formula_ → Option Prop
  | false_ => some False
  | true_ => some True
  | atom_ X => V X
  | not_ phi => do
    let val_phi ← eval V phi
    ¬ val_phi
  | and_ phi psi => do
    let val_phi ← eval V phi
    let val_psi ← eval V psi
    val_phi ∧ val_psi
  | or_ phi psi => do
    let val_phi ← eval V phi
    let val_psi ← eval V psi
    val_phi ∨ val_psi
  | imp_ phi psi => do
    let val_phi ← eval V phi
    let val_psi ← eval V psi
    val_phi → val_psi
  | iff_ phi psi => do
    let val_phi ← eval V phi
    let val_psi ← eval V psi
    val_phi ↔ val_psi


def gen_valuation :
  List (String × Prop) → Valuation
  | [] => fun _ => Option.none
  | hd :: tl => Function.updateITE (gen_valuation tl) hd.fst (Option.some hd.snd)


end Option_


example
  (V_opt : Option_.Valuation)
  (V : Valuation)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → V_opt A = Option.some (V A)) :
  Option_.eval V_opt F = Option.some (eval V F) :=
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


-------------------------------------------------------------------------------


namespace Bool_


def b_not : Bool → Bool
| false => true
| true => false

def b_and : Bool → Bool → Bool
| false, false => false
| false, true => false
| true, false => false
| true, true => true

def b_or : Bool → Bool → Bool
| false, false => false
| false, true => true
| true, false => true
| true, true => true

def b_imp : Bool → Bool → Bool
| false, false => true
| false, true => true
| true, false => false
| true, true => true

def b_iff : Bool → Bool → Bool
| false, false => true
| false, true => false
| true, false => false
| true, true => true


def Valuation : Type := String → Bool
  deriving Inhabited


def eval
  (V : Valuation) :
  Formula_ → Bool
  | false_ => false
  | true_ => true
  | atom_ X => V X
  | not_ phi => b_not (eval V phi)
  | and_ phi psi => b_and (eval V phi) (eval V psi)
  | or_ phi psi => b_or (eval V phi) (eval V psi)
  | imp_ phi psi => b_imp (eval V phi) (eval V psi)
  | iff_ phi psi => b_iff (eval V phi) (eval V psi)


end Bool_


example
  (V_bool : Bool_.Valuation)
  (V : Valuation)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → ((V_bool A = true) ↔ V A)) :
  (Bool_.eval V_bool F = true) ↔ eval V F :=
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

    have s1 : (∀ (A : String), atom_occurs_in A phi → (V_bool A = true ↔ V A)) :=
    by
      intro A a1
      apply h1
      tauto

    specialize phi_ih s1

    have s2 : (∀ (A : String), atom_occurs_in A psi → (V_bool A = true ↔ V A)) :=
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
