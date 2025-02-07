import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.Bool.Formula

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


example
  (P Q : Formula_) :
  are_logically_equivalent P Q ↔ ∀ (V : Valuation), eval V P ↔ eval V Q :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]


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

--#eval (eval (gen_valuation [("P", True)]) (atom_ "P"))


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


/-
def gen_valuation :
  List (String × Bool) → Valuation
  | [] => fun _ => Option.none
  | hd :: tl => Function.updateITE (gen_valuation tl) hd.fst (Option.some hd.snd)
-/

--#lint
