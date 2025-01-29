import HandbookOfPracticalLogicLean.Chapter2.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


def PropValuation : Type := String → Prop
  deriving Inhabited


def eval
  (V : PropValuation) :
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
  (V : PropValuation)
  [DecidablePred V]
  (F : Formula_) :
  Decidable (eval V F) :=
  by
  induction F
  all_goals
    simp only [eval]
    infer_instance


def satisfies
  (V : PropValuation)
  (F : Formula_) :
  Prop :=
  eval V F

def Formula_.is_tautology
  (F : Formula_) :
  Prop :=
  ∀ (V : PropValuation), satisfies V F

def Formula_.is_satisfiable
  (F : Formula_) :
  Prop :=
  ∃ (V : PropValuation), satisfies V F

def Formula_.is_unsatisfiable
  (F : Formula_) :
  Prop :=
  ¬ ∃ (V : PropValuation), satisfies V F


example
  (F : Formula_)
  (h1 : F.is_tautology) :
  F.is_satisfiable :=
  by
  unfold is_tautology at h1

  unfold is_satisfiable
  apply Exists.intro default
  apply h1


def set_is_satisfiable
  (Γ : Set Formula_) :
  Prop :=
  ∃ (V : PropValuation), ∀ (F : Formula_), F ∈ Γ → satisfies V F


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
  (P Q : Formula_)
  (h1 : are_logically_equivalent P Q) :
  ∀ (V : PropValuation), eval V P ↔ eval V Q :=
  by
  unfold are_logically_equivalent at h1
  unfold is_tautology at h1
  unfold satisfies at h1
  unfold eval at h1
  exact h1
