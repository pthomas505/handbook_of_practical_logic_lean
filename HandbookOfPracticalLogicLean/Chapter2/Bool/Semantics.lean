import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.Bool.Atom

import Mathlib.Tactic


set_option autoImplicit false


namespace Prop_


open Formula_


/--
  The truth table definition of boolean `not`.
-/
def b_not : Bool → Bool
| false => true
| true => false

/--
  The truth table definition of boolean `and`.
-/
def b_and : Bool → Bool → Bool
| false, false => false
| false, true => false
| true, false => false
| true, true => true

/--
  The truth table definition of boolean `or`.
-/
def b_or : Bool → Bool → Bool
| false, false => false
| false, true => true
| true, false => true
| true, true => true

/--
  The truth table definition of boolean `imp`.
-/
def b_imp : Bool → Bool → Bool
| false, false => true
| false, true => true
| true, false => false
| true, true => true

/--
  The truth table definition of boolean `iff`.
-/
def b_iff : Bool → Bool → Bool
| false, false => true
| false, true => false
| true, false => false
| true, true => true


lemma bool_iff_prop_not
  (b : Bool) :
  (b_not b = true) ↔ ¬ (b = true) :=
  by
  cases b
  all_goals
    simp only [b_not]
    tauto


lemma bool_iff_prop_and
  (b1 b2 : Bool) :
  (b_and b1 b2 = true) ↔ ((b1 = true) ∧ (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      simp only [b_and]
      tauto


lemma bool_iff_prop_or
  (b1 b2 : Bool) :
  (b_or b1 b2 = true) ↔ ((b1 = true) ∨ (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      simp only [b_or]
      tauto


lemma bool_iff_prop_imp
  (b1 b2 : Bool) :
  (b_imp b1 b2 = true) ↔ ((b1 = true) → (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      simp only [b_imp]
      tauto


lemma bool_iff_prop_iff
  (b1 b2 : Bool) :
  (b_iff b1 b2 = true) ↔ ((b1 = true) ↔ (b2 = true)) :=
  by
  cases b1
  all_goals
    cases b2
    all_goals
      simp only [b_iff]
    all_goals
      tauto


-------------------------------------------------------------------------------


lemma b_iff_rfl
  (b : Bool) :
  b_iff b b = true :=
  by
  cases b
  · simp only [b_iff]
  · simp only [b_iff]


lemma b_not_eq_false
  (b : Bool) :
  (b_not b = false ↔ b = true) :=
  by
  constructor
  · intro a1
    cases b
    · simp only [b_not] at a1
      cases a1
    · rfl
  · intro a1
    cases b
    · cases a1
    · simp only [b_not]


lemma b_not_eq_true
  (b : Bool) :
  (b_not b = true ↔ b = false) :=
  by
  constructor
  · intro a1
    cases b
    · rfl
    · simp only [b_not] at a1
      cases a1
  · intro a1
    cases b
    · simp only [b_not]
    · cases a1


lemma b_iff_eq_false
  (b1 b2 : Bool) :
  (b_iff b1 b2 = false) ↔ ¬ (b1 = b2) :=
  by
  constructor
  · intro a1
    cases b1
    · cases b2
      · simp only [b_iff] at a1
        cases a1
      · intro contra
        cases contra
    · cases b2
      · intro contra
        cases contra
      · simp only [b_iff] at a1
        cases a1
  · intro a1
    cases b1
    · cases b2
      · exfalso
        apply a1
        rfl
      · simp only [b_iff]
    · cases b2
      · simp only [b_iff]
      · exfalso
        apply a1
        rfl


lemma b_iff_eq_true
  (b1 b2 : Bool) :
  (b_iff b1 b2 = true) ↔ (b1 = b2) :=
  by
  constructor
  · intro a1
    cases b1
    · cases b2
      · rfl
      · simp only [b_iff] at a1
        cases a1
    · cases b2
      · simp only [b_iff] at a1
        cases a1
      · rfl
  · intro a1
    rewrite [a1]
    apply b_iff_rfl


/--
  A function from the set of atoms to the set of truth values `{false, true}`.
-/
def Valuation : Type := String → Bool
  deriving Inhabited


/--
  `eval V F` := The evaluation of a formula `F` given the valuation `V`.
-/
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


/--
  `satisfies V F` := True if and only if the valuation `V` satisfies the formula `F`.
-/
def satisfies
  (V : Valuation)
  (F : Formula_) :
  Prop :=
  eval V F = true

instance
  (V : Valuation)
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


-------------------------------------------------------------------------------


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
  F.is_unsatisfiable ↔ ¬ F.is_satisfiable :=
  by
  unfold is_unsatisfiable
  unfold is_satisfiable
  rfl


example
  (F : Formula_) :
  ¬ F.is_unsatisfiable ↔ F.is_satisfiable :=
  by
  unfold is_unsatisfiable
  unfold is_satisfiable
  exact not_not


example
  (F : Formula_) :
  (not_ F).is_unsatisfiable ↔ F.is_tautology :=
  by
  unfold is_unsatisfiable
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [bool_iff_prop_not]
  exact not_exists_not


example
  (F : Formula_) :
  F.is_unsatisfiable ↔ (not_ F).is_tautology :=
  by
  unfold is_unsatisfiable
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [bool_iff_prop_not]
  exact not_exists


-------------------------------------------------------------------------------


lemma are_logically_equivalent_iff_eval_eq
  (P Q : Formula_) :
  are_logically_equivalent P Q ↔ ∀ (V : Valuation), eval V P = eval V Q :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [b_iff_eq_true]


lemma are_logically_equivalent_false_iff
  (F : Formula_) :
  are_logically_equivalent F false_ ↔
  are_logically_equivalent (not_ F) true_ :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [b_iff_eq_true]
  simp only [b_not_eq_true]


lemma are_logically_equivalent_true_iff
  (F : Formula_) :
  are_logically_equivalent F true_ ↔
  are_logically_equivalent (not_ F) false_ :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [b_iff_eq_true]
  simp only [b_not_eq_false]


lemma not_is_tautology_iff_logically_equivalent_to_false
  (F : Formula_) :
  (not_ F).is_tautology ↔ are_logically_equivalent F false_ :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [b_iff_eq_true]
  simp only [b_not_eq_true]


lemma is_tautology_iff_logically_equivalent_to_true
  (F : Formula_) :
  F.is_tautology ↔ are_logically_equivalent F true_ :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [b_iff_eq_true]


-------------------------------------------------------------------------------


theorem theorem_2_2
  (V V' : Valuation)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → (V A = V' A)) :
  eval V F = eval V' F :=
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


/--
  A partial function from the set of atoms to the set of truth values `{false, true}`.
-/
def Valuation : Type := String → Option Bool
  deriving Inhabited


/--
  `eval V F` := The evaluation of a formula `F` given the valuation `V` as a partial function.
-/
def eval
  (V : Valuation) :
  Formula_ → Option Bool
  | false_ => some false
  | true_ => some true
  | atom_ X => V X
  | not_ phi => do
    let val_phi ← eval V phi
    b_not val_phi
  | and_ phi psi => do
    let val_phi ← eval V phi
    let val_psi ← eval V psi
    b_and val_phi val_psi
  | or_ phi psi => do
    let val_phi ← eval V phi
    let val_psi ← eval V psi
    b_or val_phi val_psi
  | imp_ phi psi => do
    let val_phi ← eval V phi
    let val_psi ← eval V psi
    b_imp val_phi val_psi
  | iff_ phi psi => do
    let val_phi ← eval V phi
    let val_psi ← eval V psi
    b_iff val_phi val_psi


/--
  `gen_valuation` := The generation of a valuation function from a list of pairs of atoms and truth values.
-/
def gen_valuation :
  List (String × Bool) → Valuation
  | [] => fun _ => Option.none
  | hd :: tl => Function.updateITE (gen_valuation tl) hd.fst (Option.some hd.snd)


#eval (eval (gen_valuation [("P", true)]) (atom_ "P"))
#eval (eval (gen_valuation [("P", false)]) (atom_ "P"))
#eval (eval (gen_valuation [("P", true)]) (not_ (atom_ "P")))
#eval (eval (gen_valuation [("P", false)]) (not_ (atom_ "P")))
#eval (eval (gen_valuation [("P", false), ("Q", false)]) (and_ (atom_ "P") (atom_ "Q")))
#eval (eval (gen_valuation [("P", false), ("Q", true)]) (and_ (atom_ "P") (atom_ "Q")))
#eval (eval (gen_valuation [("P", true), ("Q", false)]) (and_ (atom_ "P") (atom_ "Q")))
#eval (eval (gen_valuation [("P", true), ("Q", true)]) (and_ (atom_ "P") (atom_ "Q")))
#eval (eval (gen_valuation [("P", true)]) (atom_ "Q"))


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


#lint
