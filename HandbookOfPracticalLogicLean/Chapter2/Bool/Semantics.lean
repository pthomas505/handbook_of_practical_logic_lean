import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.Bool.Atom
import HandbookOfPracticalLogicLean.Chapter2.Bool.Bool

import Mathlib.Tactic


set_option autoImplicit false


namespace Bool_


open Formula_


/--
  A function from the set of atoms to the set of truth values `{false, true}`.
-/
def ValuationAsTotalFunction : Type := String → Bool
  deriving Inhabited


/--
  `eval V F` := The evaluation of a formula `F` given the valuation `V`.
-/
def eval
  (V : ValuationAsTotalFunction) :
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
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  Prop :=
  eval V F = true

instance
  (V : ValuationAsTotalFunction)
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
  ∀ (V : ValuationAsTotalFunction), satisfies V F


/--
  `Formula_.is_satisfiable F` := True if and only if the formula `F` is satisfiable.
-/
def Formula_.is_satisfiable
  (F : Formula_) :
  Prop :=
  ∃ (V : ValuationAsTotalFunction), satisfies V F


/--
  `Formula_.is_unsatisfiable F` := True if and only if the formula `F` is not satisfiable.
-/
def Formula_.is_unsatisfiable
  (F : Formula_) :
  Prop :=
  ¬ ∃ (V : ValuationAsTotalFunction), satisfies V F


/--
  `set_is_satisfiable Γ` := True if and only if there exists a valuation that simultaneously satisfies every formula in the set of formulas `Γ`.
-/
def set_is_satisfiable
  (Γ : Set Formula_) :
  Prop :=
  ∃ (V : ValuationAsTotalFunction), ∀ (F : Formula_), F ∈ Γ → satisfies V F


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
  are_logically_equivalent P Q ↔ ∀ (V : ValuationAsTotalFunction), eval V P = eval V Q :=
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


lemma are_logically_equivalent_to_false_iff_not_is_tautology
  (F : Formula_) :
  are_logically_equivalent F false_ ↔ (not_ F).is_tautology :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [b_iff_eq_true]
  simp only [b_not_eq_true]


lemma are_logically_equivalent_to_true_iff_is_tautology
  (F : Formula_) :
  are_logically_equivalent F true_ ↔ F.is_tautology :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [b_iff_eq_true]


-------------------------------------------------------------------------------


theorem theorem_2_2
  (V V' : ValuationAsTotalFunction)
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
    unfold atom_occurs_in at h1

    congr 1
    apply ih
    intro X a1
    apply h1
    exact a1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold atom_occurs_in at h1

    congr 1
    · apply phi_ih
      intro X a1
      apply h1
      left
      exact a1
    · apply psi_ih
      intro X a1
      apply h1
      right
      exact a1


-------------------------------------------------------------------------------


namespace Option_


/--
  A partial function from the set of atoms to the set of truth values `{false, true}`.
-/
def ValuationAsTotalFunction : Type := String → Option Bool
  deriving Inhabited


/--
  `eval V F` := The evaluation of a formula `F` given the valuation `V` as a partial function.
-/
def eval
  (V : ValuationAsTotalFunction) :
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
  `satisfies V F` := True if and only if the valuation `V` satisfies the formula `F`.
-/
def satisfies
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  Prop :=
  eval V F = some true

instance
  (V : ValuationAsTotalFunction)
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
  ∀ (V : ValuationAsTotalFunction), ((∀ (A : String), atom_occurs_in A F → ¬ V A = none) → satisfies V F)


/--
  `gen_valuation` := The generation of a valuation function from a list of pairs of atoms and truth values.
-/
def gen_valuation :
  List (String × Bool) → ValuationAsTotalFunction
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
  (V_opt : Option_.ValuationAsTotalFunction)
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → V_opt A = some (V A)) :
  Option_.eval V_opt F = some (eval V F) :=
  by
  induction F
  case false_ | true_ =>
    unfold Option_.eval
    unfold eval
    rfl
  case atom_ X =>
    unfold atom_occurs_in at h1

    unfold Option_.eval
    unfold eval
    apply h1
    rfl
  case not_ phi ih =>
    unfold atom_occurs_in at h1

    unfold Option_.eval
    unfold eval
    rewrite [ih h1]
    simp only [Option.bind_eq_bind, Option.some_bind]
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
      left
      exact a1

    have s2 : (∀ (A : String), atom_occurs_in A psi → V_opt A = some (V A)) :=
    by
      intro A a1
      apply h1
      right
      exact a1

    unfold Option_.eval
    unfold eval
    rewrite [phi_ih s1]
    rewrite [psi_ih s2]
    simp only [Option.bind_eq_bind, Option.some_bind]


def val_to_opt_val
  (V : ValuationAsTotalFunction) :
  Option_.ValuationAsTotalFunction :=
  fun (A : String) => some (V A)


def opt_val_to_val
  (V_opt : Option_.ValuationAsTotalFunction) :
  ValuationAsTotalFunction :=
  fun (A : String) =>
    match V_opt A with
    | some b => b
    | none => default


lemma val_to_opt_val_eq_some_val
  (V : ValuationAsTotalFunction)
  (A : String) :
  (val_to_opt_val V) A = some (V A) :=
  by
  unfold val_to_opt_val
  rfl


lemma opt_val_eq_some_opt_val_to_val
  (V_opt : Option_.ValuationAsTotalFunction)
  (A : String)
  (h1 : ¬ V_opt A = none) :
  V_opt A = some ((opt_val_to_val V_opt) A) :=
  by
  cases c1 : V_opt A
  case none =>
    contradiction
  case some b =>
    unfold opt_val_to_val
    rewrite [c1]
    dsimp only


lemma eval_opt_val_to_val
  (V_opt : Option_.ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → ¬ V_opt A = none) :
  Option_.eval V_opt F = some (eval (opt_val_to_val V_opt) F) :=
  by
  induction F
  case false_ | true_ =>
    unfold Option_.eval
    unfold eval
    rfl
  case atom_ X =>
    unfold Option_.eval
    unfold eval
    apply opt_val_eq_some_opt_val_to_val
    apply h1
    unfold atom_occurs_in
    rfl
  case not_ phi ih =>
    unfold atom_occurs_in at h1
    specialize ih h1

    unfold Option_.eval
    unfold eval
    rewrite [ih]
    simp only [Option.bind_eq_bind, Option.some_bind]
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold atom_occurs_in at h1

    have s1 : ∀ (A : String), atom_occurs_in A phi → ¬ V_opt A = none :=
    by
      intro A a1
      apply h1
      left
      exact a1

    have s2 : ∀ (A : String), atom_occurs_in A psi → ¬ V_opt A = none :=
    by
      intro A a1
      apply h1
      right
      exact a1

    specialize phi_ih s1
    specialize psi_ih s2

    unfold Option_.eval
    unfold eval
    rewrite [phi_ih]
    rewrite [psi_ih]
    simp only [Option.bind_eq_bind, Option.some_bind]


lemma eval_val_to_opt_val
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  Option_.eval (val_to_opt_val V) F = some (eval V F) :=
  by
  induction F
  case false_ | true_ =>
    unfold Option_.eval
    unfold eval
    rfl
  case atom_ X =>
    unfold Option_.eval
    unfold eval
    unfold val_to_opt_val
    rfl
  case not_ phi ih =>
    unfold Option_.eval
    unfold eval
    rewrite [ih]
    simp only [Option.bind_eq_bind, Option.some_bind]
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold Option_.eval
    unfold eval
    rewrite [phi_ih]
    rewrite [psi_ih]
    simp only [Option.bind_eq_bind, Option.some_bind]


example
  (F : Formula_)
  (h1 : F.is_tautology) :
  Option_.Formula_.is_tautology F :=
  by
  unfold is_tautology at h1
  unfold satisfies at h1

  unfold Option_.Formula_.is_tautology
  unfold Option_.satisfies
  intro V_opt a1
  specialize h1 (opt_val_to_val V_opt)
  rewrite [← h1]
  apply eval_opt_val_to_val
  exact a1


example
  (F : Formula_)
  (h1 : Option_.Formula_.is_tautology F) :
  F.is_tautology :=
  by
  unfold Option_.Formula_.is_tautology at h1
  unfold Option_.satisfies at h1

  unfold is_tautology
  unfold satisfies
  intro V
  specialize h1 (val_to_opt_val V)
  rewrite [eval_val_to_opt_val V F] at h1
  have s1 : some (eval V F) = some true :=
  by
    apply h1
    intro A a1
    unfold val_to_opt_val
    intro contra
    contradiction
  simp only [Option.some.injEq] at s1
  exact s1


--#lint
