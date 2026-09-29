import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Prop.Var
import HandbookOfPracticalLogicLean.Prop.Bool

import Mathlib.Tactic


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


open Formula_


/--
  The valuation of a formula as a function from strings to booleans.
  A function from the set of variables to the set of truth values `{false, true}`.
-/
def ValuationAsTotalFunction : Type := String → Bool
  deriving Inhabited


/--
  `eval σ F` := The evaluation of a formula `F` given the valuation `σ`.
-/
def eval
  (σ : ValuationAsTotalFunction) :
  Formula_ → Bool
  | false_ => false
  | true_ => true
  | var_ X => σ X
  | not_ phi => b_not (eval σ phi)
  | and_ phi psi => b_and (eval σ phi) (eval σ psi)
  | or_ phi psi => b_or (eval σ phi) (eval σ psi)
  | imp_ phi psi => b_imp (eval σ phi) (eval σ psi)
  | iff_ phi psi => b_iff (eval σ phi) (eval σ psi)


/--
  `satisfies σ F` := True if and only if the valuation `σ` satisfies the formula `F`.
-/
def satisfies
  (σ : ValuationAsTotalFunction)
  (F : Formula_) :
  Prop :=
  eval σ F = true

instance
  (σ : ValuationAsTotalFunction)
  (F : Formula_) :
  Decidable (satisfies σ F) :=
  by
  unfold satisfies
  infer_instance


/--
  `Formula_.is_tautology F` := True if and only if the formula `F` is a tautology.
-/
@[nolint defsWithUnderscore]
def Formula_.is_tautology
  (F : Formula_) :
  Prop :=
  ∀ (σ : ValuationAsTotalFunction), satisfies σ F


/--
  `Formula_.is_satisfiable F` := True if and only if the formula `F` is satisfiable.
-/
@[nolint defsWithUnderscore]
def Formula_.is_satisfiable
  (F : Formula_) :
  Prop :=
  ∃ (σ : ValuationAsTotalFunction), satisfies σ F


/--
  `Formula_.is_unsatisfiable F` := True if and only if the formula `F` is not satisfiable.
-/
@[nolint defsWithUnderscore]
def Formula_.is_unsatisfiable
  (F : Formula_) :
  Prop :=
  ¬ ∃ (σ : ValuationAsTotalFunction), satisfies σ F


/--
  `satisfies_set σ F` := True if and only if the valuation `σ` satisfies every formula in the set of formulas `Γ`.
-/
@[nolint defsWithUnderscore]
def satisfies_set
  (σ : ValuationAsTotalFunction)
  (Γ : Set Formula_) :
  Prop :=
  ∀ (F : Formula_), F ∈ Γ → satisfies σ F


/--
  `set_is_satisfiable Γ` := True if and only if the set of formulas `Γ` is satisfiable.
-/
@[nolint defsWithUnderscore]
def set_is_satisfiable
  (Γ : Set Formula_) :
  Prop :=
  ∃ (σ : ValuationAsTotalFunction), satisfies_set σ Γ


/--
  `set_is_unsatisfiable Γ` := True if and only if the set of formulas `Γ` is not satisfiable.
-/
@[nolint defsWithUnderscore]
def set_is_unsatisfiable
  (Γ : Set Formula_) :
  Prop :=
  ¬ ∃ (σ : ValuationAsTotalFunction), satisfies_set σ Γ


/--
  `entails Γ F` := True if and only if the set of formulas `Γ` entails the formula `F`.
-/
def entails
  (Γ : Set Formula_)
  (F : Formula_) :
  Prop :=
  ∀ (σ : ValuationAsTotalFunction), satisfies_set σ Γ → satisfies σ F


/--
  `is_logical_consequence P Q` := True if and only if the formula `Q` is a logical consequence of the formula `P`.
-/
@[nolint defsWithUnderscore]
def is_logical_consequence
  (P Q : Formula_) :
  Prop :=
  (P.imp_ Q).is_tautology


/--
  `are_logically_equivalent P Q` := True if and only if the formulas `P` and `Q` are logically equivalent.
-/
@[nolint defsWithUnderscore]
def are_logically_equivalent
  (P Q : Formula_) :
  Prop :=
  (P.iff_ Q).is_tautology


/--
  `are_equisatisfiable P Q` := True if and only if the formulas `P` and `Q` are equisatisfiable.
-/
@[nolint defsWithUnderscore]
def are_equisatisfiable
  (P Q : Formula_) :
  Prop :=
  P.is_satisfiable ↔ Q.is_satisfiable


/--
  `are_equivalid P Q` := True if and only if the formulas `P` and `Q` are equivalid.
-/
@[nolint defsWithUnderscore]
def are_equivalid
  (P Q : Formula_) :
  Prop :=
  P.is_tautology ↔ Q.is_tautology


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
  apply Iff.refl


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


theorem are_logically_equivalent_iff_eval_eq
  (P Q : Formula_) :
  are_logically_equivalent P Q ↔ ∀ (σ : ValuationAsTotalFunction), eval σ P = eval σ Q :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [b_iff_eq_true]


theorem are_logically_equivalent_false_iff
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


theorem are_logically_equivalent_true_iff
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


theorem are_logically_equivalent_to_false_iff_not_is_tautology
  (F : Formula_) :
  are_logically_equivalent F false_ ↔ (not_ F).is_tautology :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [b_iff_eq_true]
  simp only [b_not_eq_true]


theorem are_logically_equivalent_to_true_iff_is_tautology
  (F : Formula_) :
  are_logically_equivalent F true_ ↔ F.is_tautology :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [b_iff_eq_true]


-------------------------------------------------------------------------------


example
  (P Q : Formula_) :
  entails {P} Q ↔ is_logical_consequence P Q :=
  by
  unfold entails
  unfold satisfies_set
  unfold is_logical_consequence
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp only [bool_iff_prop_imp]
  simp only [Set.mem_singleton_iff]
  constructor
  · intro a1 σ a2
    apply a1
    intro F a3
    rewrite [a3]
    exact a2
  · intro a1 σ a2
    apply a1
    apply a2
    apply Eq.refl


example
  (P Q : Formula_) :
  are_logically_equivalent P Q ↔ (is_logical_consequence P Q ∧ is_logical_consequence Q P) :=
  by
  unfold are_logically_equivalent
  unfold is_logical_consequence
  unfold is_tautology
  unfold satisfies
  unfold eval
  simp only [bool_iff_prop_iff]
  simp only [bool_iff_prop_imp]
  constructor
  · intro a1
    constructor
    · intro σ a2
      rewrite [← a1]
      exact a2
    · intro σ a2
      rewrite [a1]
      exact a2
  · intro a1 σ
    obtain ⟨a1_left, a1_right⟩ := a1
    constructor
    · intro a2
      apply a1_left
      exact a2
    · intro a2
      apply a1_right
      exact a2


-------------------------------------------------------------------------------


theorem theorem_2_2
  (σ σ' : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : ∀ (V : String), var_occurs_in_formula V F → (σ V = σ' V)) :
  eval σ F = eval σ' F :=
  by
  induction F
  all_goals
    unfold eval
  case false_ | true_ =>
    apply Eq.refl
  case var_ X =>
    apply h1
    unfold var_occurs_in_formula
    apply Eq.refl
  case not_ phi ih =>
    unfold var_occurs_in_formula at h1

    congr 1
    apply ih
    intro V a1
    apply h1
    exact a1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h1

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
  The valuation of a formula as a function from strings to optional booleans.
  A function from the set of variables to the set of optional truth values `{false, true}`.
-/
def ValuationAsPartialFunction : Type := String → Option Bool
  deriving Inhabited


/--
  `eval σ F` := The evaluation of a formula `F` given the valuation `σ`.
-/
def eval
  (σ : ValuationAsPartialFunction) :
  Formula_ → Option Bool
  | false_ => some false
  | true_ => some true
  | var_ X => σ X
  | not_ phi => do
    let val_phi ← eval σ phi
    b_not val_phi
  | and_ phi psi => do
    let val_phi ← eval σ phi
    let val_psi ← eval σ psi
    b_and val_phi val_psi
  | or_ phi psi => do
    let val_phi ← eval σ phi
    let val_psi ← eval σ psi
    b_or val_phi val_psi
  | imp_ phi psi => do
    let val_phi ← eval σ phi
    let val_psi ← eval σ psi
    b_imp val_phi val_psi
  | iff_ phi psi => do
    let val_phi ← eval σ phi
    let val_psi ← eval σ psi
    b_iff val_phi val_psi


/--
  `satisfies σ F` := True if and only if the valuation `σ` satisfies the formula `F`.
-/
def satisfies
  (σ : ValuationAsPartialFunction)
  (F : Formula_) :
  Prop :=
  eval σ F = some true

instance
  (σ : ValuationAsPartialFunction)
  (F : Formula_) :
  Decidable (satisfies σ F) :=
  by
  unfold satisfies
  infer_instance


/--
  `Formula_.is_tautology F` := True if and only if the formula `F` is a tautology.
-/
@[nolint defsWithUnderscore]
def Formula_.is_tautology
  (F : Formula_) :
  Prop :=
  ∀ (σ : ValuationAsPartialFunction), ((∀ (V : String), var_occurs_in_formula V F → ¬ σ V = none) → satisfies σ F)


/--
  `valuation_as_list_of_pairs_to_valuation_as_partial_function l` := Translates the list of string and boolean pairs `l` to a function that maps each string that occurs in a pair in `l` to `some` of the leftmost boolean value that it is paired with, and each string that does not occur in a pair in `l` to `none`.
-/
@[nolint defsWithUnderscore]
def valuation_as_list_of_pairs_to_valuation_as_partial_function :
  List (String × Bool) → ValuationAsPartialFunction
  | [] => fun _ => none
  | hd :: tl => Function.updateITE (valuation_as_list_of_pairs_to_valuation_as_partial_function tl) hd.fst (some hd.snd)


#eval (eval (valuation_as_list_of_pairs_to_valuation_as_partial_function [("P", true)]) (var_ "P"))
#eval (eval (valuation_as_list_of_pairs_to_valuation_as_partial_function [("P", false)]) (var_ "P"))
#eval (eval (valuation_as_list_of_pairs_to_valuation_as_partial_function [("P", true)]) (not_ (var_ "P")))
#eval (eval (valuation_as_list_of_pairs_to_valuation_as_partial_function [("P", false)]) (not_ (var_ "P")))
#eval (eval (valuation_as_list_of_pairs_to_valuation_as_partial_function [("P", false), ("Q", false)]) (and_ (var_ "P") (var_ "Q")))
#eval (eval (valuation_as_list_of_pairs_to_valuation_as_partial_function [("P", false), ("Q", true)]) (and_ (var_ "P") (var_ "Q")))
#eval (eval (valuation_as_list_of_pairs_to_valuation_as_partial_function [("P", true), ("Q", false)]) (and_ (var_ "P") (var_ "Q")))
#eval (eval (valuation_as_list_of_pairs_to_valuation_as_partial_function [("P", true), ("Q", true)]) (and_ (var_ "P") (var_ "Q")))
#eval (eval (valuation_as_list_of_pairs_to_valuation_as_partial_function [("P", true)]) (var_ "Q"))


end Option_


example
  (σ_opt : Option_.ValuationAsPartialFunction)
  (σ : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : ∀ (V : String), var_occurs_in_formula V F → σ_opt V = some (σ V)) :
  Option_.eval σ_opt F = some (eval σ F) :=
  by
  induction F
  case false_ | true_ =>
    unfold Option_.eval
    unfold eval
    apply Eq.refl
  case var_ X =>
    unfold var_occurs_in_formula at h1

    unfold Option_.eval
    unfold eval
    apply h1
    apply Eq.refl
  case not_ phi ih =>
    unfold var_occurs_in_formula at h1

    unfold Option_.eval
    unfold eval
    rewrite [ih h1]
    simp only [Option.bind_eq_bind, Option.bind_some]
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h1

    have s1 : ∀ (V : String), var_occurs_in_formula V phi → σ_opt V = some (σ V) :=
    by
      intro V a1
      apply h1
      left
      exact a1

    have s2 : ∀ (V : String), var_occurs_in_formula V psi → σ_opt V = some (σ V) :=
    by
      intro V a1
      apply h1
      right
      exact a1

    unfold Option_.eval
    unfold eval
    rewrite [phi_ih s1]
    rewrite [psi_ih s2]
    simp only [Option.bind_eq_bind, Option.bind_some]


/--
  `val_to_opt_val σ` := The conversion of the valuation function `σ` to an option valued valuation function.
-/
@[nolint defsWithUnderscore]
def val_to_opt_val
  (σ : ValuationAsTotalFunction) :
  Option_.ValuationAsPartialFunction :=
  fun (V : String) => some (σ V)


/--
  `opt_val_to_val σ_opt` := The conversion of the option valued valuation function `σ_opt` to a valuation function.
-/
@[nolint defsWithUnderscore]
def opt_val_to_val
  (σ_opt : Option_.ValuationAsPartialFunction) :
  ValuationAsTotalFunction :=
  fun (V : String) =>
    match σ_opt V with
    | some b => b
    | none => default


theorem val_to_opt_val_eq_some_val
  (σ : ValuationAsTotalFunction)
  (V : String) :
  (val_to_opt_val σ) V = some (σ V) :=
  by
  unfold val_to_opt_val
  apply Eq.refl


theorem opt_val_eq_some_opt_val_to_val
  (σ_opt : Option_.ValuationAsPartialFunction)
  (V : String)
  (h1 : ¬ σ_opt V = none) :
  σ_opt V = some ((opt_val_to_val σ_opt) V) :=
  by
  cases c1 : σ_opt V
  case none =>
    contradiction
  case some b =>
    unfold opt_val_to_val
    rewrite [c1]
    dsimp only


theorem eval_opt_val_to_val
  (σ_opt : Option_.ValuationAsPartialFunction)
  (F : Formula_)
  (h1 : ∀ (V : String), var_occurs_in_formula V F → ¬ σ_opt V = none) :
  Option_.eval σ_opt F = some (eval (opt_val_to_val σ_opt) F) :=
  by
  induction F
  case false_ | true_ =>
    unfold Option_.eval
    unfold eval
    apply Eq.refl
  case var_ X =>
    unfold var_occurs_in_formula at h1

    unfold Option_.eval
    unfold eval
    apply opt_val_eq_some_opt_val_to_val
    apply h1
    apply Eq.refl
  case not_ phi ih =>
    unfold var_occurs_in_formula at h1

    unfold Option_.eval
    unfold eval
    rewrite [ih h1]
    simp only [Option.bind_eq_bind, Option.bind_some]
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h1

    have s1 : ∀ (V : String), var_occurs_in_formula V phi → ¬ σ_opt V = none :=
    by
      intro V a1
      apply h1
      left
      exact a1

    have s2 : ∀ (V : String), var_occurs_in_formula V psi → ¬ σ_opt V = none :=
    by
      intro V a1
      apply h1
      right
      exact a1

    unfold Option_.eval
    unfold eval
    rewrite [phi_ih s1]
    rewrite [psi_ih s2]
    simp only [Option.bind_eq_bind, Option.bind_some]


theorem eval_val_to_opt_val
  (σ : ValuationAsTotalFunction)
  (F : Formula_) :
  Option_.eval (val_to_opt_val σ) F = some (eval σ F) :=
  by
  induction F
  case false_ | true_ =>
    unfold Option_.eval
    unfold eval
    apply Eq.refl
  case var_ X =>
    unfold Option_.eval
    unfold eval
    unfold val_to_opt_val
    apply Eq.refl
  case not_ phi ih =>
    unfold Option_.eval
    unfold eval
    rewrite [ih]
    simp only [Option.bind_eq_bind, Option.bind_some]
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold Option_.eval
    unfold eval
    rewrite [phi_ih]
    rewrite [psi_ih]
    simp only [Option.bind_eq_bind, Option.bind_some]


example
  (F : Formula_)
  (h1 : F.is_tautology) :
  Option_.Formula_.is_tautology F :=
  by
  unfold is_tautology at h1
  unfold satisfies at h1

  unfold Option_.Formula_.is_tautology
  unfold Option_.satisfies
  intro σ_opt a1
  rewrite [← h1 (opt_val_to_val σ_opt)]
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
  intro σ
  rewrite [← Option.some.injEq]
  rewrite [← eval_val_to_opt_val σ F]
  apply h1
  intro V a1
  unfold val_to_opt_val
  intro contra
  contradiction


#lint
