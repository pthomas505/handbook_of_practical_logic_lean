import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Prop.Var
import HandbookOfPracticalLogicLean.Prop.Bool

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  The valuation of a formula as a function from strings to booleans.
  A function from the set of variables to the set of truth values `{false, true}`.
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
  | var_ X => V X
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
  `satisfies_set V F` := True if and only if the valuation `V` satisfies every formula in the set of formulas `Γ`.
-/
def satisfies_set
  (V : ValuationAsTotalFunction)
  (Γ : Set Formula_) :
  Prop :=
  ∀ (F : Formula_), F ∈ Γ → satisfies V F


/--
  `set_is_satisfiable Γ` := True if and only if the set of formulas `Γ` is satisfiable.
-/
def set_is_satisfiable
  (Γ : Set Formula_) :
  Prop :=
  ∃ (V : ValuationAsTotalFunction), satisfies_set V Γ


/--
  `set_is_unsatisfiable Γ` := True if and only if the set of formulas `Γ` is not satisfiable.
-/
def set_is_unsatisfiable
  (Γ : Set Formula_) :
  Prop :=
  ¬ ∃ (V : ValuationAsTotalFunction), satisfies_set V Γ


/--
  `entails Γ F` := True if and only if the set of formulas `Γ` entails the formula `F`.
-/
def entails
  (Γ : Set Formula_)
  (F : Formula_) :
  Prop :=
  ∀ (V : ValuationAsTotalFunction), satisfies_set V Γ → satisfies V F


/--
  `is_logical_consequence P Q` := True if and only if the formula `Q` is a logical consequence of the formula `P`.
-/
def is_logical_consequence
  (P Q : Formula_) :
  Prop :=
  (P.imp_ Q).is_tautology


/--
  `are_logically_equivalent P Q` := True if and only if the formulas `P` and `Q` are logically equivalent.
-/
def are_logically_equivalent
  (P Q : Formula_) :
  Prop :=
  (P.iff_ Q).is_tautology


/--
  `are_equisatisfiable P Q` := True if and only if the formulas `P` and `Q` are equisatisfiable.
-/
def are_equisatisfiable
  (P Q : Formula_) :
  Prop :=
  P.is_satisfiable ↔ Q.is_satisfiable


/--
  `are_equivalid P Q` := True if and only if the formulas `P` and `Q` are equivalid.
-/
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
  · intro a1 V a2
    apply a1
    intro F a3
    rewrite [a3]
    exact a2
  · intro a1 V a2
    apply a1
    apply a2
    rfl


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
    · intro V a2
      rewrite [← a1]
      exact a2
    · intro V a2
      rewrite [a1]
      exact a2
  · intro a1 V
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
  (V V' : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : ∀ (A : String), var_occurs_in_formula A F → (V A = V' A)) :
  eval V F = eval V' F :=
  by
  induction F
  all_goals
    unfold eval
  case false_ | true_ =>
    rfl
  case var_ X =>
    apply h1
    unfold var_occurs_in_formula
    rfl
  case not_ phi ih =>
    unfold var_occurs_in_formula at h1

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
  `eval V F` := The evaluation of a formula `F` given the valuation `V`.
-/
def eval
  (V : ValuationAsPartialFunction) :
  Formula_ → Option Bool
  | false_ => some false
  | true_ => some true
  | var_ X => V X
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
  (V : ValuationAsPartialFunction)
  (F : Formula_) :
  Prop :=
  eval V F = some true

instance
  (V : ValuationAsPartialFunction)
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
  ∀ (V : ValuationAsPartialFunction), ((∀ (A : String), var_occurs_in_formula A F → ¬ V A = none) → satisfies V F)


/--
  `valuation_as_list_of_pairs_to_valuation_as_partial_function l` := Translates the list of string and boolean pairs `l` to a function that maps each string that occurs in a pair in `l` to `some` of the leftmost boolean value that it is paired with, and each string that does not occur in a pair in `l` to `none`.
-/
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
  (V_opt : Option_.ValuationAsPartialFunction)
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : ∀ (A : String), var_occurs_in_formula A F → V_opt A = some (V A)) :
  Option_.eval V_opt F = some (eval V F) :=
  by
  induction F
  case false_ | true_ =>
    unfold Option_.eval
    unfold eval
    rfl
  case var_ X =>
    unfold var_occurs_in_formula at h1

    unfold Option_.eval
    unfold eval
    apply h1
    rfl
  case not_ phi ih =>
    unfold var_occurs_in_formula at h1

    unfold Option_.eval
    unfold eval
    rewrite [ih h1]
    simp only [Option.bind_eq_bind, Option.some_bind]
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h1

    have s1 : ∀ (A : String), var_occurs_in_formula A phi → V_opt A = some (V A) :=
    by
      intro A a1
      apply h1
      left
      exact a1

    have s2 : ∀ (A : String), var_occurs_in_formula A psi → V_opt A = some (V A) :=
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


/--
  `val_to_opt_val V` := The conversion of the valuation function `V` to an option valued valuation function.
-/
def val_to_opt_val
  (V : ValuationAsTotalFunction) :
  Option_.ValuationAsPartialFunction :=
  fun (A : String) => some (V A)


/--
  `opt_val_to_val V_opt` := The conversion of the option valued valuation function `V_opt` to a valuation function.
-/
def opt_val_to_val
  (V_opt : Option_.ValuationAsPartialFunction) :
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
  (V_opt : Option_.ValuationAsPartialFunction)
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
    rfl


lemma eval_opt_val_to_val
  (V_opt : Option_.ValuationAsPartialFunction)
  (F : Formula_)
  (h1 : ∀ (A : String), var_occurs_in_formula A F → ¬ V_opt A = none) :
  Option_.eval V_opt F = some (eval (opt_val_to_val V_opt) F) :=
  by
  induction F
  case false_ | true_ =>
    unfold Option_.eval
    unfold eval
    rfl
  case var_ X =>
    unfold var_occurs_in_formula at h1

    unfold Option_.eval
    unfold eval
    apply opt_val_eq_some_opt_val_to_val
    apply h1
    rfl
  case not_ phi ih =>
    unfold var_occurs_in_formula at h1

    unfold Option_.eval
    unfold eval
    rewrite [ih h1]
    simp only [Option.bind_eq_bind, Option.some_bind]
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h1

    have s1 : ∀ (A : String), var_occurs_in_formula A phi → ¬ V_opt A = none :=
    by
      intro A a1
      apply h1
      left
      exact a1

    have s2 : ∀ (A : String), var_occurs_in_formula A psi → ¬ V_opt A = none :=
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
  case var_ X =>
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
  rewrite [← h1 (opt_val_to_val V_opt)]
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
  rewrite [← Option.some.injEq]
  rewrite [← eval_val_to_opt_val V F]
  apply h1
  intro A a1
  unfold val_to_opt_val
  intro contra
  contradiction


#lint
