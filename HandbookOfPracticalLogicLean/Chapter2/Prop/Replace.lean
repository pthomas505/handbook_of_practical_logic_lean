import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.Prop.Semantics

import Mathlib.Tactic


set_option autoImplicit false


namespace Prop_


open Formula_


/--
  `replace_atom_one_rec A F P` :=

  `A → F` in `P` for each occurrence of the atom `A` in the formula `P`

  The result of simultaneously replacing each occurrence of the atom `A` in the formula `P` by an occurrence of the formula `F`.
-/
def replace_atom_one_rec
  (A : String)
  (F : Formula_ ) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | atom_ X => if A = X then F else atom_ X
  | not_ phi => not_ (replace_atom_one_rec A F phi)
  | and_ phi psi => and_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)
  | or_ phi psi => or_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)
  | imp_ phi psi => imp_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)
  | iff_ phi psi => iff_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)


theorem theorem_2_3_one
  (V : Valuation)
  (A : String)
  (P : Formula_)
  (F : Formula_) :
  eval V (replace_atom_one_rec A P F) ↔ eval (Function.updateITE' V A (eval V P)) F :=
  by
  induction F
  case false_ | true_ =>
    simp only [eval]
  case atom_ X =>
    simp only [eval]
    unfold replace_atom_one_rec
    unfold Function.updateITE'
    split_ifs
    · rfl
    · unfold eval
      rfl
  case not_ phi ih =>
    simp only [eval]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


theorem corollary_2_4_one
  (A : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : F.is_tautology) :
  ((replace_atom_one_rec A P F)).is_tautology :=
  by
  unfold is_tautology at h1
  unfold satisfies at h1

  unfold is_tautology
  unfold satisfies
  intro V
  rewrite [theorem_2_3_one]
  apply h1


theorem theorem_2_5_one
  (V : Valuation)
  (P Q : Formula_)
  (X : String)
  (R : Formula_)
  (h1 : eval V P ↔ eval V Q) :
  eval V (replace_atom_one_rec X P R) ↔ eval V (replace_atom_one_rec X Q R) :=
  by
  simp only [theorem_2_3_one]
  rewrite [h1]
  rfl


theorem corollary_2_6_one
  (V : Valuation)
  (P Q : Formula_)
  (X : String)
  (R : Formula_)
  (h1 : are_logically_equivalent P Q) :
  eval V (replace_atom_one_rec X P R) ↔ eval V (replace_atom_one_rec X Q R) :=
  by
  simp only [are_logically_equivalent_iff_eval_eq_all_val] at h1

  apply theorem_2_5_one
  apply h1


/--
  `replace_atom_all_rec τ F` := The simultaneous replacement of each occurrence of any atom `A` in the formula `F` by `τ A`.
-/
def replace_atom_all_rec
  (τ : String → Formula_) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | atom_ X => τ X
  | not_ phi => not_ (replace_atom_all_rec τ phi)
  | and_ phi psi => and_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)
  | or_ phi psi => or_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)
  | imp_ phi psi => imp_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)
  | iff_ phi psi => iff_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)


theorem theorem_2_3_all
  (V : Valuation)
  (τ : String → Formula_)
  (F : Formula_) :
  eval V (replace_atom_all_rec τ F) ↔ eval (eval V ∘ τ) F :=
  by
  induction F
  case false_ | true_ =>
    simp only [eval]
  case atom_ X =>
    unfold replace_atom_all_rec
    simp only [eval]
    rfl
  case not_ phi ih =>
    simp only [eval]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


theorem corollary_2_4_all
  (τ : String → Formula_)
  (F : Formula_)
  (h1 : F.is_tautology) :
  (replace_atom_all_rec τ F).is_tautology :=
  by
  unfold is_tautology at h1
  unfold satisfies at h1

  unfold is_tautology
  unfold satisfies
  intro V
  rewrite [theorem_2_3_all]
  apply h1


theorem theorem_2_5_all
  (V : Valuation)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (X : String), eval V (τ1 X) ↔ eval V (τ2 X)) :
  eval V (replace_atom_all_rec τ1 F) ↔ eval V (replace_atom_all_rec τ2 F) :=
  by
    simp only [theorem_2_3_all]
    congr! 1
    funext X
    simp only [Function.comp_apply]
    ext
    apply h1


theorem corollary_2_6_all
  (V : Valuation)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (X : String), are_logically_equivalent (τ1 X) (τ2 X)) :
  eval V (replace_atom_all_rec τ1 F) ↔ eval V (replace_atom_all_rec τ2 F) :=
  by
  simp only [are_logically_equivalent_iff_eval_eq_all_val] at h1

  apply theorem_2_5_all
  intro X
  apply h1


/--
  `is_repl_of_formula_in_formula_fun U V P_u P_v` := True if and only if `P_v` is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of `U` in `P_u` by occurrences of `V`.
-/
def is_repl_of_formula_in_formula_fun
  (U V : Formula_) :
  Formula_ → Formula_ → Prop
  | not_ P_u, not_ P_v =>
    not_ P_u = not_ P_v ∨ (not_ P_u = U ∧ not_ P_v = V) ∨
    is_repl_of_formula_in_formula_fun U V P_u P_v

  | and_ P_u Q_u, and_ P_v Q_v =>
    and_ P_u Q_u = and_ P_v Q_v ∨ (and_ P_u Q_u = U ∧ and_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_fun U V P_u P_v ∧ is_repl_of_formula_in_formula_fun U V Q_u Q_v

  | or_ P_u Q_u, or_ P_v Q_v =>
    or_ P_u Q_u = or_ P_v Q_v ∨ (or_ P_u Q_u = U ∧ or_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_fun U V P_u P_v ∧ is_repl_of_formula_in_formula_fun U V Q_u Q_v

  | imp_ P_u Q_u, imp_ P_v Q_v =>
    imp_ P_u Q_u = imp_ P_v Q_v ∨ (imp_ P_u Q_u = U ∧ imp_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_fun U V P_u P_v ∧ is_repl_of_formula_in_formula_fun U V Q_u Q_v

  | iff_ P_u Q_u, iff_ P_v Q_v =>
    iff_ P_u Q_u = iff_ P_v Q_v ∨ (iff_ P_u Q_u = U ∧ iff_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_fun U V P_u P_v ∧ is_repl_of_formula_in_formula_fun U V Q_u Q_v

  | P_u, P_v => P_u = P_v ∨ (P_u = U ∧ P_v = V)

instance (U V F F' : Formula_) : Decidable (is_repl_of_formula_in_formula_fun U V F F') :=
  by
  induction F generalizing F'
  all_goals
    cases F'
    all_goals
      simp only [is_repl_of_formula_in_formula_fun]
      infer_instance


/--
  `is_repl_of_formula_in_formula U V P_u P_v` := True if and only if `P_v` is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of `U` in `P_u` by occurrences of `V`.
-/
inductive is_repl_of_formula_in_formula
  (U V : Formula_) :
  Formula_ → Formula_ → Prop

    -- not replacing an occurrence
  | same_
    (P_u P_v : Formula_) :
    P_u = P_v →
    is_repl_of_formula_in_formula U V P_u P_v

    -- replacing an occurrence
  | diff_
    (P_u P_v : Formula_) :
    P_u = U →
    P_v = V →
    is_repl_of_formula_in_formula U V P_u P_v

  | not_
    (P_u P_v : Formula_) :
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V P_u.not_ P_v.not_

  | and_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V Q_u Q_v →
    is_repl_of_formula_in_formula U V (P_u.and_ Q_u) (P_v.and_ Q_v)

  | or_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V Q_u Q_v →
    is_repl_of_formula_in_formula U V (P_u.or_ Q_u) (P_v.or_ Q_v)

  | imp_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V Q_u Q_v →
    is_repl_of_formula_in_formula U V (P_u.imp_ Q_u) (P_v.imp_ Q_v)

  | iff_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V Q_u Q_v →
    is_repl_of_formula_in_formula U V (P_u.iff_ Q_u) (P_v.iff_ Q_v)


lemma is_repl_of_formula_in_formula_fun_imp_is_repl_of_formula_in_formula
  (U V : Formula_)
  (F F' : Formula_)
  (h1 : is_repl_of_formula_in_formula_fun U V F F') :
  is_repl_of_formula_in_formula U V F F' :=
  by
  induction F generalizing F'
  all_goals
    cases F'
  case
      true_.true_
    | false_.false_ =>
    apply is_repl_of_formula_in_formula.same_
    rfl
  case atom_.atom_ X X' =>
    unfold is_repl_of_formula_in_formula_fun at h1
    cases h1
    case inl h1 =>
      apply is_repl_of_formula_in_formula.same_
      exact h1
    case inr h1 =>
      obtain ⟨h1_left, h1_right⟩ := h1
      apply is_repl_of_formula_in_formula.diff_
      · exact h1_left
      · exact h1_right
  case not_.not_ phi ih phi' =>
    unfold is_repl_of_formula_in_formula_fun at h1
    cases h1
    case inl h1 =>
      apply is_repl_of_formula_in_formula.same_
      exact h1
    case inr h1 =>
      cases h1
      case inl h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1
        apply is_repl_of_formula_in_formula.diff_
        · exact h1_left
        · exact h1_right
      case inr h1 =>
        apply is_repl_of_formula_in_formula.not_
        apply ih
        exact h1
  case
      and_.and_ phi psi phi_ih psi_ih phi' psi'
    | or_.or_ phi psi phi_ih psi_ih phi' psi'
    | imp_.imp_ phi psi phi_ih psi_ih phi' psi'
    | iff_.iff_ phi psi phi_ih psi_ih phi' psi' =>
    unfold is_repl_of_formula_in_formula_fun at h1
    cases h1
    case inl h1 =>
      apply is_repl_of_formula_in_formula.same_
      exact h1
    case inr h1 =>
      cases h1
      case inl h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1
        apply is_repl_of_formula_in_formula.diff_
        · exact h1_left
        · exact h1_right
      case inr h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1

        first
          | apply is_repl_of_formula_in_formula.and_
          | apply is_repl_of_formula_in_formula.or_
          | apply is_repl_of_formula_in_formula.imp_
          | apply is_repl_of_formula_in_formula.iff_
        · apply phi_ih
          exact h1_left
        · apply psi_ih
          exact h1_right

  all_goals
    unfold is_repl_of_formula_in_formula_fun at h1
    cases h1
    case _ h1 =>
      cases h1
    case _ h1 =>
      obtain ⟨h1_left, h1_right⟩ := h1
      apply is_repl_of_formula_in_formula.diff_
      · exact h1_left
      · exact h1_right


lemma is_repl_of_formula_in_formula_imp_is_repl_of_formula_in_formula_fun
  (U V : Formula_)
  (F F' : Formula_)
  (h1 : is_repl_of_formula_in_formula U V F F') :
  is_repl_of_formula_in_formula_fun U V F F' :=
  by
  induction h1
  case same_ P_u P_v h1_ih =>
    induction P_u generalizing P_v
    all_goals
      cases P_v
      all_goals
        simp only [is_repl_of_formula_in_formula_fun]
        tauto
  case diff_ P_u P_v h1_ih_1 h1_ih_2 =>
    induction P_u generalizing P_v
    all_goals
      cases P_v
      all_goals
        simp only [is_repl_of_formula_in_formula_fun]
        tauto
  all_goals
    simp only [is_repl_of_formula_in_formula_fun]
    tauto


lemma is_repl_of_formula_in_formula_fun_iff_is_repl_of_formula_in_formula
  (U V : Formula_)
  (F F' : Formula_) :
  is_repl_of_formula_in_formula_fun U V F F' ↔ is_repl_of_formula_in_formula U V F F' :=
  by
  constructor
  · apply is_repl_of_formula_in_formula_fun_imp_is_repl_of_formula_in_formula
  · apply is_repl_of_formula_in_formula_imp_is_repl_of_formula_in_formula_fun


example
  (V : Valuation)
  (R S : Formula_)
  (P_R P_S : Formula_)
  (h1 : is_repl_of_formula_in_formula R S P_R P_S)
  (h2 : eval V R ↔ eval V S) :
  eval V P_R ↔ eval V P_S :=
  by
  induction h1
  case same_ P_u P_v ih =>
    rewrite [ih]
    rfl
  case diff_ P_u P_v ih_1 ih_2 =>
    rewrite [ih_1]
    rewrite [ih_2]
    exact h2
  case not_ P_u P_v ih_1 ih_2 =>
    unfold eval
    rewrite [ih_2]
    rfl
  case
      and_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4
    | or_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4
    | imp_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4
    | iff_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4 =>
    unfold eval
    rewrite [ih_3]
    rewrite [ih_4]
    rfl


#lint
