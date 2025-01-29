import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


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


theorem theorem_2_2
  (V V' : PropValuation)
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


def replace_atom_one_rec
  (A : String)
  (F : Formula_ ):
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
  (V : PropValuation)
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
  (V : PropValuation)
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
  (V : PropValuation)
  (P Q : Formula_)
  (X : String)
  (R : Formula_)
  (h1 : are_logically_equivalent P Q) :
  eval V (replace_atom_one_rec X P R) ↔ eval V (replace_atom_one_rec X Q R) :=
  by
  unfold are_logically_equivalent at h1
  unfold is_tautology at h1
  unfold satisfies at h1
  unfold eval at h1

  apply theorem_2_5_one
  apply h1


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
  (V : PropValuation)
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
  (V : PropValuation)
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
  (V : PropValuation)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (X : String), are_logically_equivalent (τ1 X) (τ2 X)) :
  eval V (replace_atom_all_rec τ1 F) ↔ eval V (replace_atom_all_rec τ2 F) :=
  by
  unfold are_logically_equivalent at h1
  unfold is_tautology at h1
  unfold satisfies at h1
  unfold eval at h1

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
  (V : PropValuation)
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


def Formula_.has_dual :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ phi => phi.has_dual
  | and_ phi psi => phi.has_dual ∧ psi.has_dual
  | or_ phi psi => phi.has_dual ∧ psi.has_dual
  | _ => False

instance
  (F : Formula_) :
  Decidable (has_dual F) :=
  by
  induction F
  all_goals
    simp only [has_dual]
    infer_instance


def Formula_.dual :
  Formula_ → Formula_
  | false_ => true_
  | true_ => false_
  | atom_ X => atom_ X
  | not_ phi => not_ phi.dual
  | and_ phi psi => or_ phi.dual psi.dual
  | or_ phi psi => and_ phi.dual psi.dual
  | imp_ phi psi => imp_ phi.dual psi.dual
  | iff_ phi psi => iff_ phi.dual psi.dual


example
  (F : Formula_) :
  dual (dual F) = F :=
  by
  induction F
  all_goals
    simp only [dual]
  case not_ phi ih =>
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


theorem theorem_2_7
  (V : PropValuation)
  (F : Formula_)
  (h1 : has_dual F) :
  eval V (dual F) ↔ Not (eval (Not ∘ V) F) :=
  by
  induction F
  all_goals
    unfold dual
    unfold eval
  case false_ =>
    itauto
  case true_ =>
    itauto
  case atom_ X =>
    simp only [Function.comp_apply]
    tauto
  case not_ phi ih =>
    unfold has_dual at h1

    rewrite [ih h1]
    itauto
  case and_ phi psi phi_ih psi_ih =>
    unfold has_dual at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    rewrite [phi_ih h1_left]
    rewrite [psi_ih h1_right]
    tauto
  case or_ phi psi phi_ih psi_ih =>
    unfold has_dual at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    rewrite [phi_ih h1_left]
    rewrite [psi_ih h1_right]
    itauto
  all_goals
    unfold has_dual at h1
    contradiction


theorem corollary_2_8_a
  (P Q : Formula_)
  (h1 : are_logically_equivalent P Q)
  (h2 : has_dual P)
  (h3 : has_dual Q) :
  are_logically_equivalent (dual P) (dual Q) :=
  by
  unfold are_logically_equivalent at h1
  unfold is_tautology at h1
  unfold satisfies at h1
  unfold eval at h1

  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  intro V
  unfold eval
  rewrite [theorem_2_7 V P h2]
  rewrite [theorem_2_7 V Q h3]
  congr! 1
  apply h1


lemma is_tautology_iff_logically_equivalent_to_true
  (F : Formula_) :
  F.is_tautology ↔ are_logically_equivalent F true_ :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp


example
  (F : Formula_) :
  are_logically_equivalent F false_ ↔ are_logically_equivalent (not_ F) true_ :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  simp


theorem corollary_2_8_b
  (F : Formula_)
  (h1 : F.is_tautology)
  (h2 : has_dual F) :
  (not_ (dual F)).is_tautology :=
  by
  rewrite [is_tautology_iff_logically_equivalent_to_true] at h1

  obtain s1 := corollary_2_8_a F true_ h1 h2
  simp only [has_dual] at s1
  simp only [dual] at s1
  simp at s1

  unfold are_logically_equivalent at s1
  unfold is_tautology at s1
  unfold satisfies at s1
  simp only [eval] at s1

  unfold is_tautology
  unfold satisfies
  unfold eval
  intro V
  rewrite [s1]
  simp


def is_subformula
  (F : Formula_) :
  Formula_ → Prop
  | false_ => F = false_
  | true_ => F = true_
  | atom_ X => F = atom_ X
  | not_ phi =>
    F = not_ phi ∨
    is_subformula F phi
  | and_ phi psi =>
    F = and_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi
  | or_ phi psi =>
    F = or_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi
  | imp_ phi psi =>
    F = imp_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi
  | iff_ phi psi =>
    F = iff_ phi psi ∨
    is_subformula F phi ∨
    is_subformula F psi

instance
  (F F' : Formula_) :
  Decidable (is_subformula F F') :=
  by
  induction F'
  all_goals
    simp only [is_subformula]
    infer_instance


lemma not_is_subformula_imp_not_equal
  (F F' : Formula_)
  (h1 : ¬ is_subformula F F') :
  ¬ F' = F :=
  by
  cases F'
  all_goals
    simp only [is_subformula] at h1
    tauto


def is_proper_subformula
  (F F' : Formula_) :
  Prop :=
  is_subformula F F' ∧ ¬ F = F'

instance
  (F F' : Formula_) :
  Decidable (is_proper_subformula F F') :=
  by
  unfold is_proper_subformula
  infer_instance


def simplify_aux :
  Formula_ → Formula_
  | not_ false_ => true_
  | not_ true_ => false_
  | not_ (not_ phi) => phi
  | and_ _ false_ => false_
  | and_ false_ _ => false_
  | and_ phi true_ => phi
  | and_ true_ phi => phi
  | or_ phi false_ => phi
  | or_ false_ phi => phi
  | or_ _ true_ => true_
  | or_ true_ _ => true_
  | imp_ false_ _ => true_
  | imp_ _ true_ => true_
  | imp_ true_ phi => phi
  | imp_ phi false_ => not_ phi
  | iff_ phi true_ => phi
  | iff_ true_ phi => phi
  | iff_ phi false_ => not_ phi
  | iff_ false_ phi => not_ phi
  | phi => phi


def simplify_aux_and :
  Formula_ → Formula_
  | and_ _ false_ => false_
  | and_ false_ _ => false_
  | and_ phi true_ => phi
  | and_ true_ phi => phi
  | phi => phi


example
  (F : Formula_) :
  simplify_aux_and (and_ F false_) = false_ :=
  by
  simp only [simplify_aux_and]


example
  (F : Formula_) :
  simplify_aux_and (and_ false_ F) = false_ :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi h1 =>
    rfl
  case _ phi psi h1 h2 =>
    rfl
  case _ phi psi h1 h2 =>
    cases h2
    rfl
  case _ phi psi h1 h2 h3 =>
    cases h3
  · tauto


example
  (F : Formula_) :
  simplify_aux_and (and_ true_ F) = F :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi h1 =>
    cases h1
    rfl
  case _ phi psi h1 h2 =>
    cases h2
  case _ phi psi h1 h2 =>
    cases h2
    rfl
  case _ phi psi h1 h2 h3 =>
    cases h3
    rfl
  · tauto


example
  (F : Formula_) :
  simplify_aux_and (and_ F true_) = F :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi h1 =>
    cases h1
  case _ phi psi h1 h2 =>
    cases h2
    rfl
  case _ phi psi h1 h2 =>
    cases h2
    rfl
  case _ phi psi h1 h2 h3 =>
    cases h3
    rfl
  · tauto


example
  (P Q : Formula_)
  (h1 : ¬ P = false_)
  (h2 : ¬ P = true_)
  (h3 : ¬ Q = false_)
  (h4 : ¬ Q = true_) :
  simplify_aux_and (and_ P Q) = and_ P Q :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi ih_1 =>
    cases ih_1
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    contradiction
  · tauto


lemma simplify_aux_is_logically_equivalent
  (V : PropValuation)
  (F : Formula_) :
  eval V F ↔ eval V (simplify_aux F) :=
  by
  cases F
  case false_ | true_ | atom_ X =>
    simp only [simplify_aux]
  case not_ phi =>
    cases phi
    all_goals
      simp only [simplify_aux]
    all_goals
      simp only [eval]
      tauto
  case
      and_ phi psi
    | or_ phi psi
    | imp_ phi psi
    | iff_ phi psi =>
    cases phi
    all_goals
      cases psi
      all_goals
        simp only [simplify_aux]
      all_goals
        simp only [eval]
      all_goals
        tauto


def simplify :
  Formula_ → Formula_
  | not_ phi => simplify_aux (not_ (simplify phi))
  | and_ phi psi => simplify_aux (and_ (simplify phi) (simplify psi))
  | or_ phi psi => simplify_aux (or_ (simplify phi) (simplify psi))
  | imp_ phi psi => simplify_aux (imp_ (simplify phi) (simplify psi))
  | iff_ phi psi => simplify_aux (iff_ (simplify phi) (simplify psi))
  | phi => phi


lemma simplify_is_logically_equivalent
  (V : PropValuation)
  (F : Formula_) :
  eval V F ↔ eval V (simplify F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    rfl
  case not_ phi ih =>
    simp only [simplify]
    rewrite [← simplify_aux_is_logically_equivalent]
    simp only [eval]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [simplify]
    rewrite [← simplify_aux_is_logically_equivalent]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


example
  (F : Formula_) :
  are_logically_equivalent F (simplify F) :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  intro V
  unfold satisfies
  unfold eval
  apply simplify_is_logically_equivalent


def Formula_.is_literal :
  Formula_ → Prop
  | atom_ _ => True
  | not_ (atom_ _) => True
  | _ => False

def Formula_.is_negative_literal :
  Formula_ → Prop
  | not_ (atom_ _) => True
  | _ => False

def Formula_.is_positive_literal :
  Formula_ → Prop
  | atom_ _ => True
  | _ => False

def negate_literal :
  Formula_ → Formula_
  | atom_ X => not_ (atom_ X)
  | not_ (atom_ X) => atom_ X
  | phi => phi

def Formula_.is_nnf :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_nnf ∧ psi.is_nnf
  | or_ phi psi => phi.is_nnf ∧ psi.is_nnf
  | _ => False


-------------------------------------------------------------------------------


mutual
def to_nnf_v1 :
  Formula_ → Formula_
  | not_ phi => to_nnf_neg_v1 phi
  | and_ phi psi => and_ (to_nnf_v1 phi) (to_nnf_v1 psi)
  | or_ phi psi => or_ (to_nnf_v1 phi) (to_nnf_v1 psi)
  | imp_ phi psi => or_ (to_nnf_neg_v1 phi) (to_nnf_v1 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v1 phi) (to_nnf_v1 psi)) (and_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi))
  | phi => phi

def to_nnf_neg_v1 :
  Formula_ → Formula_
  | false_ => true_
  | true_ => false_
  | not_ phi => to_nnf_v1 phi
  | and_ phi psi => or_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi)
  | or_ phi psi => and_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi)
  | imp_ phi psi => and_ (to_nnf_v1 phi) (to_nnf_neg_v1 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v1 phi) (to_nnf_neg_v1 psi)) (and_ (to_nnf_neg_v1 phi) (to_nnf_v1 psi))
  | phi => not_ phi
end

#eval to_nnf_v1 false_
#eval to_nnf_v1 (not_ false_)
#eval to_nnf_v1 (not_ (not_ false_))
#eval to_nnf_v1 (not_ (not_ (not_ false_)))
#eval to_nnf_v1 (not_ (not_ (not_ (not_ false_))))


theorem eval_to_nnf_neg_iff_not_eval_to_nnf_v1
  (V : PropValuation)
  (F : Formula_) :
  eval V (to_nnf_neg_v1 F) ↔ ¬ eval V (to_nnf_v1 F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [eval]
    tauto
  case atom_ X =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [eval]
  case not_ phi ih =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    rewrite [ih]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    tauto


example
  (V : PropValuation)
  (F : Formula_) :
  eval V F ↔ eval V (to_nnf_v1 F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v1
    rfl
  case not_ phi ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V phi]
    rfl
  case and_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case or_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case imp_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V phi]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V phi]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V psi]
    tauto


lemma to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1
  (F : Formula_) :
  (to_nnf_neg_v1 F).is_nnf ↔ (to_nnf_v1 F).is_nnf :=
  by
  induction F
  case true_ | false_ | atom_ X =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [is_nnf]
  case not_ phi ih =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [is_nnf]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


example
  (F : Formula_) :
  (to_nnf_v1 F).is_nnf :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v1
    unfold is_nnf
    exact trivial
  case not_ phi ih =>
    simp only [to_nnf_v1]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1]
    apply ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [is_nnf]
    tauto
  case imp_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [is_nnf]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [is_nnf]
    simp only [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1]
    tauto


-------------------------------------------------------------------------------


mutual
def to_nnf_v2 :
  Formula_ → Formula_
  | not_ phi => to_nnf_neg_v2 phi
  | and_ phi psi => and_ (to_nnf_v2 phi) (to_nnf_v2 psi)
  | or_ phi psi => or_ (to_nnf_v2 phi) (to_nnf_v2 psi)
  | imp_ phi psi => or_ (to_nnf_neg_v2 phi) (to_nnf_v2 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v2 phi) (to_nnf_v2 psi)) (and_ (to_nnf_neg_v2 phi) (to_nnf_neg_v2 psi))
  | phi => phi

def to_nnf_neg_v2 :
  Formula_ → Formula_
  | not_ phi => to_nnf_v2 phi
  | and_ phi psi => or_ (to_nnf_neg_v2 phi) (to_nnf_neg_v2 psi)
  | or_ phi psi => and_ (to_nnf_neg_v2 phi) (to_nnf_neg_v2 psi)
  | imp_ phi psi => and_ (to_nnf_v2 phi) (to_nnf_neg_v2 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v2 phi) (to_nnf_neg_v2 psi)) (and_ (to_nnf_neg_v2 phi) (to_nnf_v2 psi))
  | phi => not_ phi
end

#eval to_nnf_v2 false_
#eval to_nnf_v2 (not_ false_)
#eval to_nnf_v2 (not_ (not_ false_))
#eval to_nnf_v2 (not_ (not_ (not_ false_)))
#eval to_nnf_v2 (not_ (not_ (not_ (not_ false_))))


theorem eval_to_nnf_neg_iff_not_eval_to_nnf_v2
  (V : PropValuation)
  (F : Formula_) :
  eval V (to_nnf_neg_v2 F) ↔ ¬ eval V (to_nnf_v2 F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [eval]
  case atom_ X =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [eval]
  case not_ phi ih =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    rewrite [ih]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    tauto


example
  (V : PropValuation)
  (F : Formula_) :
  eval V F ↔ eval V (to_nnf_v2 F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    rfl
  case not_ phi ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V phi]
    rfl
  case and_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case or_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case imp_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V phi]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V phi]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V psi]
    tauto


lemma to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2
  (F : Formula_)
  (h1 : ¬ is_subformula false_ F)
  (h2 : ¬ is_subformula true_ F) :
  (to_nnf_neg_v2 F).is_nnf ↔ (to_nnf_v2 F).is_nnf :=
  by
  induction F
  case false_ =>
    simp only [is_subformula] at h1
    contradiction
  case true_ =>
    simp only [is_subformula] at h2
    contradiction
  case atom_ X =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [is_nnf]
  case not_ phi ih =>
    simp only [is_subformula] at h1
    simp only [is_subformula] at h2

    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [is_subformula] at h1
    simp only [is_subformula] at h2

    simp only [is_nnf]
    tauto


example
  (F : Formula_)
  (h2 : ¬ is_proper_subformula false_ F)
  (h3 : ¬ is_proper_subformula true_ F) :
  (to_nnf_v2 F).is_nnf :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    unfold is_nnf
    exact trivial
  case not_ phi ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [to_nnf_v2]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    apply ih
    · simp only [is_proper_subformula]
      tauto
    · simp only [is_proper_subformula]
      tauto
    · tauto
    · tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [is_proper_subformula] at phi_ih
    simp only [is_proper_subformula] at psi_ih

    simp only [to_nnf_v2]
    simp only [is_nnf]
    tauto
  case imp_ phi psi phi_ih psi_ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [is_proper_subformula] at phi_ih
    simp only [is_proper_subformula] at psi_ih

    simp only [to_nnf_v2]
    simp only [is_nnf]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    all_goals
      tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [is_proper_subformula] at phi_ih
    simp only [is_proper_subformula] at psi_ih

    simp only [to_nnf_v2]
    simp only [is_nnf]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    all_goals
      tauto


-------------------------------------------------------------------------------


example
  (F : Formula_) :
  ¬ is_proper_subformula false_ (simplify F) ∧
  ¬ is_proper_subformula true_ (simplify F) :=
  by
  induction F
  case and_ phi psi phi_ih psi_ih =>
    simp only [simplify]
    simp only [is_proper_subformula] at phi_ih

    have s1 : simplify phi = true_ ∨ ¬ is_subformula true_ (simplify phi) :=
    by
      tauto

    have s2 : simplify phi = false_ ∨ ¬ is_subformula false_ (simplify phi) :=
    by
      tauto

    clear phi_ih

    simp only [is_proper_subformula] at psi_ih

    have s3 : simplify psi = true_ ∨ ¬ is_subformula true_ (simplify psi) :=
    by
      tauto

    have s4 : simplify psi = false_ ∨ ¬ is_subformula false_ (simplify psi) :=
    by
      tauto

    clear psi_ih

    constructor
    · cases s1
      case _ s1 =>
        cases s2
        case _ s2 =>
          rewrite [s1] at s2
          contradiction
        case _ s2 =>
          rewrite [s1]
          cases s3
          case _ s3 =>
            rewrite [s3]
            simp only [simplify_aux]
            simp only [is_proper_subformula]
            simp only [is_subformula]
            tauto
          case _ s3 =>
            cases s4
            case _ s4 =>
              rewrite [s4]
              simp only [simplify_aux]
              simp only [is_proper_subformula]
              simp only [is_subformula]
              tauto
            case _ s4 =>
              have s5 : ¬ simplify psi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s3

              have s6 : ¬ simplify psi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s4

              simp only [simplify_aux]
              simp only [is_proper_subformula]
              tauto
      case _ s1 =>
        cases s2
        case _ s2 =>
          rewrite [s2]
          cases s3
          case _ s3 =>
            rewrite [s3]
            simp only [simplify_aux]
            simp only [is_proper_subformula]
            tauto
          case _ s3 =>
            cases s4
            case _ s4 =>
              rewrite [s4]
              simp only [simplify_aux]
              simp only [is_proper_subformula]
              tauto
            case _ s4 =>
              have s5 : ¬ simplify psi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s3

              have s6 : ¬ simplify psi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s4

              simp only [simplify_aux]
              simp only [is_proper_subformula]
              tauto
        case _ s2 =>
          cases s3
          case _ s3 =>
            rewrite [s3]
            cases s4
            case _ s4 =>
              rewrite [s3] at s4
              contradiction
            case _ s4 =>
              have s5 : ¬ simplify phi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s1

              have s6 : ¬ simplify phi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s2

              simp only [simplify_aux]
              simp only [is_proper_subformula]
              tauto
          case _ s3 =>
            cases s4
            case _ s4 =>
              rewrite [s4]

              have s5 : ¬ simplify phi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s1

              have s6 : ¬ simplify phi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s2

              simp only [simplify_aux]
              simp only [is_proper_subformula]
              tauto
            case _ s4 =>
              have s5 : ¬ simplify phi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s1

              have s6 : ¬ simplify phi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s2

              have s7 : ¬ simplify psi = true_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s3

              have s8 : ¬ simplify psi = false_ :=
              by
                apply not_is_subformula_imp_not_equal
                exact s4

              simp only [simplify_aux]
              simp_all only [and_.injEq, and_false, implies_true, false_and]
              simp only [is_proper_subformula]
              simp only [is_subformula]
              tauto
    · sorry
  all_goals
    sorry
