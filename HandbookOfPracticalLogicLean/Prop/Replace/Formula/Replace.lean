import HandbookOfPracticalLogicLean.Prop.Semantics

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `is_repl_of_formula_in_formula_rec U V P_u P_v` := True if and only if `P_v` is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of `U` in `P_u` by occurrences of `V`.
-/
def is_repl_of_formula_in_formula_rec
  (U V : Formula_) :
  Formula_ → Formula_ → Prop
  | not_ P_u, not_ P_v =>
    not_ P_u = not_ P_v ∨ (not_ P_u = U ∧ not_ P_v = V) ∨
    is_repl_of_formula_in_formula_rec U V P_u P_v

  | and_ P_u Q_u, and_ P_v Q_v =>
    and_ P_u Q_u = and_ P_v Q_v ∨ (and_ P_u Q_u = U ∧ and_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_rec U V P_u P_v ∧ is_repl_of_formula_in_formula_rec U V Q_u Q_v

  | or_ P_u Q_u, or_ P_v Q_v =>
    or_ P_u Q_u = or_ P_v Q_v ∨ (or_ P_u Q_u = U ∧ or_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_rec U V P_u P_v ∧ is_repl_of_formula_in_formula_rec U V Q_u Q_v

  | imp_ P_u Q_u, imp_ P_v Q_v =>
    imp_ P_u Q_u = imp_ P_v Q_v ∨ (imp_ P_u Q_u = U ∧ imp_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_rec U V P_u P_v ∧ is_repl_of_formula_in_formula_rec U V Q_u Q_v

  | iff_ P_u Q_u, iff_ P_v Q_v =>
    iff_ P_u Q_u = iff_ P_v Q_v ∨ (iff_ P_u Q_u = U ∧ iff_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_rec U V P_u P_v ∧ is_repl_of_formula_in_formula_rec U V Q_u Q_v

  | P_u, P_v => P_u = P_v ∨ (P_u = U ∧ P_v = V)

instance (U V F F' : Formula_) : Decidable (is_repl_of_formula_in_formula_rec U V F F') :=
  by
  induction F generalizing F'
  all_goals
    cases F'
    all_goals
      unfold is_repl_of_formula_in_formula_rec
      infer_instance


/--
  `is_repl_of_formula_in_formula_ind U V P_u P_v` := True if and only if `P_v` is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of `U` in `P_u` by occurrences of `V`.
-/
inductive is_repl_of_formula_in_formula_ind
  (U V : Formula_) :
  Formula_ → Formula_ → Prop

    -- not replacing an occurrence
  | same_
    (P_u P_v : Formula_) :
    P_u = P_v →
    is_repl_of_formula_in_formula_ind U V P_u P_v

    -- replacing an occurrence
  | diff_
    (P_u P_v : Formula_) :
    P_u = U →
    P_v = V →
    is_repl_of_formula_in_formula_ind U V P_u P_v

  | not_
    (P_u P_v : Formula_) :
    is_repl_of_formula_in_formula_ind U V P_u P_v →
    is_repl_of_formula_in_formula_ind U V P_u.not_ P_v.not_

  | and_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula_ind U V P_u P_v →
    is_repl_of_formula_in_formula_ind U V Q_u Q_v →
    is_repl_of_formula_in_formula_ind U V (P_u.and_ Q_u) (P_v.and_ Q_v)

  | or_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula_ind U V P_u P_v →
    is_repl_of_formula_in_formula_ind U V Q_u Q_v →
    is_repl_of_formula_in_formula_ind U V (P_u.or_ Q_u) (P_v.or_ Q_v)

  | imp_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula_ind U V P_u P_v →
    is_repl_of_formula_in_formula_ind U V Q_u Q_v →
    is_repl_of_formula_in_formula_ind U V (P_u.imp_ Q_u) (P_v.imp_ Q_v)

  | iff_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula_ind U V P_u P_v →
    is_repl_of_formula_in_formula_ind U V Q_u Q_v →
    is_repl_of_formula_in_formula_ind U V (P_u.iff_ Q_u) (P_v.iff_ Q_v)


lemma is_repl_of_formula_in_formula_rec_imp_is_repl_of_formula_in_formula_ind
  (U V : Formula_)
  (F F' : Formula_)
  (h1 : is_repl_of_formula_in_formula_rec U V F F') :
  is_repl_of_formula_in_formula_ind U V F F' :=
  by
  induction F generalizing F'
  all_goals
    cases F'
  case
      true_.true_
    | false_.false_ =>
    apply is_repl_of_formula_in_formula_ind.same_
    rfl
  case var_.var_ X X' =>
    unfold is_repl_of_formula_in_formula_rec at h1

    cases h1
    case inl h1 =>
      apply is_repl_of_formula_in_formula_ind.same_
      exact h1
    case inr h1 =>
      obtain ⟨h1_left, h1_right⟩ := h1

      apply is_repl_of_formula_in_formula_ind.diff_
      · exact h1_left
      · exact h1_right
  case not_.not_ phi ih phi' =>
    unfold is_repl_of_formula_in_formula_rec at h1

    cases h1
    case inl h1 =>
      apply is_repl_of_formula_in_formula_ind.same_
      exact h1
    case inr h1 =>
      cases h1
      case inl h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1

        apply is_repl_of_formula_in_formula_ind.diff_
        · exact h1_left
        · exact h1_right
      case inr h1 =>
        apply is_repl_of_formula_in_formula_ind.not_
        apply ih
        exact h1
  case
      and_.and_ phi psi phi_ih psi_ih phi' psi'
    | or_.or_ phi psi phi_ih psi_ih phi' psi'
    | imp_.imp_ phi psi phi_ih psi_ih phi' psi'
    | iff_.iff_ phi psi phi_ih psi_ih phi' psi' =>
    unfold is_repl_of_formula_in_formula_rec at h1

    cases h1
    case inl h1 =>
      apply is_repl_of_formula_in_formula_ind.same_
      exact h1
    case inr h1 =>
      cases h1
      case inl h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1

        apply is_repl_of_formula_in_formula_ind.diff_
        · exact h1_left
        · exact h1_right
      case inr h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1

        first
          | apply is_repl_of_formula_in_formula_ind.and_
          | apply is_repl_of_formula_in_formula_ind.or_
          | apply is_repl_of_formula_in_formula_ind.imp_
          | apply is_repl_of_formula_in_formula_ind.iff_
        · apply phi_ih
          exact h1_left
        · apply psi_ih
          exact h1_right

  all_goals
    unfold is_repl_of_formula_in_formula_rec at h1

    cases h1
    case inl h1 =>
      contradiction
    case inr h1 =>
      obtain ⟨h1_left, h1_right⟩ := h1

      apply is_repl_of_formula_in_formula_ind.diff_
      · exact h1_left
      · exact h1_right


lemma is_repl_of_formula_in_formula_ind_imp_is_repl_of_formula_in_formula_rec
  (U V : Formula_)
  (F F' : Formula_)
  (h1 : is_repl_of_formula_in_formula_ind U V F F') :
  is_repl_of_formula_in_formula_rec U V F F' :=
  by
  induction h1
  case same_ P_u P_v h1_ih =>
    rewrite [h1_ih]
    cases P_v
    all_goals
      unfold is_repl_of_formula_in_formula_rec
      left
      rfl
  case diff_ P_u P_v h1_ih_1 h1_ih_2 =>
    rewrite [h1_ih_1]
    rewrite [h1_ih_2]
    cases U
    all_goals
      cases V
    all_goals
      unfold is_repl_of_formula_in_formula_rec
      right
    case not_.not_ | and_.and_ | or_.or_ | imp_.imp_ | iff_.iff_ =>
      left
      exact ⟨rfl, rfl⟩
    all_goals
      exact ⟨rfl, rfl⟩
  case not_ P_u P_v h1_ih_1 h1_ih_2 =>
    unfold is_repl_of_formula_in_formula_rec
    right
    right
    exact h1_ih_2
  case
    and_ P_u Q_u P_v Q_v h1_ih_1 h1_ih_2 h1_ih_3 h1_ih_4
  | or_ P_u Q_u P_v Q_v h1_ih_1 h1_ih_2 h1_ih_3 h1_ih_4
  | imp_ P_u Q_u P_v Q_v h1_ih_1 h1_ih_2 h1_ih_3 h1_ih_4
  | iff_ P_u Q_u P_v Q_v h1_ih_1 h1_ih_2 h1_ih_3 h1_ih_4 =>
    unfold is_repl_of_formula_in_formula_rec
    right
    right
    exact ⟨h1_ih_3, h1_ih_4⟩


lemma is_repl_of_formula_in_formula_rec_iff_is_repl_of_formula_in_formula_ind
  (U V : Formula_)
  (F F' : Formula_) :
  is_repl_of_formula_in_formula_rec U V F F' ↔ is_repl_of_formula_in_formula_ind U V F F' :=
  by
  constructor
  · apply is_repl_of_formula_in_formula_rec_imp_is_repl_of_formula_in_formula_ind
  · apply is_repl_of_formula_in_formula_ind_imp_is_repl_of_formula_in_formula_rec


example
  (V : ValuationAsTotalFunction)
  (R S : Formula_)
  (P_R P_S : Formula_)
  (h1 : is_repl_of_formula_in_formula_ind R S P_R P_S)
  (h2 : eval V R = eval V S) :
  eval V P_R = eval V P_S :=
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
