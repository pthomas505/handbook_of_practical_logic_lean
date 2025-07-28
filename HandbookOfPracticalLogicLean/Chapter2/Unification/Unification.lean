-- https://dl.acm.org/doi/10.1145/357162.357169

import HandbookOfPracticalLogicLean.Chapter2.Replace
import HandbookOfPracticalLogicLean.Chapter2.SubFormula

import MathlibExtraLean.FunctionUpdateITE


set_option autoImplicit false


open Formula_


def Instantiation : Type := String → Formula_


/--
  `is_unifier σ L` := True if and only if the instantiation `σ` is a unifier of the list of pairs of formulas `L`.
-/
def is_unifier
  (σ : Instantiation)
  (L : List (Formula_ × Formula_)) :
  Prop :=
  ∀ (p : (Formula_ × Formula_)), p ∈ L →
    replace_atom_all_rec σ p.fst =
      replace_atom_all_rec σ p.snd


lemma replace_atom_all_rec_compose
  (σ τ : Instantiation)
  (F : Formula_) :
  replace_atom_all_rec ((replace_atom_all_rec τ) ∘ σ) F =
    replace_atom_all_rec τ (replace_atom_all_rec σ F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [replace_atom_all_rec]
  case atom_ X =>
    simp only [replace_atom_all_rec]
    exact Function.comp_apply
  case not_ phi ih =>
    simp only [replace_atom_all_rec]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [replace_atom_all_rec]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


example
  (σ τ : Instantiation)
  (L : List (Formula_ × Formula_))
  (h1 : is_unifier σ L) :
  is_unifier ((replace_atom_all_rec τ) ∘ σ) L :=
  by
  unfold is_unifier at h1
  unfold is_unifier
  intro p a1
  simp only [replace_atom_all_rec_compose]
  congr 1
  apply h1
  exact a1


/--
  `is_more_general_instantiation σ τ` := True if and only if the instantiation `σ` is more general than the instantiation `τ`.
  `σ ≤ τ`
-/
def is_more_general_instantiation
  (σ τ : Instantiation) :
  Prop :=
  ∃ (δ : Instantiation), replace_atom_all_rec τ = (replace_atom_all_rec δ) ∘ (replace_atom_all_rec σ)


example
  (σ : Instantiation) :
  is_more_general_instantiation σ σ :=
  by
  unfold is_more_general_instantiation
  apply Exists.intro (fun (X : String) => (atom_ X))
  funext F
  simp only [Function.comp_apply]
  simp only [replace_atom_all_rec_id]


/--
  `is_most_general_unifier σ L` := True if and only if the instantiation `σ` is a most general unifier (MGU) of the list of pairs of formulas `L`.
-/
def is_most_general_unifier
  (σ : Instantiation)
  (L : List (Formula_ × Formula_)) :
  Prop :=
  is_unifier σ L ∧ ∀ (τ : Instantiation), is_unifier τ L → is_more_general_instantiation σ τ


def are_equivalent_equation_lists
  (L L' : List (Formula_ × Formula_)) :
  Prop :=
  ∀ (σ : Instantiation), (is_unifier σ L ↔ is_unifier σ L')


def reduce :
  (Formula_ × Formula_) → Option (List (Formula_ × Formula_))
  | (not_ phi, not_ phi') => Option.some [(phi, phi')]
  | (and_ phi psi, and_ phi' psi')
  | (or_ phi psi, or_ phi' psi')
  | (imp_ phi psi, imp_ phi' psi')
  | (iff_ phi psi, iff_ phi' psi') => Option.some ([(phi, phi')] ∪ [(psi, psi')])
  | _ => Option.none


def are_reducible :
  (Formula_ × Formula_) → Prop
  | (not_ _, not_ _)
  | (and_ _ _, and_ _ _)
  | (or_ _ _, or_ _ _)
  | (imp_ _ _, imp_ _ _)
  | (iff_ _ _, iff_ _ _) => True
  | _ => False


example
  (F F' : Formula_)
  (h1 : (reduce (F, F')).isSome) :
  are_equivalent_equation_lists [(F, F')] ((reduce (F, F')).get h1) :=
  by
  cases F
  case false_ | true_ | atom_ X =>
    simp only [reduce] at h1
    simp only [Option.isSome_none] at h1
    contradiction
  case not_ phi =>
    cases F'
    case not_ phi' =>
      simp only [reduce]
      unfold are_equivalent_equation_lists
      intro σ
      unfold is_unifier
      simp only [Option.get_some]
      simp only [List.mem_singleton]
      constructor
      · intro a1 p a2
        specialize a1 (not_ phi, not_ phi')
        simp only at a1
        unfold replace_atom_all_rec at a1
        specialize a1 trivial
        simp only [not_.injEq] at a1

        rewrite [a2]
        simp only
        exact a1
      · intro a1 p a2
        rewrite [a2]
        simp only
        unfold replace_atom_all_rec
        simp only [not_.injEq]
        specialize a1 (phi, phi')
        simp only at a1
        apply a1
        exact trivial
    all_goals
      simp only [reduce] at h1
      simp only [Option.isSome_none] at h1
      contradiction
  case and_ phi psi =>
    cases F'
    case and_ phi' psi' =>
      simp only [reduce]
      unfold are_equivalent_equation_lists
      intro σ
      unfold is_unifier
      simp only [Option.get_some]
      simp only [List.cons_union]
      simp only [List.nil_union]
      simp only [List.mem_insert_iff]
      simp only [List.mem_singleton]
      constructor
      · intro a1 p a2
        specialize a1 (and_ phi psi, and_ phi' psi')
        simp only at a1
        unfold replace_atom_all_rec at a1
        specialize a1 trivial
        simp only [and_.injEq] at a1
        obtain ⟨a1_left, a1_right⟩ := a1

        cases a2
        case inl a2 =>
          rewrite [a2]
          simp only
          exact a1_left
        case inr a2 =>
          rewrite [a2]
          simp only
          exact a1_right
      · intro a1 p a2
        rewrite [a2]
        simp only
        unfold replace_atom_all_rec
        simp only [and_.injEq]
        constructor
        · specialize a1 (phi, phi')
          simp only at a1
          apply a1
          left
          exact trivial
        · specialize a1 (psi, psi')
          simp only at a1
          apply a1
          right
          exact trivial
    all_goals
      simp only [reduce] at h1
      simp only [Option.isSome_none] at h1
      contradiction
  all_goals
    sorry


-------------------------------------------------------------------------------


lemma is_subformula_imp_is_subformula_replace_atom_all_rec
  (σ : Instantiation)
  (F F' : Formula_)
  (h1 : is_subformula F F') :
  is_subformula (replace_atom_all_rec σ F) (replace_atom_all_rec σ F') :=
  by
  induction F'
  case false_ | true_ | atom_ X =>
    unfold is_subformula at h1
    rewrite [h1]
    apply is_subformula_refl
  case not_ phi ih =>
    unfold is_subformula at h1

    cases h1
    case inl h1 =>
      rewrite [h1]
      apply is_subformula_refl
    case inr h1 =>
      simp only [replace_atom_all_rec]
      unfold is_subformula
      right
      apply ih
      exact h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold is_subformula at h1

    cases h1
    case inl h1 =>
      rewrite [h1]
      apply is_subformula_refl
    case inr h1 =>
      simp only [replace_atom_all_rec]
      unfold is_subformula
      right

      cases h1
      case inl h1 =>
        left
        apply phi_ih
        exact h1
      case inr h1 =>
        right
        apply psi_ih
        exact h1


lemma is_proper_subformula_v2_imp_replace_atom_all_rec_not_eq
  (σ : Instantiation)
  (F F' : Formula_)
  (h1 : is_proper_subformula_v2 F F') :
  ¬ replace_atom_all_rec σ F = replace_atom_all_rec σ F' :=
  by
  cases F'
  case false_ | true_ | atom_ X =>
    unfold is_proper_subformula_v2 at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    unfold is_subformula at h1_left
    contradiction
  case not_ phi =>
    unfold is_proper_subformula_v2 at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    unfold is_subformula at h1_left

    cases h1_left
    case inl h1_left =>
      contradiction
    case inr h1_left =>
      obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec σ F phi h1_left
      intro contra
      rewrite [contra] at s1
      simp only [replace_atom_all_rec] at s1
      apply not_is_subformula_not (replace_atom_all_rec σ phi)
      exact s1
  case
      and_ phi psi
    | or_ phi psi
    | imp_ phi psi
    | iff_ phi psi =>
    unfold is_proper_subformula_v2 at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    unfold is_subformula at h1_left

    cases h1_left
    case inl h1_left =>
      contradiction
    case inr h1_left =>
      cases h1_left
      case inl h1_left =>
        obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec σ F phi h1_left
        intro contra
        rewrite [contra] at s1
        simp only [replace_atom_all_rec] at s1
        first
        | exact not_is_subformula_and_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_or_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_imp_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_iff_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
      case inr h1_left =>
        obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec σ F psi h1_left
        intro contra
        rewrite [contra] at s1
        simp only [replace_atom_all_rec] at s1
        first
        | exact not_is_subformula_and_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_or_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_imp_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_iff_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1


lemma is_proper_subformula_v2_imp_is_proper_subformula_v2_replace_atom_all_rec
  (σ : Instantiation)
  (F F' : Formula_)
  (h1 : is_proper_subformula_v2 F F') :
  is_proper_subformula_v2 (replace_atom_all_rec σ F) (replace_atom_all_rec σ F') :=
  by
  unfold is_proper_subformula_v2 at h1
  obtain ⟨h1_left, h1_right⟩ := h1

  unfold is_proper_subformula_v2
  constructor
  · apply is_subformula_imp_is_subformula_replace_atom_all_rec
    exact h1_left
  · apply is_proper_subformula_v2_imp_replace_atom_all_rec_not_eq
    unfold is_proper_subformula_v2
    exact ⟨h1_left, h1_right⟩


example
  (σ : Instantiation)
  (F F' : Formula_)
  (h1 : is_proper_subformula_v2 F F') :
  ¬ is_unifier σ [(F, F')] :=
  by
  unfold is_unifier
  simp only [List.mem_singleton]
  intro contra
  apply is_proper_subformula_v2_imp_replace_atom_all_rec_not_eq σ F F'
  · exact h1
  · specialize contra (F, F')
    simp only at contra
    apply contra
    exact trivial


-------------------------------------------------------------------------------


/-
  Let `X` be a variable, `F` be a formula, and `L : List (Formula_ × Formula_)` be a list of equations. If `(X, F) ∈ L` then every instantiation that is a unifier of `L` is also a unifier of `(X, F)`. Hence every instantiation that is a unifier of `L` maps `X` and `F` to the same formula. Let `L'` be the replacement of every occurrence of `X` in `L` by `F`. Then every instantiation that is a unifier of `L` maps `X` and `F` in `L` to the same formula that it maps `F` in `L'` to. Therefore `L` and `L'` are equivalent equation lists.
-/


def var_elim
  (X : String)
  (F : Formula_)
  (L : List (Formula_ × Formula_)) :
  List (Formula_ × Formula_) :=
  L.map (fun (eq : Formula_ × Formula_) => (replace_atom_one_rec X F eq.fst, replace_atom_one_rec X F eq.snd))


example
  (σ : Instantiation)
  (X : String)
  (F : Formula_)
  (L : List (Formula_ × Formula_))
  (h1 : is_unifier σ ((atom_ X, F) :: L)) :
  σ X = replace_atom_all_rec σ F :=
  by
  unfold is_unifier at h1
  simp only [List.mem_cons] at h1
  specialize h1 (atom_ X, F)
  simp only at h1
  simp only [replace_atom_all_rec] at h1
  apply h1
  left
  exact trivial


lemma replace_atom_all_rec_eq_replace_atom_all_rec_of_replace_atom_one_rec
  (σ : Instantiation)
  (X' : String)
  (F' : Formula_)
  (F : Formula_)
  (h1 : σ X' = replace_atom_all_rec σ F') :
  replace_atom_all_rec σ F =
    replace_atom_all_rec σ (replace_atom_one_rec X' F' F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [replace_atom_all_rec]
  case atom_ X =>
    simp only [replace_atom_all_rec]
    unfold replace_atom_one_rec
    split_ifs
    case pos c1 =>
      rewrite [← c1]
      exact h1
    case neg c1 =>
      unfold replace_atom_all_rec
      rfl
  case not_ phi ih =>
    simp only [replace_atom_all_rec]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [replace_atom_all_rec]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


lemma is_unifier_singleton
  (σ : Instantiation)
  (F F' : Formula_) :
  is_unifier σ [(F, F')] ↔ replace_atom_all_rec σ F = replace_atom_all_rec σ F' :=
  by
  unfold is_unifier
  simp only [List.mem_singleton]
  constructor
  · intro a1
    specialize a1 (F, F')
    simp only at a1
    specialize a1 trivial
    exact a1
  · intro a1 p a2
    rewrite [a2]
    simp only
    exact a1


example
  (σ : Instantiation)
  (X : String)
  (F : Formula_)
  (F_1 F_2 : Formula_)
  (h1 : is_unifier σ [(atom_ X, F)])
  (h2 : is_unifier σ [(F_1, F_2)]) :
  is_unifier σ ([(replace_atom_one_rec X F F_1, replace_atom_one_rec X F F_2)]) :=
  by
  simp only [is_unifier_singleton] at h1
  simp only [replace_atom_all_rec] at h1

  simp only [is_unifier_singleton] at h2

  simp only [is_unifier_singleton]

  obtain s1 := replace_atom_all_rec_eq_replace_atom_all_rec_of_replace_atom_one_rec σ X F F_1 h1
  rewrite [← s1]

  obtain s2 := replace_atom_all_rec_eq_replace_atom_all_rec_of_replace_atom_one_rec σ X F F_2 h1
  rewrite [← s2]

  exact h2


lemma is_unifier_singleton_refl
  (σ : Instantiation)
  (F : Formula_) :
  is_unifier σ [(F, F)] :=
  by
  rewrite [is_unifier_singleton]
  rfl


lemma is_unifier_singleton_comm
  (σ : Instantiation)
  (F F' : Formula_) :
  is_unifier σ [(F, F')] ↔ is_unifier σ [(F', F)] :=
  by
  simp only [is_unifier_singleton]
  exact eq_comm


lemma is_unifier_singleton_trans
  (σ : Instantiation)
  (F F' F'' : Formula_)
  (h1 : is_unifier σ [(F, F')])
  (h2 : is_unifier σ [(F', F'')]) :
  is_unifier σ [(F, F'')] :=
  by
  simp only [is_unifier_singleton] at h1

  simp only [is_unifier_singleton] at h2

  simp only [is_unifier_singleton]
  trans (replace_atom_all_rec σ F')
  · apply h1
  · apply h2


lemma is_unifier_append
  (σ : Instantiation)
  (L L' : List (Formula_ × Formula_)) :
  is_unifier σ (L ++ L') ↔ (is_unifier σ L ∧ is_unifier σ L') :=
  by
  unfold is_unifier
  simp only [List.mem_append]
  constructor
  · intro a1
    constructor
    · intro p a2
      apply a1
      left
      exact a2
    · intro p a2
      apply a1
      right
      exact a2
  · intro a1 p a2
    obtain ⟨a1_left, a1_right⟩ := a1

    cases a2
    case inl a2 =>
      apply a1_left
      exact a2
    case inr a2 =>
      apply a1_right
      exact a2


theorem extracted_1
  (σ : Instantiation)
  (Y : String)
  (F F_1 F_2 : Formula_)
  (h1 : ¬ atom_occurs_in Y F)
  (h2 : is_unifier σ [(atom_ Y, F)])
  (h3 : is_unifier σ [(F_1, F_2)]) :
  is_unifier σ [(replace_atom_all_rec (Function.updateITE atom_ Y F) F_1, replace_atom_all_rec (Function.updateITE atom_ Y F) F_2)] :=
  by
  induction F_1 generalizing F_2
  case atom_ X =>
    cases F_2
    case atom_ X' =>
      unfold replace_atom_all_rec
      simp only [Function.updateITE]
      split_ifs
      case pos c1 c2 =>
        apply is_unifier_singleton_refl
      case neg c1 c2 =>
        rewrite [c1] at h3
        apply is_unifier_singleton_trans σ F (atom_ Y) (atom_ X')
        · rewrite [is_unifier_singleton_comm]
          exact h2
        · exact h3
      case pos c1 c2 =>
        rewrite [c2] at h3
        apply is_unifier_singleton_trans σ (atom_ X) (atom_ Y) F
        · exact h3
        · exact h2
      case neg c1 c2 =>
        exact h3
    all_goals
      sorry
  all_goals
    sorry


example
  (X : String)
  (F : Formula_)
  (F_1 F_2 : Formula_)
  (h1 : ¬ atom_occurs_in X F) :
  are_equivalent_equation_lists ((atom_ X, F) :: [(F_1, F_2)]) ((atom_ X, F) :: (var_elim X F [(F_1, F_2)])) :=
  by
  unfold are_equivalent_equation_lists
  intro σ
  constructor
  · intro a1
    rewrite [← List.singleton_append] at a1
    rewrite [is_unifier_append] at a1
    obtain ⟨a1_left, a1_right⟩ := a1
    rewrite [← List.singleton_append]
    rewrite [is_unifier_append]
    constructor
    · exact a1_left
    · unfold var_elim
      simp only [List.map_cons, List.map_nil]
      sorry
  · intro a1
    rewrite [← List.singleton_append] at a1
    rewrite [is_unifier_append] at a1
    obtain ⟨a1_left, a1_right⟩ := a1
    rewrite [← List.singleton_append]
    rewrite [is_unifier_append]
    constructor
    · exact a1_left
    · unfold var_elim at a1_right
      simp only [List.map_cons, List.map_nil] at a1_right
      sorry


example
  (X : String)
  (F : Formula_)
  (L : List (Formula_ × Formula_))
  (h1 : ¬ atom_occurs_in X F) :
  are_equivalent_equation_lists ((atom_ X, F) :: L) ((atom_ X, F) :: (var_elim X F L)) :=
  by
  sorry
