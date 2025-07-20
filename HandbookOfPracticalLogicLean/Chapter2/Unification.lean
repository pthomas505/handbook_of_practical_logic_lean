import HandbookOfPracticalLogicLean.Chapter2.DeMorgan
import HandbookOfPracticalLogicLean.Chapter2.Replace
import HandbookOfPracticalLogicLean.Chapter2.SubFormula


set_option autoImplicit false


open Formula_


def Instantiation : Type := String → Formula_


/--
  `is_unifier σ S` := True if and only if the instantiation `σ` is a unifier of the set of pairs of formulas `S`.
-/
def is_unifier
  (σ : Instantiation)
  (S : Set (Formula_ × Formula_)) :
  Prop :=
  ∀ (p : (Formula_ × Formula_)), p ∈ S →
    replace_atom_all_rec σ p.fst =
      replace_atom_all_rec σ p.snd


lemma replace_atom_all_rec_compose
  (F : Formula_)
  (σ τ : Instantiation) :
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
  (S : Set (Formula_ × Formula_))
  (h1 : is_unifier σ S) :
  is_unifier ((replace_atom_all_rec τ) ∘ σ) S :=
  by
  unfold is_unifier at h1
  unfold is_unifier
  intro p a1
  simp only [replace_atom_all_rec_compose]
  rewrite [h1 p a1]
  rfl


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
  `is_most_general_unifier σ S` := True if and only if the instantiation `σ` is a most general unifier (MGU) of the set of pairs of formulas `S`.
-/
def is_most_general_unifier
  (σ : Instantiation)
  (S : Set (Formula_ × Formula_)) :
  Prop :=
  is_unifier σ S ∧ ∀ (τ : Instantiation), is_unifier τ S → is_more_general_instantiation σ τ


def are_equivalent_equation_sets
  (S S' : Set (Formula_ × Formula_)) :
  Prop :=
  ∀ (σ : Instantiation), (is_unifier σ S ↔ is_unifier σ S')


def reduce :
  (Formula_ × Formula_) → Option (Set (Formula_ × Formula_))
  | (not_ phi, not_ phi') => Option.some { (phi, phi') }
  | (and_ phi psi, and_ phi' psi')
  | (or_ phi psi, or_ phi' psi')
  | (imp_ phi psi, imp_ phi' psi')
  | (iff_ phi psi, iff_ phi' psi') => Option.some { (phi, phi'), (psi, psi') }
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
  are_equivalent_equation_sets { (F, F') } ((reduce (F, F')).get h1) :=
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
      unfold are_equivalent_equation_sets
      intro σ
      unfold is_unifier
      simp only [Option.get_some]
      simp only [Set.mem_singleton_iff]
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
      unfold are_equivalent_equation_sets
      intro σ
      unfold is_unifier
      simp only [Option.get_some]
      simp only [Set.mem_insert_iff]
      simp only [Set.mem_singleton_iff]
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


/-
--def Environment : Type := Std.HashMap String Formula_
def Environment : Type := List (String × Formula_)


def Environment.get?
  (E : Environment)
  (X : String) :
  Option Formula_ :=
  match E.find? (fun (step : String × Formula_) => step.fst = X) with
  | none => none
  | some step => step.snd


def is_small_step
  (E : Environment)
  (X Y : String) :
  Prop :=
  match E.get? X with
  | none => False
  | some F => atom_occurs_in Y F

instance
  (E : Environment)
  (X Y : String) :
  Decidable (is_small_step E X Y) :=
  by
  unfold is_small_step
  cases E.get? X
  case none =>
    simp only
    infer_instance
  case some F =>
    simp only
    infer_instance


def is_one_or_more_small_steps
  (E : Environment)
  (X Y : String)
  (l : List String) :
  Prop :=
  List.Chain (is_small_step E) X (l ++ [Y])

instance
  (E : Environment)
  (X Y : String)
  (l : List String) :
  Decidable (is_one_or_more_small_steps E X Y l) :=
  by
  unfold is_one_or_more_small_steps
  infer_instance


def is_zero_or_more_small_steps
  (E : Environment)
  (X : String)
  (F : Formula_) :
  Prop :=
  atom_occurs_in X F ∨ ∃ (Y : String), ∃ (l : List String), is_one_or_more_small_steps E X Y l


def Environment.has_cycle
  (E : Environment) :
  Prop :=
  ∃ (X : String), ∃ (l : List String), is_one_or_more_small_steps E X X l


-------------------------------------------------------------------------------


lemma is_small_step_refl
  (E : Environment)
  (X : String)
  (F : Formula_)
  (h1 : atom_occurs_in X F)
  (h2 : E.get? X = some F) :
  is_small_step E X X :=
  by
  unfold is_small_step
  cases c1 : E.get? X
  case none =>
    rewrite [c1] at h2
    contradiction
  case some F' =>
    rewrite [c1] at h2
    cases h2
    simp only
    exact h1


lemma is_one_or_more_small_steps_refl_nil
  (E : Environment)
  (X : String)
  (F : Formula_)
  (h1 : atom_occurs_in X F)
  (h2 : E.get? X = some F) :
  is_one_or_more_small_steps E X X [] :=
  by
  unfold is_one_or_more_small_steps
  simp only [List.nil_append, List.chain_cons, List.Chain.nil]
  constructor
  · exact is_small_step_refl E X F h1 h2
  · exact trivial


example
  (X : String)
  (F : Formula_)
  (h1 : atom_occurs_in X F) :
  Environment.has_cycle [(X, F)] :=
  by
  unfold Environment.has_cycle
  apply Exists.intro X
  apply Exists.intro []
  apply is_one_or_more_small_steps_refl_nil [(X, F)] X F
  · exact h1
  · unfold Environment.get?
    simp only [decide_true, List.find?_cons_of_pos]


-------------------------------------------------------------------------------


lemma not_is_small_step_nil
  (X Y : String) :
  ¬ is_small_step [] X Y :=
  by
  unfold is_small_step
  unfold Environment.get?
  simp only [List.find?_nil]
  intro contra
  exact contra


theorem not_is_small_step_singleton_refl
  (X Y : String)
  (F : Formula_)
  (h1 : ¬ atom_occurs_in X F) :
  ¬ is_small_step [(X, F)] Y Y :=
  by
  intro contra
  unfold is_small_step at contra
  unfold Environment.get? at contra
  simp only [List.find?_singleton] at contra
  split_ifs at contra
  case pos c1 =>
    simp only at contra
    simp only [decide_eq_true_iff] at c1
    rewrite [c1] at h1
    contradiction
  case neg c1 =>
    simp only at contra


lemma not_has_cycle_nil :
  ¬ Environment.has_cycle [] :=
  by
  unfold Environment.has_cycle
  simp only [not_exists]
  intro X l contra
  unfold is_one_or_more_small_steps at contra
  cases l
  case nil =>
    simp only [List.nil_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    exact not_is_small_step_nil X X contra_left
  case cons hd tl =>
    simp only [List.cons_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    exact not_is_small_step_nil X hd contra_left


example
  (X : String)
  (F : Formula_)
  (h1 : ¬ atom_occurs_in X F) :
  ¬ Environment.has_cycle [(X, F)] :=
  by
  unfold Environment.has_cycle
  simp only [not_exists]
  intro Y l contra
  unfold is_one_or_more_small_steps at contra
  cases l
  case nil =>
    simp only [List.nil_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    exact not_is_small_step_singleton_refl X Y F h1 contra_left
  case cons hd tl =>
    sorry


example
  (E : Environment)
  (X : String)
  (F : Formula_)
  (h1 : ¬ E.has_cycle)
  (h2 : ¬ atom_occurs_in X F)
  (h3 : ∀ (Y : String), ∀ (l : List String), atom_occurs_in Y F → ¬ is_one_or_more_small_steps E X Y l) :
  let E' : Environment := (X, F) :: E
  ¬ E'.has_cycle :=
  by
  simp only
  unfold Environment.has_cycle
  intro contra
  obtain ⟨Z, l, contra⟩ := contra
  induction l
  case nil =>
    unfold is_one_or_more_small_steps at contra
    simp at contra
    sorry
  sorry
-/


-------------------------------------------------------------------------------


def is_small_step_v1
  (E : List (String × Formula_))
  (X Y : String) :
  Prop :=
  ∃ (F : Formula_), (X, F) ∈ E ∧ atom_occurs_in Y F


def is_small_step_v2
  (E : List (String × Formula_))
  (X Y : String) :
  Prop :=
  match E with
  | [] => False
  | hd :: tl => (hd.fst = X ∧ atom_occurs_in Y hd.snd) ∨
    is_small_step_v2 tl X Y

instance
  (E : List (String × Formula_))
  (X Y : String) :
  Decidable (is_small_step_v2 E X Y) :=
  by
  induction E
  all_goals
    unfold is_small_step_v2
    infer_instance


lemma is_small_step_v1_imp_is_small_step_v2
  (E : List (String × Formula_))
  (X Y : String)
  (h1 : is_small_step_v1 E X Y) :
  is_small_step_v2 E X Y :=
  by
  induction E
  case nil =>
    unfold is_small_step_v1 at h1
    simp only [List.not_mem_nil] at h1
    obtain ⟨F, h1_left, h1_right⟩ := h1
    contradiction
  case cons hd tl ih =>
    unfold is_small_step_v1 at h1
    obtain ⟨F, h1_left, h1_right⟩ := h1
    simp only [List.mem_cons] at h1_left

    cases h1_left
    case inl h1_left =>
      rewrite [← h1_left]
      unfold is_small_step_v2
      simp only
      left
      exact ⟨trivial, h1_right⟩
    case inr h1_left =>
      unfold is_small_step_v2
      right
      apply ih
      unfold is_small_step_v1
      apply Exists.intro F
      exact ⟨h1_left, h1_right⟩


lemma is_small_step_v2_imp_is_small_step_v1
  (E : List (String × Formula_))
  (X Y : String)
  (h1 : is_small_step_v2 E X Y) :
  is_small_step_v1 E X Y :=
  by
  induction E
  case nil =>
    unfold is_small_step_v2 at h1
    contradiction
  case cons hd tl ih =>
    unfold is_small_step_v2 at h1

    cases h1
    case inl h1 =>
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold is_small_step_v1
      apply Exists.intro hd.2
      rewrite [← h1_left]
      simp only [List.mem_cons]
      constructor
      · left
        exact trivial
      · exact h1_right
    case inr h1 =>
      specialize ih h1
      unfold is_small_step_v1 at ih
      obtain ⟨F, ih_left, ih_right⟩ := ih

      unfold is_small_step_v1
      apply Exists.intro F
      constructor
      · simp only [List.mem_cons]
        right
        exact ih_left
      · exact ih_right


lemma is_small_step_v1_iff_is_small_step_v2
  (E : List (String × Formula_))
  (X Y : String) :
  is_small_step_v1 E X Y ↔ is_small_step_v2 E X Y :=
  by
  constructor
  · apply is_small_step_v1_imp_is_small_step_v2
  · apply is_small_step_v2_imp_is_small_step_v1


-------------------------------------------------------------------------------


instance
  (E : List (String × Formula_))
  (X Y : String) :
  Decidable (is_small_step_v1 E X Y) :=
  by
  simp only [is_small_step_v1_iff_is_small_step_v2]
  infer_instance


def is_one_or_more_small_steps
  (E : List (String × Formula_))
  (X Y : String)
  (l : List String) :
  Prop :=
  List.Chain (is_small_step_v1 E) X (l ++ [Y])

instance
  (E : List (String × Formula_))
  (X Y : String)
  (l : List String) :
  Decidable (is_one_or_more_small_steps E X Y l) :=
  by
  unfold is_one_or_more_small_steps
  infer_instance


def is_zero_or_more_small_steps
  (E : List (String × Formula_))
  (X : String)
  (F : Formula_) :
  Prop :=
  atom_occurs_in X F ∨ ∃ (Y : String), ∃ (l : List String), is_one_or_more_small_steps E X Y l


def has_cycle
  (E : List (String × Formula_)) :
  Prop :=
  ∃ (X : String), ∃ (l : List String), is_one_or_more_small_steps E X X l


-------------------------------------------------------------------------------


lemma not_is_small_step_nil
  (X Y : String) :
  ¬ is_small_step_v1 [] X Y :=
  by
  unfold is_small_step_v1
  simp only [not_exists]
  intro F contra
  obtain ⟨contra_left, contra_right⟩ := contra
  simp only [List.not_mem_nil] at contra_left


-------------------------------------------------------------------------------


lemma is_small_step_singleton_left
  (X Y : String)
  (F : Formula_)
  (Z : String)
  (h1 : is_small_step_v1 [(X, F)] Y Z) :
  Y = X ∧ atom_occurs_in Z F :=
  by
  unfold is_small_step_v1 at h1
  obtain ⟨F', h1_left, h1_right⟩ := h1
  simp only [List.mem_singleton, Prod.mk.injEq] at h1_left
  obtain ⟨h1_left_left, h1_left_right⟩ := h1_left

  constructor
  · exact h1_left_left
  · rewrite [← h1_left_right]
    exact h1_right


lemma is_small_step_singleton_right
  (X Y : String)
  (F : Formula_)
  (Z : String)
  (h1 : Y = X)
  (h2 : atom_occurs_in Z F) :
  is_small_step_v1 [(X, F)] Y Z :=
  by
  unfold is_small_step_v1
  apply Exists.intro F
  constructor
  · simp only [List.mem_singleton, Prod.mk.injEq]
    constructor
    · exact h1
    · exact trivial
  · exact h2


lemma is_small_step_singleton
  (X Y : String)
  (F : Formula_)
  (Z : String) :
  (is_small_step_v1 [(X, F)] Y Z) ↔ (Y = X ∧ atom_occurs_in Z F) :=
  by
  constructor
  · apply is_small_step_singleton_left
  · intro a1
    obtain ⟨a1_left, a1_right⟩ := a1
    apply is_small_step_singleton_right
    · exact a1_left
    · exact a1_right


-------------------------------------------------------------------------------


theorem not_is_small_step_singleton_refl
  (X Y : String)
  (F : Formula_)
  (h1 : ¬ atom_occurs_in X F) :
  ¬ is_small_step_v1 [(X, F)] Y Y :=
  by
  simp only [not_is_small_step_singleton]
  intro contra
  obtain ⟨contra_left, contra_right⟩ := contra
  apply h1
  rewrite [← contra_left]
  exact contra_right


-------------------------------------------------------------------------------


lemma is_small_step_append_left
  (E_1 E_2 : List (String × Formula_))
  (X Y : String)
  (h1 : is_small_step_v1 (E_1 ++ E_2) X Y) :
  (is_small_step_v1 E_1 X Y) ∨ (is_small_step_v1 E_2 X Y) :=
  by
  unfold is_small_step_v1 at h1
  obtain ⟨F, h1_left, h1_right⟩ := h1
  simp only [List.mem_append] at h1_left

  unfold is_small_step_v1
  cases h1_left
  case inl h1_left =>
    left
    apply Exists.intro F
    exact ⟨h1_left, h1_right⟩
  case inr h1_left =>
    right
    apply Exists.intro F
    exact ⟨h1_left, h1_right⟩


lemma is_small_step_append_right
  (E_1 E_2 : List (String × Formula_))
  (X Y : String)
  (h1 : is_small_step_v1 E_1 X Y ∨ is_small_step_v1 E_2 X Y) :
  is_small_step_v1 (E_1 ++ E_2) X Y :=
  by
  unfold is_small_step_v1

  cases h1
  case inl h1 =>
    unfold is_small_step_v1 at h1
    obtain ⟨F, h1_left, h1_right⟩ := h1

    apply Exists.intro F
    constructor
    · simp only [List.mem_append]
      left
      exact h1_left
    · exact h1_right
  case inr h1 =>
    unfold is_small_step_v1 at h1
    obtain ⟨F, h1_left, h1_right⟩ := h1

    apply Exists.intro F
    constructor
    · simp only [List.mem_append]
      right
      exact h1_left
    · exact h1_right


example
  (E_1 E_2 : List (String × Formula_))
  (X Y : String) :
  (is_small_step_v1 (E_1 ++ E_2) X Y) ↔ (is_small_step_v1 E_1 X Y ∨ is_small_step_v1 E_2 X Y) :=
  by
  constructor
  · apply is_small_step_append_left
  · apply is_small_step_append_right


lemma not_is_small_step_append_left
  (E_1 E_2 : List (String × Formula_))
  (X Y : String)
  (h1 : ¬ is_small_step_v1 (E_1 ++ E_2) X Y) :
  (¬ is_small_step_v1 E_1 X Y) ∧ (¬ is_small_step_v1 E_2 X Y) :=
  by
  unfold is_small_step_v1 at h1
  simp only [not_exists] at h1
  simp only [List.mem_append] at h1

  unfold is_small_step_v1
  simp only [not_exists]
  constructor
  · intro F contra
    obtain ⟨contra_left, contra_right⟩ := contra
    specialize h1 F
    apply h1
    constructor
    · left
      exact contra_left
    · exact contra_right
  · intro F contra
    obtain ⟨contra_left, contra_right⟩ := contra
    specialize h1 F
    apply h1
    constructor
    · right
      exact contra_left
    · exact contra_right


lemma not_is_small_step_append_right
  (E_1 E_2 : List (String × Formula_))
  (X Y : String)
  (h1 : ¬ is_small_step_v1 E_1 X Y)
  (h2 : ¬ is_small_step_v1 E_2 X Y) :
  ¬ is_small_step_v1 (E_1 ++ E_2) X Y :=
  by
  unfold is_small_step_v1 at h1
  simp only [not_exists] at h1

  unfold is_small_step_v1 at h2
  simp only [not_exists] at h2

  unfold is_small_step_v1
  simp only [not_exists]
  simp only [List.mem_append]
  intro F contra
  obtain ⟨contra_left, contra_right⟩ := contra
  cases contra_left
  case inl contra_left =>
    apply h1 F
    exact ⟨contra_left, contra_right⟩
  case inr contra_left =>
    apply h2 F
    exact ⟨contra_left, contra_right⟩


lemma not_is_small_step_append
  (E_1 E_2 : List (String × Formula_))
  (X Y : String) :
  (¬ is_small_step_v1 (E_1 ++ E_2) X Y) ↔ (¬ is_small_step_v1 E_1 X Y ∧ ¬ is_small_step_v1 E_2 X Y) :=
  by
  constructor
  · apply not_is_small_step_append_left
  · intro a1
    obtain ⟨a1_left, a1_right⟩ := a1
    apply not_is_small_step_append_right
    · exact a1_left
    · exact a1_right


-------------------------------------------------------------------------------


lemma is_one_or_more_small_steps_trans
  (E : List (String × Formula_))
  (X Y Z : String)
  (l : List String)
  (h1 : ¬ l = [])
  (h2 : is_one_or_more_small_steps E X Y l)
  (h3 : is_one_or_more_small_steps E Y Z l) :
  is_one_or_more_small_steps E X Z l :=
  by
  cases l
  case nil =>
    contradiction
  case cons hd tl =>
    unfold is_one_or_more_small_steps at h2
    simp only [List.cons_append, List.chain_cons] at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    unfold is_one_or_more_small_steps at h3
    simp only [List.cons_append, List.chain_cons] at h3
    obtain ⟨h3_left, h3_right⟩ := h3

    unfold is_one_or_more_small_steps
    simp only [List.cons_append, List.chain_cons]
    exact ⟨h2_left, h3_right⟩


example
  (X Y Z : String)
  (F : Formula_)
  (l : List String)
  (h1 : ¬ Y = X ∨ ¬ atom_occurs_in Z F) :
  ¬ is_one_or_more_small_steps [(X, F)] Y Z l :=
  by
  unfold is_one_or_more_small_steps
  cases l
  case nil =>
    simp only [List.nil_append, List.chain_cons, List.Chain.nil]
    intro contra
    obtain ⟨contra_left, contra_right⟩ := contra
    apply not_is_small_step_singleton_right X Y F Z
    · simp only [de_morgan_prop_1]
      exact h1
    · exact contra_left
  case cons hd tl =>
    simp only [List.cons_append, List.chain_cons]
    intro contra
    obtain ⟨contra_left, contra_right⟩ := contra
    apply not_is_small_step_singleton_right X Y F hd
    · simp only [de_morgan_prop_1]
      unfold is_small_step_v1 at contra_left

      exact h1
    · exact contra_left


lemma not_nil_not_eq_imp_not_is_one_or_more_small_steps_singleton
  (X Y : String)
  (F : Formula_)
  (l : List String)
  (h1 : ¬ l = [])
  (h2 : ¬ Y = X) :
  ¬ List.Chain (is_small_step_v1 [(X, F)]) Y l :=
  by
  cases l
  case nil =>
    contradiction
  case cons hd tl =>
    intro contra_1
    simp only [List.chain_cons] at contra_1
    obtain ⟨contra_1_left, contra_1_right⟩ := contra_1
    apply not_is_small_step_singleton_right X Y F hd
    · intro contra_2
      obtain ⟨contra_2_left, contra_2_right⟩ := contra_2
      contradiction
    · exact contra_1_left


lemma not_has_cycle_nil :
  ¬ has_cycle [] :=
  by
  unfold has_cycle
  simp only [not_exists]
  intro X l contra
  unfold is_one_or_more_small_steps at contra
  cases l
  case nil =>
    simp only [List.nil_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    exact not_is_small_step_nil X X contra_left
  case cons hd tl =>
    simp only [List.cons_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    exact not_is_small_step_nil X hd contra_left


lemma not_has_cycle_singleton
  (X : String)
  (F : Formula_)
  (h1 : ¬ atom_occurs_in X F) :
  ¬ has_cycle [(X, F)] :=
  by
  unfold has_cycle
  simp only [not_exists]
  intro Y l contra
  unfold is_one_or_more_small_steps at contra
  cases l
  case nil =>
    simp only [List.nil_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    exact not_is_small_step_singleton_refl X Y F h1 contra_left
  case cons hd tl =>
    simp only [List.cons_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    unfold is_small_step_v1 at contra_left
    obtain ⟨F', contra_left_left, contra_left_right⟩ := contra_left
    simp only [List.mem_singleton, Prod.mk.injEq] at contra_left_left
    obtain ⟨contra_left_left_left, contra_left_left_right⟩ := contra_left_left
    rewrite [contra_left_left_right] at contra_left_right
    apply not_nil_not_eq_imp_not_is_one_or_more_small_steps_singleton X hd F (tl ++ [Y])
    · simp only [List.append_eq_nil, List.cons_ne_self]
      intro contra
      obtain ⟨contra_left, contra_right⟩ := contra
      contradiction
    · intro contra
      rewrite [contra] at contra_left_right
      contradiction
    · exact contra_right


example
  (E : List (String × Formula_))
  (X : String)
  (F : Formula_)
  (h1 : ¬ has_cycle E)
  (h2 : ¬ atom_occurs_in X F)
  (h3 : ∀ (Y : String), ∀ (l : List String), atom_occurs_in Y F → ¬ is_one_or_more_small_steps E X Y l) :
  ¬ has_cycle ((X, F) :: E) :=
  by
  unfold has_cycle at h1
  simp only [not_exists] at h1
  unfold is_one_or_more_small_steps at h1

  unfold is_one_or_more_small_steps at h3

  obtain s1 := not_has_cycle_singleton X F h2
  unfold has_cycle at s1
  simp only [not_exists] at s1
  unfold is_one_or_more_small_steps at s1

  unfold has_cycle
  simp only [not_exists]
  intro Y l contra
  unfold is_one_or_more_small_steps at contra

  induction l
  case nil =>
    simp only [List.nil_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    clear contra_right
    unfold is_small_step_v1 at contra_left
    obtain ⟨F', contra_left_left, contra_left_right⟩ := contra_left
    simp only [List.mem_cons, Prod.mk.injEq] at contra_left_left
    cases contra_left_left
    case inl contra_left_left =>
      obtain ⟨contra_left_left_left, contra_left_left_right⟩ := contra_left_left
      rewrite [contra_left_left_left] at contra_left_right
      rewrite [contra_left_left_right] at contra_left_right
      contradiction
    case inr contra_left_left =>
      specialize h1 Y []
      simp only [List.nil_append, List.chain_cons] at h1
      apply h1
      constructor
      · unfold is_small_step_v1
        apply Exists.intro F'
        exact ⟨contra_left_left, contra_left_right⟩
      · simp only [List.Chain.nil]
  case cons hd tl ih =>
    sorry


-------------------------------------------------------------------------------


lemma is_subformula_imp_is_subformula_replace_atom_all_rec
  (F F' : Formula_)
  (σ : Instantiation)
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
  (F F' : Formula_)
  (σ : Instantiation)
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
      obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec F phi σ h1_left
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
        obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec F phi σ h1_left
        intro contra
        rewrite [contra] at s1
        simp only [replace_atom_all_rec] at s1
        first
        | exact not_is_subformula_and_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_or_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_imp_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_iff_left (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
      case inr h1_left =>
        obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec F psi σ h1_left
        intro contra
        rewrite [contra] at s1
        simp only [replace_atom_all_rec] at s1
        first
        | exact not_is_subformula_and_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_or_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_imp_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1
        | exact not_is_subformula_iff_right (replace_atom_all_rec σ phi) (replace_atom_all_rec σ psi) s1


lemma is_proper_subformula_v2_imp_is_proper_subformula_v2_replace_atom_all_rec
  (F F' : Formula_)
  (σ : Instantiation)
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
  (F F' : Formula_)
  (σ : Instantiation)
  (h1 : is_proper_subformula_v2 F F') :
  ¬ is_unifier σ { (F, F') } :=
  by
  unfold is_unifier
  simp only [Set.mem_singleton_iff]
  intro contra
  apply is_proper_subformula_v2_imp_replace_atom_all_rec_not_eq F F' σ
  · exact h1
  · specialize contra (F, F')
    simp only at contra
    apply contra
    exact trivial
