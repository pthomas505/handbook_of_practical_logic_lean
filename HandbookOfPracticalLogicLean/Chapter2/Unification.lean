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


theorem not_is_small_step_singleton_refl
  (X Y : String)
  (F : Formula_)
  (h1 : ¬ atom_occurs_in X F) :
  ¬ is_small_step_v1 [(X, F)] Y Y :=
  by
  unfold is_small_step_v1
  simp only [not_exists]
  simp only [List.mem_singleton, Prod.mk.injEq]
  intro F' contra
  obtain ⟨⟨contra_left_left, contra_left_right⟩, contra_right⟩ := contra
  apply h1
  rewrite [← contra_left_left]
  rewrite [← contra_left_right]
  exact contra_right


lemma not_nil_not_eq_imp_not_is_one_or_more_small_steps_singleton
  (X Y : String)
  (F : Formula_)
  (l : List String)
  (h1 : ¬ l = [])
  (h2 : ¬ Y = X) :
  ¬ List.Chain (is_small_step_v1 [(X, F)]) Y l :=
  by
  intro contra
  cases l
  case nil =>
    contradiction
  case cons hd tl =>
    simp only [List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    unfold is_small_step_v1 at contra_left
    obtain ⟨F', contra_left_left, contra_left_right⟩ := contra_left
    simp only [List.mem_singleton, Prod.mk.injEq] at contra_left_left
    obtain ⟨contra_left_left_left, contra_left_left_right⟩ := contra_left_left
    contradiction


example
  (X : String)
  (F : Formula_)
  (h1 : ¬ atom_occurs_in X F) :
  ¬ has_cycle [(X, F)] :=
  by
  unfold has_cycle
  simp only [not_exists]
  intro Y l contra
  unfold is_one_or_more_small_steps at contra
  induction l
  case nil =>
    simp only [List.nil_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    exact not_is_small_step_singleton_refl X Y F h1 contra_left
  case cons hd tl ih =>
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
  unfold has_cycle
  simp only [not_exists]
  intro Y l contra
  unfold is_one_or_more_small_steps at contra
  induction l
  case nil =>
    simp only [List.nil_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    unfold is_small_step_v1 at contra_left
    sorry
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
  case and_ phi psi =>
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
        sorry
      case inr h1_left =>
        obtain s1 := is_subformula_imp_is_subformula_replace_atom_all_rec F psi σ h1_left
        intro contra
        rewrite [contra] at s1
        simp only [replace_atom_all_rec] at s1
        sorry
  all_goals
    sorry


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
