import HandbookOfPracticalLogicLean.Chapter2.Atom


set_option autoImplicit false


open Formula_


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


instance
  (E : List (String × Formula_))
  (X Y : String) :
  Decidable (is_small_step_v1 E X Y) :=
  by
  simp only [is_small_step_v1_iff_is_small_step_v2]
  infer_instance


-------------------------------------------------------------------------------


def is_big_step_v1
  (E : List (String × Formula_))
  (X Y : String)
  (l : List String) :
  Prop :=
  List.Chain (is_small_step_v1 E) X (l ++ [Y])

instance
  (E : List (String × Formula_))
  (X Y : String)
  (l : List String) :
  Decidable (is_big_step_v1 E X Y l) :=
  by
  unfold is_big_step_v1
  infer_instance


def has_cycle_v1
  (E : List (String × Formula_)) :
  Prop :=
  ∃ (X : String), ∃ (l : List String), is_big_step_v1 E X X l


-------------------------------------------------------------------------------


def env_to_step_list_aux
  (X : String)
  (F : Formula_) :
  List (String × String) :=
  List.map (fun (Y : String) => (X, Y)) (atom_list F)


def env_to_step_list :
  List (String × Formula_) → List (String × String)
  | [] => []
  | (X, F) :: tl => (env_to_step_list_aux X F) ++ (env_to_step_list tl)


lemma is_small_step_v1_imp_mem_env_to_step_list
  (E : List (String × Formula_))
  (X Y : String)
  (h1 : is_small_step_v1 E X Y) :
  (X, Y) ∈ env_to_step_list E :=
  by
  induction E
  case nil =>
    unfold is_small_step_v1 at h1
    obtain ⟨F, h1_left, h1_right⟩ := h1
    simp only [List.not_mem_nil] at h1_left
  case cons hd tl ih =>
    unfold is_small_step_v1 at h1
    obtain ⟨F, h1_left, h1_right⟩ := h1
    simp only [List.mem_cons] at h1_left

    unfold env_to_step_list
    unfold env_to_step_list_aux
    simp only [List.mem_append, List.mem_map, Prod.mk.injEq]
    cases h1_left
    case inl h1_left =>
      left
      apply Exists.intro Y
      rewrite [← h1_left]
      simp only
      simp only [← atom_occurs_in_iff_mem_atom_list]
      exact ⟨h1_right, ⟨trivial, trivial⟩⟩
    case inr h1_left =>
      right
      apply ih
      unfold is_small_step_v1
      apply Exists.intro F
      exact ⟨h1_left, h1_right⟩


lemma mem_env_to_step_list_imp_is_small_step_v1
  (E : List (String × Formula_))
  (X Y : String)
  (h1 : (X, Y) ∈ env_to_step_list E) :
  is_small_step_v1 E X Y :=
  by
  induction E
  case nil =>
    unfold env_to_step_list at h1
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    unfold env_to_step_list at h1
    unfold env_to_step_list_aux at h1
    simp only [List.mem_append, List.mem_map, Prod.mk.injEq] at h1

    unfold is_small_step_v1
    simp only [List.mem_cons]
    cases h1
    case inl h1 =>
      obtain ⟨Z, h1_left, ⟨h1_right_left, h1_right_right⟩⟩ := h1

      apply Exists.intro hd.snd
      rewrite [← h1_right_left]
      rewrite [← h1_right_right]
      constructor
      · left
        simp only [Prod.mk.eta]
      · simp only [atom_occurs_in_iff_mem_atom_list]
        exact h1_left
    case inr h1 =>
      specialize ih h1
      unfold is_small_step_v1 at ih
      obtain ⟨F, ih_left, ih_right⟩ := ih

      apply Exists.intro F
      constructor
      · right
        exact ih_left
      · exact ih_right


lemma is_small_step_v1_iff_mem_env_to_step_list
  (E : List (String × Formula_))
  (X Y : String) :
  is_small_step_v1 E X Y ↔ (X, Y) ∈ env_to_step_list E :=
  by
  constructor
  · apply is_small_step_v1_imp_mem_env_to_step_list
  · apply mem_env_to_step_list_imp_is_small_step_v1


-------------------------------------------------------------------------------


def List.prodChain
  {α : Type}
  (R : α → α → Prop)
  [DecidableRel R] :
  List (α × α) → Prop
  | [] => False
  | [_] => True
  | a :: b :: tl => R a.snd b.fst ∧ List.prodChain R (b :: tl)

instance
  {α : Type}
  (R : α → α → Prop)
  (l : List (α × α))
  (h1 : DecidableRel R) :
  Decidable (List.prodChain R l) :=
  by
  induction l
  case nil =>
    unfold List.prodChain
    infer_instance
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold List.prodChain
      infer_instance
    case cons tl_hd tl_tl =>
      unfold List.prodChain
      infer_instance


#eval List.prodChain (· = ·) [(0, 1)]
#eval List.prodChain (· = ·) [(0, 1), (1, 2)]
#eval List.prodChain (· = ·) [(0, 1), (2, 3)]
#eval List.prodChain (· = ·) [(0, 1), (1, 2), (2, 3)]
#eval List.prodChain (· = ·) [(0, 1), (1, 2), (3, 4)]


def List.prodCycle
  {α : Type}
  (R : α → α → Prop)
  [DecidableRel R]
  (l : List (α × α)) :
  Prop :=
  ∃ (a : α × α), a ∈ l ∧ R a.fst a.snd ∧ List.prodChain R l


-------------------------------------------------------------------------------


inductive List.is_cycle {α : Type} : (List (α × α)) → Prop
  | refl
    (a : α × α) :
    a.snd = a.fst →
    is_cycle [a]

  | trans
    (a b : α × α)
    (l : List (α × α)) :
    b.snd = a.fst →
    List.Chain' (fun (p1 p2 : α × α) => p1.snd = p2.fst) l →
    is_cycle (a :: (l ++ [b]))


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


lemma is_small_step_v1_singleton_left
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


lemma is_small_step_v1_singleton_right
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


lemma is_small_step_v1_singleton
  (X Y : String)
  (F : Formula_)
  (Z : String) :
  (is_small_step_v1 [(X, F)] Y Z) ↔ (Y = X ∧ atom_occurs_in Z F) :=
  by
  constructor
  · apply is_small_step_v1_singleton_left
  · intro a1
    obtain ⟨a1_left, a1_right⟩ := a1
    apply is_small_step_v1_singleton_right
    · exact a1_left
    · exact a1_right


-------------------------------------------------------------------------------


lemma is_small_step_v1_singleton_refl
  (X Y : String)
  (F : Formula_)
  (h1 : is_small_step_v1 [(X, F)] Y Y) :
  atom_occurs_in X F :=
  by
  simp only [is_small_step_v1_singleton] at h1
  obtain ⟨h1_left, h1_right⟩ := h1
  rewrite [← h1_left]
  exact h1_right


lemma is_small_step_v1_singleton_trans
  (X A B C : String)
  (F : Formula_)
  (h1 : is_small_step_v1 [(X, F)] A B)
  (h2 : is_small_step_v1 [(X, F)] B C) :
  is_small_step_v1 [(X, F)] A C :=
  by
  simp only [is_small_step_v1_singleton] at h1
  obtain ⟨h1_left, h1_right⟩ := h1

  simp only [is_small_step_v1_singleton] at h2
  obtain ⟨h2_left, h2_right⟩ := h2

  simp only [is_small_step_v1_singleton]
  exact ⟨h1_left, h2_right⟩


-------------------------------------------------------------------------------


lemma is_small_step_v1_append_left
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


lemma is_small_step_v1_append_right
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


lemma is_small_step_v1_append
  (E_1 E_2 : List (String × Formula_))
  (X Y : String) :
  (is_small_step_v1 (E_1 ++ E_2) X Y) ↔ (is_small_step_v1 E_1 X Y ∨ is_small_step_v1 E_2 X Y) :=
  by
  constructor
  · apply is_small_step_v1_append_left
  · apply is_small_step_v1_append_right


-------------------------------------------------------------------------------


lemma not_is_one_or_more_small_steps_nil
  (X Y : String)
  (l : List String) :
  ¬ is_big_step_v1 [] X Y l :=
  by
  unfold is_big_step_v1
  cases l
  case nil =>
    simp only [List.nil_append, List.chain_cons, List.Chain.nil]
    intro contra
    obtain ⟨contra_left, contra_right⟩ := contra
    simp only [not_is_small_step_nil] at contra_left
  case cons hd tl =>
    simp only [List.cons_append, List.chain_cons]
    intro contra
    obtain ⟨contra_left, contra_right⟩ := contra
    simp only [not_is_small_step_nil] at contra_left


lemma is_one_or_more_small_steps_trans
  (E : List (String × Formula_))
  (X Y Z : String)
  (l : List String)
  (h1 : ¬ l = [])
  (h2 : is_big_step_v1 E X Y l)
  (h3 : is_big_step_v1 E Y Z l) :
  is_big_step_v1 E X Z l :=
  by
  cases l
  case nil =>
    contradiction
  case cons hd tl =>
    unfold is_big_step_v1 at h2
    simp only [List.cons_append, List.chain_cons] at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    unfold is_big_step_v1 at h3
    simp only [List.cons_append, List.chain_cons] at h3
    obtain ⟨h3_left, h3_right⟩ := h3

    unfold is_big_step_v1
    simp only [List.cons_append, List.chain_cons]
    exact ⟨h2_left, h3_right⟩


lemma is_small_step_v1_is_one_or_more_small_steps_trans
  (X A B C : String)
  (F : Formula_)
  (l : List String)
  (h1 : is_small_step_v1 [(X, F)] A B)
  (h2 : is_big_step_v1 [(X, F)] B C l) :
  is_small_step_v1 [(X, F)] A C :=
  by
  unfold is_big_step_v1 at h2
  induction l generalizing B
  case nil =>
    simp only [List.nil_append, List.chain_cons, List.Chain.nil] at h2
    obtain ⟨h2_left, h2_right⟩ := h2
    apply is_small_step_v1_singleton_trans X A B
    · exact h1
    · exact h2_left
  case cons hd tl ih =>
    simp only [List.cons_append, List.chain_cons] at h2
    obtain ⟨h2_left, h2_right⟩ := h2
    apply ih hd
    · apply is_small_step_v1_singleton_trans X A B
      · exact h1
      · exact h2_left
    · exact h2_right


lemma is_one_or_more_small_steps_singleton_contract
  (X Y Z : String)
  (F : Formula_)
  (l : List String)
  (h1 : is_big_step_v1 [(X, F)] Y Z l) :
  is_small_step_v1 [(X, F)] Y Z :=
  by
  unfold is_big_step_v1 at h1
  induction l
  case nil =>
    simp only [List.nil_append, List.chain_cons, List.Chain.nil] at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    exact h1_left
  case cons hd tl ih =>
    simp only [List.cons_append, List.chain_cons] at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    apply is_small_step_v1_is_one_or_more_small_steps_trans X Y hd Z F tl
    · exact h1_left
    · unfold is_big_step_v1
      exact h1_right


-------------------------------------------------------------------------------


lemma not_has_cycle_nil :
  ¬ has_cycle_v1 [] :=
  by
  unfold has_cycle_v1
  simp only [not_exists]
  intro X l contra
  unfold is_big_step_v1 at contra
  cases l
  case nil =>
    simp only [List.nil_append, List.chain_cons, List.Chain.nil] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    exact not_is_small_step_nil X X contra_left
  case cons hd tl =>
    simp only [List.cons_append, List.chain_cons] at contra
    obtain ⟨contra_left, contra_right⟩ := contra
    exact not_is_small_step_nil X hd contra_left


-------------------------------------------------------------------------------


lemma has_cycle_singleton_left
  (X : String)
  (F : Formula_)
  (h1 : has_cycle_v1 [(X, F)]) :
  atom_occurs_in X F :=
  by
  unfold has_cycle_v1 at h1
  unfold is_big_step_v1 at h1
  obtain ⟨Y, l, h1⟩ := h1
  cases l
  case nil =>
    simp only [List.nil_append, List.chain_cons, List.Chain.nil] at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    apply is_small_step_v1_singleton_refl X Y
    exact h1_left
  case cons hd tl =>
    simp only [List.cons_append, List.chain_cons] at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    apply is_small_step_v1_singleton_refl X Y
    apply is_small_step_v1_is_one_or_more_small_steps_trans X Y hd Y F tl
    · exact h1_left
    · unfold is_big_step_v1
      exact h1_right


lemma has_cycle_singleton_right
  (X : String)
  (F : Formula_)
  (h1 : atom_occurs_in X F) :
  has_cycle_v1 [(X, F)] :=
  by
  unfold has_cycle_v1
  apply Exists.intro X
  apply Exists.intro []
  unfold is_big_step_v1
  simp only [List.nil_append, List.chain_cons, List.Chain.nil]
  simp only [is_small_step_v1_singleton]
  exact ⟨⟨trivial, h1⟩, trivial⟩


lemma has_cycle_singleton
  (X : String)
  (F : Formula_) :
  has_cycle_v1 [(X, F)] ↔ atom_occurs_in X F :=
  by
  constructor
  · apply has_cycle_singleton_left
  · apply has_cycle_singleton_right


-------------------------------------------------------------------------------


lemma is_small_step_v1_refl_imp_has_cycle
  (E : List (String × Formula_))
  (X : String)
  (h1 : is_small_step_v1 E X X) :
  has_cycle_v1 E :=
  by
  unfold has_cycle_v1
  apply Exists.intro X
  apply Exists.intro []
  unfold is_big_step_v1
  simp only [List.nil_append, List.chain_cons, List.Chain.nil]
  exact ⟨h1, trivial⟩


example
  (E : List (String × Formula_))
  (X Y : String)
  (F : Formula_)
  (l : List String)
  (h1 : is_big_step_v1 ((X, F) :: E) Y Y l)
  (h2 : ¬ atom_occurs_in X F)
  (h3 : ¬ has_cycle_v1 E) :
  sorry :=
  by
  induction l
  case nil =>
    unfold is_big_step_v1 at h1
    simp only [List.nil_append, List.chain_cons, List.Chain.nil] at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    rewrite [← List.singleton_append] at h1_left
    simp only [is_small_step_v1_append] at h1_left

    cases h1_left
    case inl h1_left =>
      obtain s1 := is_small_step_v1_singleton_refl X Y F h1_left
      contradiction
    case inr h1_left =>
      obtain s1 := is_small_step_v1_refl_imp_has_cycle E Y h1_left
      contradiction
  case cons hd tl ih =>
    unfold is_big_step_v1 at h1
    simp only [List.cons_append, List.chain_cons] at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    rewrite [← List.singleton_append] at h1_left
    simp only [is_small_step_v1_append] at h1_left

    unfold has_cycle_v1 at h3
    simp only [not_exists] at h3
    unfold is_big_step_v1 at h3

    unfold is_big_step_v1 at ih

    cases h1_left
    case inl h1_left =>
      unfold is_small_step_v1 at h1_left
      simp only [List.mem_singleton, Prod.mk.injEq] at h1_left
      obtain ⟨F', ⟨h1_left_left_left, h1_left_left_right⟩ , h1_left_right⟩ := h1_left
      rewrite [h1_left_left_left] at h1_right
      rewrite [h1_left_left_left] at ih
      rewrite [h1_left_left_right] at h1_left_right
      sorry
    case inr h1_left =>
      unfold is_small_step_v1 at h1_left
      obtain ⟨F', h1_left_left, h1_left_right⟩ := h1_left
      sorry


example
  (E : List (String × Formula_))
  (X : String)
  (F : Formula_)
  (h1 : has_cycle_v1 ((X, F) :: E))
  (h2 : ¬ atom_occurs_in X F)
  (h3 : ¬ has_cycle_v1 E) :
  ∃ (Y : String), ∃ (l : List String), atom_occurs_in Y F ∧ is_big_step_v1 E Y X l :=
  by
  unfold has_cycle_v1 at h1
  obtain ⟨Y, l, h1⟩ := h1

  induction l
  case nil =>
    unfold is_big_step_v1 at h1
    simp only [List.nil_append, List.chain_cons, List.Chain.nil] at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    rewrite [← List.singleton_append] at h1_left
    simp only [is_small_step_v1_append] at h1_left

    cases h1_left
    case inl h1_left =>
      exfalso
      apply h2
      apply is_small_step_v1_singleton_refl X Y
      exact h1_left
    case inr h1_left =>
      exfalso
      apply h3
      apply is_small_step_v1_refl_imp_has_cycle E Y
      exact h1_left
  case cons hd tl ih =>
    unfold is_big_step_v1 at h1
    simp only [List.cons_append, List.chain_cons] at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    rewrite [← List.singleton_append] at h1_left
    simp only [is_small_step_v1_append] at h1_left

    cases h1_left
    case inl h1_left =>
      simp only [is_small_step_v1_singleton] at h1_left
      obtain ⟨h1_left_left, h1_left_right⟩ := h1_left
      apply Exists.intro hd
      apply Exists.intro tl
      constructor
      · exact h1_left_right
      · unfold is_big_step_v1
        rewrite [← h1_left_left]
        sorry
    case inr h1_left =>
      apply ih
      sorry


example
  (E : List (String × Formula_))
  (X : String)
  (F : Formula_)
  (h1 : ¬ has_cycle_v1 E)
  (h2 : ¬ atom_occurs_in X F)
  (h3 : ∀ (Y : String), ∀ (l : List String), atom_occurs_in Y F → ¬ is_big_step_v1 E Y X l) :
  ¬ has_cycle_v1 ((X, F) :: E) :=
  by
  unfold has_cycle_v1 at h1
  simp only [not_exists] at h1
  unfold is_big_step_v1 at h1

  unfold is_big_step_v1 at h3

  unfold has_cycle_v1
  simp only [not_exists]
  intro Y l contra
  unfold is_big_step_v1 at contra

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
