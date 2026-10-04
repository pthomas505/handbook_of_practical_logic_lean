import HandbookOfPracticalLogicLean.Prop.NF.DNF.ToDNF_3_Simp_1
import HandbookOfPracticalLogicLean.Prop.NF.NNF.NNF_1


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


open Formula_


/-
  If `PS` and `QS` are lists of formulas, and `PS` is a subset of `QS`, then the evaluation of the disjunction of the conjunction of the formulas in `PS` and the conjunction of the formulas in `QS` is true if and only if the evaluation of the conjunction of the formulas in `PS` is true. Hence the conjunction of the formulas in `QS` can be removed from the disjuction.
-/


/--
  `filter_not_has_proper_subset_in_v1 ll` := The result of removing every list that has a proper subset in the list of lists `ll` from the list of lists `ll`.
-/
@[nolint defsWithUnderscore]
def filter_not_has_proper_subset_in_v1
  {α : Type}
  [DecidableEq α]
  (ll : List (List α)) :
  List (List α) :=
  ll.filter fun (l1 : List α) => ∀ (l2 : List α), l2 ∈ ll → (l2 ⊆ l1 → l1 ⊆ l2)

example : filter_not_has_proper_subset_in_v1 [[1], [1]] = [[1], [1]] := by apply Eq.refl
example : filter_not_has_proper_subset_in_v1 [[1], [2]] = [[1], [2]] := by apply Eq.refl
example : filter_not_has_proper_subset_in_v1 [[2], [1]] = [[2], [1]] := by apply Eq.refl
example : filter_not_has_proper_subset_in_v1 [[1], [1, 2]] = [[1]] := by apply Eq.refl
example : filter_not_has_proper_subset_in_v1 [[1, 2], [1]] = [[1]] := by apply Eq.refl
example : filter_not_has_proper_subset_in_v1 [[1], [1, 2, 2]] = [[1]] := by apply Eq.refl
example : filter_not_has_proper_subset_in_v1 [[1, 2, 2], [1]] = [[1]] := by apply Eq.refl
example : filter_not_has_proper_subset_in_v1 [[1], [1, 1, 2]] = [[1]] := by apply Eq.refl
example : filter_not_has_proper_subset_in_v1 [[1, 1, 2], [1]] = [[1]] := by apply Eq.refl
example : filter_not_has_proper_subset_in_v1 [[1], [1, 2], [2, 3]] = [[1], [2, 3]] := by apply Eq.refl
example : filter_not_has_proper_subset_in_v1 [[1], [2, 3], [1, 2]] = [[1], [2, 3]] := by apply Eq.refl


/--
  `List.is_proper_subset_of l1 l2` := True if and only if `l1` is a proper subset of `l2`.
-/
@[nolint defsWithUnderscore]
def List.is_proper_subset_of
  {α : Type}
  (l1 l2 : List α) :
  Prop :=
  l1 ⊆ l2 ∧ ¬ l2 ⊆ l1

@[nolint defsWithUnderscore]
instance
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List α) :
  Decidable (List.is_proper_subset_of l1 l2) :=
  by
  unfold List.is_proper_subset_of
  infer_instance


/--
  `filter_not_has_proper_subset_in_v2 ll` := The result of removing every list that has a proper subset in the list of lists `ll` from the list of lists `ll`.
-/
@[nolint defsWithUnderscore]
def filter_not_has_proper_subset_in_v2
  {α : Type}
  [DecidableEq α]
  (ll : List (List α)) :
  List (List α) :=
  List.filter (fun (l1 : List α) => ¬ (∃ (l2 : List α), l2 ∈ ll ∧ List.is_proper_subset_of l2 l1)) ll


/--
  `List.dedupSet ll` := The result of removing all except the last occurrence of multiple occurences of lists with identical sets of elements from the list of lists `ll`.
-/
def List.dedupSet
  {α : Type}
  [DecidableEq α]
  (ll : List (List α)) :
  List (List α) :=
  ll.pwFilter fun (l1 l2 : List α) => ¬ (l1 ⊆ l2 ∧ l2 ⊆ l1)

example : List.dedupSet [[1]] = [[1]] := by apply Eq.refl
example : List.dedupSet [[1], [1]] = [[1]] := by apply Eq.refl
example : List.dedupSet [[1], [1], [1]] = [[1]] := by apply Eq.refl

example : List.dedupSet [[1], [2]] = [[1], [2]] := by apply Eq.refl
example : List.dedupSet [[2], [1]] = [[2], [1]] := by apply Eq.refl

example : List.dedupSet [[1], [2], [1]] = [[2], [1]] := by apply Eq.refl
example : List.dedupSet [[2], [1], [2]] = [[1], [2]] := by apply Eq.refl

example : List.dedupSet [[1, 2], [2, 1, 1]] = [[2, 1, 1]] := by apply Eq.refl


example
  (σ : ValuationAsTotalFunction)
  (P Q : Formula_)
  (h1 : eval σ Q = true → eval σ P = true) :
  eval σ (or_ P Q) = true ↔ eval σ P = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_or]
  constructor
  · intro a1
    cases a1
    case inl a1 =>
      exact a1
    case inr a1 =>
      apply h1
      exact a1
  · intro a1
    left
    exact a1


example
  (σ : ValuationAsTotalFunction)
  (PS QS : List Formula_)
  (h1 : PS ⊆ QS) :
  eval σ (or_ (list_conj PS) (list_conj QS)) = true ↔
    eval σ (list_conj PS) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_or]
  constructor
  · intro a1
    cases a1
    case inl a1 =>
      exact a1
    case inr a1 =>
      apply eval_list_conj_subset σ PS QS
      · exact h1
      · exact a1
  · intro a1
    left
    exact a1


example
  (σ : ValuationAsTotalFunction)
  (P : Formula_)
  (FS : List Formula_)
  (h1 : P ∈ FS) :
  eval σ (list_disj FS) = true ↔
    eval σ (list_disj (List.filter (fun (Q : Formula_) => Q = P ∨ ¬ (eval σ Q = true → eval σ P = true)) FS)) = true :=
  by
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_filter]
  simp only [decide_eq_true_iff]
  constructor
  · intro a1
    obtain ⟨F, a1_left, a1_right⟩ := a1
    by_cases c1 : eval σ F = true → eval σ P = true
    · apply Exists.intro P
      constructor
      · constructor
        · exact h1
        · left
          apply Eq.refl
      · apply c1
        exact a1_right
    · apply Exists.intro F
      constructor
      · constructor
        · exact a1_left
        · right
          exact c1
      · exact a1_right
  · intro a1
    obtain ⟨F, ⟨a1_left_left, a1_left_right⟩, a1_right⟩ := a1
    apply Exists.intro F
    exact ⟨a1_left_left, a1_right⟩


example
  (σ : ValuationAsTotalFunction)
  (PS : List Formula_)
  (FSS : List (List Formula_))
  (h1 : PS ∈ FSS) :
  eval σ (list_of_lists_to_disjunction_of_conjunctions FSS) = true ↔
    eval σ (list_of_lists_to_disjunction_of_conjunctions (List.filter (fun (QS : List Formula_) => ¬ List.is_proper_subset_of PS QS) FSS)) = true :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_map, List.mem_filter]
  simp only [decide_eq_true_iff]
  constructor
  · intro a1
    obtain ⟨F, ⟨QS, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
    by_cases c1 : List.is_proper_subset_of PS QS
    · apply Exists.intro (list_conj PS)
      constructor
      · apply Exists.intro PS
        constructor
        · constructor
          · exact h1
          · unfold List.is_proper_subset_of
            intro contra
            obtain ⟨contra_left, contra_right⟩ := contra
            contradiction
        · apply Eq.refl
      · unfold List.is_proper_subset_of at c1
        obtain ⟨c1_left, c1_right⟩ := c1
        rewrite [← a1_left_right] at a1_right
        apply eval_list_conj_subset σ PS QS
        · exact c1_left
        · exact a1_right
    · exact ⟨F, ⟨QS, ⟨a1_left_left, c1⟩, a1_left_right⟩, a1_right⟩
  · intro a1
    obtain ⟨F, ⟨QS, ⟨a1_left_left_left, a1_left_left_right⟩, a1_left_right⟩, a1_right⟩ := a1
    exact ⟨F, ⟨QS, a1_left_left_left, a1_left_right⟩, a1_right⟩


example
  (σ : ValuationAsTotalFunction)
  (P Q : Formula_)
  (FS : List Formula_)
  (h1 : P ∈ FS)
  (h2 : Q ∈ FS) :
  eval σ (list_disj FS) = true ↔
    eval σ (list_disj (List.filter (fun (R : Formula_) => R = P ∨ R = Q ∨ (¬ (eval σ R = true → eval σ P = true) ∧ ¬ (eval σ R = true → eval σ Q = true))) FS)) = true :=
  by
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_filter]
  simp only [decide_eq_true_iff]
  constructor
  · intro a1
    obtain ⟨F, a1_left, a1_right⟩ := a1
    by_cases c1 : eval σ F = true → eval σ P = true
    · apply Exists.intro P
      constructor
      · constructor
        · exact h1
        · left
          apply Eq.refl
      · apply c1
        exact a1_right
    · by_cases c2 : eval σ F = true → eval σ Q = true
      · apply Exists.intro Q
        constructor
        · constructor
          · exact h2
          · right
            left
            apply Eq.refl
        · apply c2
          exact a1_right
      · apply Exists.intro F
        constructor
        · constructor
          · exact a1_left
          · right
            right
            exact ⟨c1, c2⟩
        · exact a1_right
  · intro a1
    obtain ⟨F, ⟨a1_left_left, a1_left_right⟩, a1_right⟩ := a1
    exact ⟨F, a1_left_left, a1_right⟩


example
  (σ : ValuationAsTotalFunction)
  (PS QS : List Formula_)
  (h1 : PS ⊆ QS) :
  eval σ (list_of_lists_to_disjunction_of_conjunctions [PS, QS]) = true ↔
    eval σ (list_of_lists_to_disjunction_of_conjunctions [PS]) = true :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions
  simp only [List.map_cons, List.map_nil]
  simp only [list_disj]
  simp only [eval]
  simp only [bool_iff_prop_or]
  constructor
  · intro a1
    cases a1
    case inl a1 =>
      exact a1
    case inr a1 =>
      apply eval_list_conj_subset σ PS QS
      · exact h1
      · exact a1
  · intro a1
    left
    exact a1


example
  (σ : ValuationAsTotalFunction)
  (PS QS RS : List Formula_)
  (h1 : PS ⊆ QS)
  (h2 : QS ⊆ RS) :
  eval σ (list_of_lists_to_disjunction_of_conjunctions [PS, QS, RS]) = true ↔
    eval σ (list_of_lists_to_disjunction_of_conjunctions [PS]) = true :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions
  simp only [List.map_cons, List.map_nil]
  simp only [list_disj]
  simp only [eval]
  simp only [bool_iff_prop_or]
  constructor
  · intro a1
    cases a1
    case inl a1 =>
      exact a1
    case inr a1 =>
      cases a1
      case inl a1 =>
        apply eval_list_conj_subset σ PS QS
        · exact h1
        · exact a1
      case inr a1 =>
        apply eval_list_conj_subset σ PS RS
        · trans QS
          · exact h1
          · exact h2
        · exact a1
  · intro a1
    left
    exact a1


example
  (σ : ValuationAsTotalFunction)
  (PS QS RS : List Formula_)
  (h1 : PS ⊆ RS) :
  eval σ (list_of_lists_to_disjunction_of_conjunctions [PS, QS, RS]) = true ↔
    eval σ (list_of_lists_to_disjunction_of_conjunctions [PS, QS]) = true :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions
  simp only [List.map_cons, List.map_nil]
  simp only [list_disj]
  simp only [eval]
  simp only [bool_iff_prop_or]
  constructor
  · intro a1
    cases a1
    case inl a1 =>
      left
      exact a1
    case inr a1 =>
      cases a1
      case inl a1 =>
        right
        exact a1
      case inr a1 =>
        left
        apply eval_list_conj_subset σ PS RS
        · exact h1
        · exact a1
  · intro a1
    cases a1
    case inl a1 =>
      left
      exact a1
    case inr a1 =>
      right
      left
      exact a1


example
  (σ : ValuationAsTotalFunction)
  (P Q : Formula_)
  (h1 : eval σ Q = true → eval σ P = true) :
  eval σ (list_disj [P, Q]) = true ↔
    eval σ (list_disj [P]) = true :=
  by
  simp only [list_disj]
  simp only [eval]
  simp only [bool_iff_prop_or]
  constructor
  · intro a1
    cases a1
    case inl a1 =>
      exact a1
    case inr a1 =>
      apply h1
      exact a1
  · intro a1
    left
    exact a1


example
  (σ : ValuationAsTotalFunction)
  (FS : List Formula_) :
  eval σ (list_disj FS) = true ↔
    eval σ (list_disj (List.dedup FS)) = true :=
  by
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_dedup]


#eval let FSS : List (List Formula_):= [[]]; (filter_not_has_proper_subset_in_v2 FSS).toString

#eval let FSS := [[var_ "P"]]; (filter_not_has_proper_subset_in_v2 FSS).toString

#eval let FSS := [[var_ "P"], []]; (filter_not_has_proper_subset_in_v2 FSS).toString

#eval let FSS := [[var_ "P"], [var_ "P"]]; (filter_not_has_proper_subset_in_v2 FSS).toString

#eval let FSS := [[var_ "P"], [var_ "P", var_ "Q"]]; (filter_not_has_proper_subset_in_v2 FSS).toString


-------------------------------------------------------------------------------


theorem eval_filter_not_has_proper_subset_in_v2_left
  (σ : ValuationAsTotalFunction)
  (FSS : List (List Formula_))
  (h1 : eval σ (list_of_lists_to_disjunction_of_conjunctions FSS) = true) :
  eval σ (list_of_lists_to_disjunction_of_conjunctions (filter_not_has_proper_subset_in_v2 FSS)) = true :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions at h1
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true] at h1
  obtain ⟨F, h1_left, h1_right⟩ := h1
  simp only [List.mem_map] at h1_left
  obtain ⟨RS, h1_left_left, h1_left_right⟩ := h1_left
  rewrite [← h1_left_right] at h1_right

  unfold filter_not_has_proper_subset_in_v2
  unfold list_of_lists_to_disjunction_of_conjunctions
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_map, List.mem_filter]
  simp only [decide_eq_true_iff]

  simp only [not_exists]
  simp only [not_and]

  obtain ⟨PS, s1_left, ⟨s1_right_left, s1_right_right⟩⟩ := List.exists_minimal_subset_of_mem FSS RS h1_left_left
  apply Exists.intro (list_conj PS)
  constructor
  · apply Exists.intro PS
    constructor
    · constructor
      · exact s1_left
      · intro QS a1 contra
        unfold List.is_proper_subset_of at contra
        obtain ⟨contra_left, contra_right⟩ := contra
        apply contra_right
        apply s1_right_right
        constructor
        · exact a1
        · exact contra_left
    · apply Eq.refl
  · exact eval_list_conj_subset σ PS RS s1_right_left h1_right


theorem eval_list_of_lists_to_disjunction_of_conjunctions_subset
  (σ : ValuationAsTotalFunction)
  (PSS QSS : List (List Formula_))
  (h1 : PSS ⊆ QSS)
  (h2 : eval σ (list_of_lists_to_disjunction_of_conjunctions PSS) = true) :
  eval σ (list_of_lists_to_disjunction_of_conjunctions QSS) = true :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions at h2
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true] at h2
  simp only [List.mem_map] at h2
  obtain ⟨F, ⟨PS, h2_left_left, h2_left_right⟩, h2_right⟩ := h2

  unfold list_of_lists_to_disjunction_of_conjunctions
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_map]
  apply Exists.intro F
  constructor
  · apply Exists.intro PS
    constructor
    · exact h1 h2_left_left
    · exact h2_left_right
  · exact h2_right


theorem eval_filter_not_has_proper_subset_in_v2_right
  (σ : ValuationAsTotalFunction)
  (FSS : List (List Formula_))
  (h1 : eval σ (list_of_lists_to_disjunction_of_conjunctions (filter_not_has_proper_subset_in_v2 FSS)) = true) :
  eval σ (list_of_lists_to_disjunction_of_conjunctions FSS) = true :=
  by
  apply eval_list_of_lists_to_disjunction_of_conjunctions_subset σ (filter_not_has_proper_subset_in_v2 FSS)
  · unfold filter_not_has_proper_subset_in_v2
    simp only [List.filter_subset_self]
  · exact h1


theorem eval_filter_not_has_proper_subset_in_v2
  (σ : ValuationAsTotalFunction)
  (FSS : List (List Formula_)) :
  eval σ (list_of_lists_to_disjunction_of_conjunctions FSS) = true ↔
    eval σ (list_of_lists_to_disjunction_of_conjunctions (filter_not_has_proper_subset_in_v2 FSS)) = true :=
  by
  constructor
  · apply eval_filter_not_has_proper_subset_in_v2_left
  · apply eval_filter_not_has_proper_subset_in_v2_right


-------------------------------------------------------------------------------


theorem filter_not_has_proper_subset_in_v2_is_dnf_ind_v1
  (FSS : List (List Formula_))
  (h1 : is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions FSS)) :
  is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions (filter_not_has_proper_subset_in_v2 FSS)) :=
  by
  unfold filter_not_has_proper_subset_in_v2
  apply is_dnf_ind_v1_list_of_lists_to_disjunction_of_conjunctions_filter
  exact h1


-------------------------------------------------------------------------------


/--
  Helper function for `to_dnf_v3_simp`.
-/
@[nolint defsWithUnderscore]
def to_dnf_v3_simp_aux
  (F : Formula_) :
  List (List Formula_) :=
  if F = false_
  then []
  else
    if F = true_
    then [[]]
    else
      let djs : List (List Formula_) := to_dnf_v3_aux_simp_1 (to_nnf_v1 F)
      (filter_not_has_proper_subset_in_v2 djs)


/--
  `to_dnf_v3_simp F` := Translates the formula `F` to a simplified logically equivalent formula in disjunctive normal form.
-/
@[nolint defsWithUnderscore]
def to_dnf_v3_simp
  (F : Formula_) :
  Formula_ :=
  list_of_lists_to_disjunction_of_conjunctions (to_dnf_v3_simp_aux F)


example
  (σ : ValuationAsTotalFunction)
  (F : Formula_) :
  eval σ F = true ↔ eval σ (to_dnf_v3_simp F) = true :=
  by
  unfold to_dnf_v3_simp
  unfold to_dnf_v3_simp_aux
  split
  case isTrue c1 =>
    rewrite [c1]
    unfold list_of_lists_to_disjunction_of_conjunctions
    simp only [List.map_nil]
    unfold list_disj
    apply Iff.refl
  case isFalse c1 =>
    split
    case isTrue c2 =>
      rewrite [c2]
      unfold list_of_lists_to_disjunction_of_conjunctions
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      unfold list_disj
      apply Iff.refl
    case isFalse c2 =>
    simp only
    simp only [← eval_filter_not_has_proper_subset_in_v2]
    simp only [← eval_eq_eval_to_dnf_v3_simp_1_aux]
    simp only [← eval_eq_eval_to_nnf_v1]


example
  (F : Formula_) :
  is_dnf_ind_v1 (to_dnf_v3_simp F) :=
  by
  unfold to_dnf_v3_simp
  unfold to_dnf_v3_simp_aux
  split
  case isTrue c1 =>
    unfold list_of_lists_to_disjunction_of_conjunctions
    simp only [List.map_nil]
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    exact is_constant_ind.rule_1
  case isFalse c1 =>
    split
    case isTrue c2 =>
      unfold list_of_lists_to_disjunction_of_conjunctions
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      unfold list_disj
      apply is_dnf_ind_v1.rule_1
      apply is_conj_ind_v1.rule_1
      exact is_constant_ind.rule_2
    case isFalse c2 =>
      simp only
      apply filter_not_has_proper_subset_in_v2_is_dnf_ind_v1
      apply is_dnf_ind_v1_to_dnf_v3_simp_1_aux
      apply to_nnf_v1_is_nnf_rec_v1


#lint
