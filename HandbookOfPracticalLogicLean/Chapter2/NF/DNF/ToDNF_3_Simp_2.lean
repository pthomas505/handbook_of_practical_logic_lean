import HandbookOfPracticalLogicLean.Chapter2.NF.DNF.ToDNF_3_Simp_1
import HandbookOfPracticalLogicLean.Chapter2.NF.NNF.NNF_1


set_option autoImplicit false


open Formula_


/--
  `filterMin ll` := The result of removing from the list of lists `ll` every list that is a proper superset of some list in `ll`.
-/
def filterMin
  {α : Type}
  [DecidableEq α]
  (ll : List (List α)) :
  List (List α) :=
  ll.filter fun (l1 : List α) => ∀ (l2 : List α), l2 ∈ ll → (l2 ⊆ l1 → l1 ⊆ l2)

example : filterMin [[1], [1]] = [[1], [1]] := by rfl
example : filterMin [[1], [2]] = [[1], [2]] := by rfl
example : filterMin [[2], [1]] = [[2], [1]] := by rfl
example : filterMin [[1], [1, 2]] = [[1]] := by rfl
example : filterMin [[1, 2], [1]] = [[1]] := by rfl
example : filterMin [[1], [1, 2], [2, 3]] = [[1], [2, 3]] := by rfl
example : filterMin [[1], [2, 3], [1, 2]] = [[1], [2, 3]] := by rfl


/--
  `List.dedupSet ll` := The result of removing all except the last occurrence of multiple occurences of lists with identical sets of elements from the list of lists `ll`.
-/
def List.dedupSet
  {α : Type}
  [DecidableEq α]
  (ll : List (List α)) :
  List (List α) :=
  ll.pwFilter fun (l1 l2 : List α) => ¬ (l1 ⊆ l2 ∧ l2 ⊆ l1)

example : List.dedupSet [[1]] = [[1]] := by rfl
example : List.dedupSet [[1], [1]] = [[1]] := by rfl
example : List.dedupSet [[1], [1], [1]] = [[1]] := by rfl

example : List.dedupSet [[1], [2]] = [[1], [2]] := by rfl
example : List.dedupSet [[2], [1]] = [[2], [1]] := by rfl

example : List.dedupSet [[1, 2], [2, 1, 1]] = [[2, 1, 1]] := by rfl


/--
  `List.SSubset l1 l2` := True if and only if `l1` is a strict subset of `l2`.
-/
def List.SSubset
  {α : Type}
  (l1 l2 : List α) :
  Prop :=
  l1 ⊆ l2 ∧ ¬ l2 ⊆ l1

instance
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List α) :
  Decidable (List.SSubset l1 l2) :=
  by
  unfold List.SSubset
  infer_instance


/--
  `pure_dnf_simp_2 FSS` := The result of removing from the list of lists of formulas `FSS` every list of formulas that is a proper superset of some list of formulas in `ll`.

  If `PS` and `QS` are lists of formulas, and `PS` is a subset of `QS`, then the evaluation of the disjunction of the conjunction of the formulas in `PS` and the conjunction of the formulas in `QS` is true if and only if the evaluation of the conjunction of the formulas in `PS` is true. Hence the conjunction of the formulas in `QS` can be removed from the disjuction.
-/
def pure_dnf_simp_2
  (FSS : List (List Formula_)) :
  List (List Formula_) :=
  List.filter (fun (QS : List Formula_) => ¬ (∃ (PS : List Formula_), PS ∈ FSS ∧ List.SSubset PS QS)) FSS


example
  (V : ValuationAsTotalFunction)
  (P Q : Formula_)
  (h1 : eval V Q = true → eval V P = true) :
  eval V (or_ P Q) = true ↔ eval V P = true :=
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
  (V : ValuationAsTotalFunction)
  (PS QS : List Formula_)
  (h1 : PS ⊆ QS) :
  eval V (or_ (list_conj PS) (list_conj QS)) = true ↔
    eval V (list_conj PS) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_or]
  constructor
  · intro a1
    cases a1
    case inl a1 =>
      exact a1
    case inr a1 =>
      exact eval_list_conj_subset V PS QS h1 a1
  · intro a1
    left
    exact a1


example
  (V : ValuationAsTotalFunction)
  (P : Formula_)
  (FS : List Formula_)
  (h1 : P ∈ FS) :
  eval V (list_disj FS) = true ↔
    eval V (list_disj (List.filter (fun (Q : Formula_) => Q = P ∨ ¬ (eval V Q = true → eval V P = true)) FS)) = true :=
  by
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_filter]
  simp only [decide_eq_true_iff]
  constructor
  · intro a1
    obtain ⟨F, a1_left, a1_right⟩ := a1
    by_cases c1 : eval V F = true → eval V P = true
    case pos =>
      apply Exists.intro P
      constructor
      · constructor
        · exact h1
        · left
          rfl
      · apply c1
        exact a1_right
    case neg =>
      apply Exists.intro F
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
  (V : ValuationAsTotalFunction)
  (PS : List Formula_)
  (FSS : List (List Formula_))
  (h1 : PS ∈ FSS) :
  eval V (list_of_lists_to_disjunction_of_conjunctions FSS) = true ↔
    eval V (list_of_lists_to_disjunction_of_conjunctions (List.filter (fun (QS : List Formula_) => ¬ List.SSubset PS QS) FSS)) = true :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_map, List.mem_filter]
  simp only [decide_eq_true_iff]
  constructor
  · intro a1
    obtain ⟨F, ⟨QS, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
    by_cases c1 : List.SSubset PS QS
    case pos =>
      apply Exists.intro (list_conj PS)
      constructor
      · apply Exists.intro PS
        constructor
        · constructor
          · exact h1
          · unfold List.SSubset
            intro contra
            obtain ⟨contra_left, contra_right⟩ := contra
            contradiction
        · rfl
      · unfold List.SSubset at c1
        obtain ⟨c1_left, c1_right⟩ := c1
        rewrite [← a1_left_right] at a1_right
        apply eval_list_conj_subset V PS QS
        · exact c1_left
        · exact a1_right
    case neg =>
      exact ⟨F, ⟨QS, ⟨a1_left_left, c1⟩, a1_left_right⟩, a1_right⟩
  · intro a1
    obtain ⟨F, ⟨QS, ⟨a1_left_left_left, a1_left_left_right⟩, a1_left_right⟩, a1_right⟩ := a1
    exact ⟨F, ⟨QS, a1_left_left_left, a1_left_right⟩, a1_right⟩


example
  (V : ValuationAsTotalFunction)
  (P Q : Formula_)
  (FS : List Formula_)
  (h1 : P ∈ FS)
  (h2 : Q ∈ FS) :
  eval V (list_disj FS) = true ↔
    eval V (list_disj (List.filter (fun (R : Formula_) => R = P ∨ R = Q ∨ (¬ (eval V R = true → eval V P = true) ∧ ¬ (eval V R = true → eval V Q = true))) FS)) = true :=
  by
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_filter]
  simp only [decide_eq_true_iff]
  constructor
  · intro a1
    obtain ⟨F, a1_left, a1_right⟩ := a1
    by_cases c1 : eval V F = true → eval V P = true
    case pos =>
      apply Exists.intro P
      constructor
      · constructor
        · exact h1
        · left
          rfl
      · apply c1
        exact a1_right
    case neg =>
      by_cases c2 : eval V F = true → eval V Q = true
      case pos =>
        apply Exists.intro Q
        constructor
        · constructor
          · exact h2
          · right
            left
            rfl
        · apply c2
          exact a1_right
      case neg =>
        apply Exists.intro F
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
  (V : ValuationAsTotalFunction)
  (PS QS : List Formula_)
  (h1 : PS ⊆ QS) :
  eval V (list_of_lists_to_disjunction_of_conjunctions [PS, QS]) = true ↔
    eval V (list_of_lists_to_disjunction_of_conjunctions [PS]) = true :=
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
      apply eval_list_conj_subset V PS QS
      · exact h1
      · exact a1
  · intro a1
    left
    exact a1


example
  (V : ValuationAsTotalFunction)
  (PS QS RS : List Formula_)
  (h1 : PS ⊆ QS)
  (h2 : QS ⊆ RS) :
  eval V (list_of_lists_to_disjunction_of_conjunctions [PS, QS, RS]) = true ↔
    eval V (list_of_lists_to_disjunction_of_conjunctions [PS]) = true :=
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
        apply eval_list_conj_subset V PS QS
        · exact h1
        · exact a1
      case inr a1 =>
        apply eval_list_conj_subset V PS RS
        · trans QS
          · exact h1
          · exact h2
        · exact a1
  · intro a1
    left
    exact a1


example
  (V : ValuationAsTotalFunction)
  (PS QS RS : List Formula_)
  (h1 : PS ⊆ RS) :
  eval V (list_of_lists_to_disjunction_of_conjunctions [PS, QS, RS]) = true ↔
    eval V (list_of_lists_to_disjunction_of_conjunctions [PS, QS]) = true :=
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
        apply eval_list_conj_subset V PS RS
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
  (V : ValuationAsTotalFunction)
  (P Q : Formula_)
  (h1 : eval V Q = true → eval V P = true) :
  eval V (list_disj [P, Q]) = true ↔
    eval V (list_disj [P]) = true :=
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
  (V : ValuationAsTotalFunction)
  (FS : List Formula_) :
  eval V (list_disj FS) = true ↔
    eval V (list_disj (List.dedup FS)) = true :=
  by
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_dedup]


#eval let PSS := [[]]; (List.filter (fun (RS : List Formula_) => ¬ (∃ (PS : List Formula_), PS ∈ PSS ∧ List.SSubset PS RS)) PSS).toString

#eval let PSS := [[atom_ "P"]]; (List.filter (fun (RS : List Formula_) => ¬ (∃ (PS : List Formula_), PS ∈ PSS ∧ List.SSubset PS RS)) PSS).toString

#eval let PSS := [[atom_ "P"], []]; (List.filter (fun (RS : List Formula_) => ¬ (∃ (PS : List Formula_), PS ∈ PSS ∧ List.SSubset PS RS)) PSS).toString

#eval let PSS := [[atom_ "P"], [atom_ "P"]]; (List.filter (fun (RS : List Formula_) => ¬ (∃ (PS : List Formula_), PS ∈ PSS ∧ List.SSubset PS RS)) PSS).toString

#eval let PSS := [[atom_ "P"], [atom_ "P", atom_ "Q"]]; (List.filter (fun (RS : List Formula_) => ¬ (∃ (PS : List Formula_), PS ∈ PSS ∧ List.SSubset PS RS)) PSS).toString


-------------------------------------------------------------------------------


lemma eval_pure_dnf_simp_2_left
  (V : ValuationAsTotalFunction)
  (FSS : List (List Formula_))
  (h1 : eval V (list_of_lists_to_disjunction_of_conjunctions FSS) = true) :
  eval V (list_of_lists_to_disjunction_of_conjunctions (pure_dnf_simp_2 FSS)) = true :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions at h1
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true] at h1
  obtain ⟨F, h1_left, h1_right⟩ := h1
  simp only [List.mem_map] at h1_left
  obtain ⟨RS, h1_left_left, h1_left_right⟩ := h1_left
  rewrite [← h1_left_right] at h1_right

  unfold pure_dnf_simp_2
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
      · intro QS a1
        intro contra
        unfold List.SSubset at contra
        obtain ⟨contra_left, contra_right⟩ := contra
        apply contra_right
        apply s1_right_right
        constructor
        · exact a1
        · exact contra_left
    · rfl
  · exact eval_list_conj_subset V PS RS s1_right_left h1_right


lemma eval_dnf_list_of_list_to_formula_subset
  (V : ValuationAsTotalFunction)
  (PSS QSS : List (List Formula_))
  (h1 : PSS ⊆ QSS)
  (h2 : eval V (list_of_lists_to_disjunction_of_conjunctions PSS) = true) :
  eval V (list_of_lists_to_disjunction_of_conjunctions QSS) = true :=
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


lemma eval_pure_dnf_simp_2_right
  (V : ValuationAsTotalFunction)
  (FSS : List (List Formula_))
  (h1 : eval V (list_of_lists_to_disjunction_of_conjunctions (pure_dnf_simp_2 FSS)) = true) :
  eval V (list_of_lists_to_disjunction_of_conjunctions FSS) = true :=
  by
  apply eval_dnf_list_of_list_to_formula_subset V (pure_dnf_simp_2 FSS)
  · unfold pure_dnf_simp_2
    simp only [List.filter_subset']
  · exact h1


lemma eval_pure_dnf_simp_2
  (V : ValuationAsTotalFunction)
  (FSS : List (List Formula_)) :
  eval V (list_of_lists_to_disjunction_of_conjunctions FSS) = true ↔
    eval V (list_of_lists_to_disjunction_of_conjunctions (pure_dnf_simp_2 FSS)) = true :=
  by
  constructor
  · apply eval_pure_dnf_simp_2_left
  · apply eval_pure_dnf_simp_2_right


lemma pure_dnf_simp_2_is_dnf_ind_v1
  (FSS : List (List Formula_))
  (h1 : is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions FSS)) :
  is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions (pure_dnf_simp_2 FSS)) :=
  by
  unfold pure_dnf_simp_2
  apply is_dnf_ind_v1_list_of_lists_to_disjunction_of_conjunctions_filter
  exact h1


-------------------------------------------------------------------------------


def simp_dnf
  (F : Formula_) :
  List (List Formula_) :=
  if F = false_
  then []
  else
    if F = true_
    then [[]]
    else
      let djs : List (List Formula_) := to_dnf_v3_aux_simp_1 (to_nnf_v1 F)
      (pure_dnf_simp_2 djs)


example
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (list_of_lists_to_disjunction_of_conjunctions (simp_dnf F)) = true :=
  by
  unfold simp_dnf
  split_ifs
  case pos c1 =>
    rewrite [c1]
    unfold list_of_lists_to_disjunction_of_conjunctions
    simp only [List.map_nil]
    unfold list_disj
    rfl
  case pos c1 c2 =>
    rewrite [c2]
    unfold list_of_lists_to_disjunction_of_conjunctions
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    rfl
  case neg c1 c2 =>
    simp only
    simp only [← eval_pure_dnf_simp_2]
    simp only [← eval_eq_eval_to_dnf_v3_simp_1_aux]
    simp only [← eval_eq_eval_to_nnf_v1]


example
  (F : Formula_) :
  is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions (simp_dnf F)) :=
  by
  unfold simp_dnf
  split_ifs
  case pos c1 =>
    unfold list_of_lists_to_disjunction_of_conjunctions
    simp only [List.map_nil]
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    exact is_constant_ind.rule_1
  case pos c1 c2 =>
    unfold list_of_lists_to_disjunction_of_conjunctions
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    exact is_constant_ind.rule_2
  case neg c1 c2 =>
    simp only
    apply pure_dnf_simp_2_is_dnf_ind_v1
    apply is_dnf_ind_v1_to_dnf_v3_simp_1_aux
    apply to_nnf_v1_is_nnf_rec_v1
