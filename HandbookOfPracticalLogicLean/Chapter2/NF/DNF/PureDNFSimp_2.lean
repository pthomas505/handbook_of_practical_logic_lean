import HandbookOfPracticalLogicLean.Chapter2.NF.DNF.PureDNFSimp_1
import HandbookOfPracticalLogicLean.Chapter2.NF.NNF.NNF_1


set_option autoImplicit false


open Formula_


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
  (l1 l2 : List Formula_)
  (h1 : l1 ⊆ l2) :
  eval V (or_ (list_conj l1) (list_conj l2)) = true ↔
    eval V (list_conj l1) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_or]
  constructor
  · intro a1
    cases a1
    case inl a1 =>
      exact a1
    case inr a1 =>
      exact eval_list_conj_subset V l1 l2 h1 a1
  · intro a1
    left
    exact a1


example
  (V : ValuationAsTotalFunction)
  (P : Formula_)
  (xs : List Formula_)
  (h1 : P ∈ xs) :
  eval V (list_disj xs) = true ↔
    eval V (list_disj (List.filter (fun (Q : Formula_) => Q = P ∨ ¬ (eval V Q = true → eval V P = true)) xs)) = true :=
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


def List.SSubset
  {α : Type}
  (l₁ l₂ : List α) :
  Prop :=
  l₁ ⊆ l₂ ∧ ¬ l₂ ⊆ l₁

instance
  {α : Type}
  [DecidableEq α]
  (l₁ l₂ : List α) :
  Decidable (List.SSubset l₁ l₂) :=
  by
  unfold List.SSubset
  infer_instance


example
  (V : ValuationAsTotalFunction)
  (xs : List Formula_)
  (zss : List (List Formula_))
  (h1 : xs ∈ zss) :
  eval V (to_dnf_v3_aux_2 zss) = true ↔
    eval V (to_dnf_v3_aux_2 (List.filter (fun (zs : List Formula_) => ¬ List.SSubset xs zs) zss)) = true :=
  by
  unfold to_dnf_v3_aux_2
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_map, List.mem_filter]
  simp only [decide_eq_true_iff]
  constructor
  · intro a1
    obtain ⟨F, ⟨zs, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
    by_cases c1 : List.SSubset xs zs
    case pos =>
      apply Exists.intro (list_conj xs)
      constructor
      · apply Exists.intro xs
        constructor
        · constructor
          · exact h1
          · unfold List.SSubset
            intro ⟨contra_left, contra_right⟩
            contradiction
        · rfl
      · unfold List.SSubset at c1
        obtain ⟨c1_left, c1_right⟩ := c1
        rewrite [← a1_left_right] at a1_right
        apply eval_list_conj_subset V xs zs c1_left a1_right
    case neg =>
      exact ⟨F, ⟨zs, ⟨a1_left_left, c1⟩, a1_left_right⟩, a1_right⟩
  · intro a1
    obtain ⟨F, ⟨zs, ⟨a1_left_left_left, a1_left_left_right⟩, a1_left_right⟩, a1_right⟩ := a1
    exact ⟨F, ⟨zs, a1_left_left_left, a1_left_right⟩, a1_right⟩


example
  (V : ValuationAsTotalFunction)
  (P Q : Formula_)
  (xs : List Formula_)
  (h1 : P ∈ xs)
  (h2 : Q ∈ xs) :
  eval V (list_disj xs) = true ↔
    eval V (list_disj (List.filter (fun (R : Formula_) => R = P ∨ R = Q ∨ (¬ (eval V R = true → eval V P = true) ∧ ¬ (eval V R = true → eval V Q = true))) xs)) = true :=
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
    obtain ⟨F, ⟨a1_left_left, a1_left_right⟩ , a1_right⟩ := a1
    exact ⟨F, a1_left_left, a1_right⟩


example
  (V : ValuationAsTotalFunction)
  (xs ys : List Formula_)
  (h1 : xs ⊆ ys) :
  eval V (to_dnf_v3_aux_2 [xs, ys]) = true ↔
  eval V (to_dnf_v3_aux_2 [xs]) = true :=
  by
  unfold to_dnf_v3_aux_2
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
      exact eval_list_conj_subset V xs ys h1 a1
  · intro a1
    left
    exact a1


example
  (V : ValuationAsTotalFunction)
  (xs ys zs : List Formula_)
  (h1 : xs ⊆ ys)
  (h2 : ys ⊆ zs) :
  eval V (to_dnf_v3_aux_2 [xs, ys, zs]) = true ↔
  eval V (to_dnf_v3_aux_2 [xs]) = true :=
  by
  unfold to_dnf_v3_aux_2
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
        exact eval_list_conj_subset V xs ys h1 a1
      case inr a1 =>
        apply eval_list_conj_subset V xs zs
        · trans ys
          · exact h1
          · exact h2
        · exact a1
  · intro a1
    left
    exact a1


example
  (V : ValuationAsTotalFunction)
  (xs ys zs : List Formula_)
  (h1 : xs ⊆ zs) :
  eval V (to_dnf_v3_aux_2 [xs, ys, zs]) = true ↔
  eval V (to_dnf_v3_aux_2 [xs, ys]) = true :=
  by
  unfold to_dnf_v3_aux_2
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
        exact eval_list_conj_subset V xs zs h1 a1
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
  (xs : List Formula_) :
  (eval V (list_disj xs) = true) ↔ eval V (list_disj (List.dedup xs)) = true :=
  by
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_dedup]


#eval let xss := [[]]; (List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss).toString

#eval let xss := [[atom_ "P"]]; (List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss).toString

#eval let xss := [[atom_ "P"], []]; (List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss).toString

#eval let xss := [[atom_ "P"], [atom_ "P"]]; (List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss).toString

#eval let xss := [[atom_ "P"], [atom_ "P", atom_ "Q"]]; (List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss).toString


def pure_dnf_simp_2
  (xss : List (List Formula_)) :
  List (List Formula_) :=
  List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss


lemma eval_pure_dnf_simp_2_left
  (V : ValuationAsTotalFunction)
  (xss : List (List Formula_))
  (h1 : eval V (to_dnf_v3_aux_2 xss) = true) :
  eval V (to_dnf_v3_aux_2 (pure_dnf_simp_2 xss)) = true :=
  by
  unfold to_dnf_v3_aux_2 at h1
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true] at h1
  obtain ⟨F, h1_left, h1_right⟩ := h1
  simp only [List.mem_map] at h1_left
  obtain ⟨zs, h1_left_left, h1_left_right⟩ := h1_left
  rewrite [← h1_left_right] at h1_right

  unfold pure_dnf_simp_2
  unfold to_dnf_v3_aux_2
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_map, List.mem_filter]
  simp only [decide_eq_true_iff]

  simp only [not_exists]
  simp only [not_and]

  obtain ⟨xs, s1_left, ⟨s1_right_left, s1_right_right⟩⟩ := List.exists_minimal_subset_of_mem xss zs h1_left_left
  apply Exists.intro (list_conj xs)
  constructor
  · apply Exists.intro xs
    constructor
    · constructor
      · exact s1_left
      · intro ys a1
        intro contra
        unfold List.SSubset at contra
        obtain ⟨contra_left, contra_right⟩ := contra
        apply contra_right
        apply s1_right_right
        constructor
        · exact a1
        · exact contra_left
    · rfl
  · exact eval_list_conj_subset V xs zs s1_right_left h1_right


lemma eval_dnf_list_of_list_to_formula_subset
  (V : ValuationAsTotalFunction)
  (xss yss : List (List Formula_))
  (h1 : xss ⊆ yss)
  (h2 : eval V (to_dnf_v3_aux_2 xss) = true) :
  eval V (to_dnf_v3_aux_2 yss) = true :=
  by
  unfold to_dnf_v3_aux_2 at h2
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true] at h2
  simp only [List.mem_map] at h2
  obtain ⟨F, ⟨xs, h2_left_left, h2_left_right⟩, h2_right⟩ := h2

  unfold to_dnf_v3_aux_2
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_map]
  apply Exists.intro F
  constructor
  · apply Exists.intro xs
    constructor
    · exact h1 h2_left_left
    · exact h2_left_right
  · exact h2_right


lemma eval_pure_dnf_simp_2_right
  (V : ValuationAsTotalFunction)
  (xss : List (List Formula_))
  (h1 : eval V (to_dnf_v3_aux_2 (pure_dnf_simp_2 xss)) = true) :
  eval V (to_dnf_v3_aux_2 xss) = true :=
  by
  apply eval_dnf_list_of_list_to_formula_subset V (pure_dnf_simp_2 xss)
  · unfold pure_dnf_simp_2
    simp only [List.filter_subset']
  · exact h1


lemma eval_pure_dnf_simp_2
  (V : ValuationAsTotalFunction)
  (xss : List (List Formula_)) :
  eval V (to_dnf_v3_aux_2 xss) = true ↔
    eval V (to_dnf_v3_aux_2 (pure_dnf_simp_2 xss)) = true :=
  by
  constructor
  · apply eval_pure_dnf_simp_2_left
  · apply eval_pure_dnf_simp_2_right


lemma pure_dnf_simp_2_is_dnf_ind_v1
  (xss : List (List Formula_))
  (h1 : is_dnf_ind_v1 (to_dnf_v3_aux_2 xss)) :
  is_dnf_ind_v1 (to_dnf_v3_aux_2 (pure_dnf_simp_2 xss)) :=
  by
  unfold pure_dnf_simp_2
  apply is_dnf_ind_v1_dnf_list_of_list_to_formula_filter
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
      let djs : List (List Formula_) := to_dnf_v3_aux_1_simp_1 (to_nnf_v1 F)
      (pure_dnf_simp_2 djs)


example
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (to_dnf_v3_aux_2 (simp_dnf F)) = true :=
  by
  unfold simp_dnf
  split_ifs
  case pos c1 =>
    rewrite [c1]
    unfold to_dnf_v3_aux_2
    simp only [List.map_nil]
    unfold list_disj
    rfl
  case pos c1 c2 =>
    rewrite [c2]
    unfold to_dnf_v3_aux_2
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
  is_dnf_ind_v1 (to_dnf_v3_aux_2 (simp_dnf F)) :=
  by
  unfold simp_dnf
  split_ifs
  case pos c1 =>
    unfold to_dnf_v3_aux_2
    simp only [List.map_nil]
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    exact is_constant_ind.rule_1
  case pos c1 c2 =>
    unfold to_dnf_v3_aux_2
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    exact is_constant_ind.rule_2
  case neg c1 c2 =>
    simp only
    apply pure_dnf_simp_2_is_dnf_ind_v1
    apply pure_dnf_simp_1_is_dnf_ind_v1
    apply to_nnf_v1_is_nnf_rec_v1
