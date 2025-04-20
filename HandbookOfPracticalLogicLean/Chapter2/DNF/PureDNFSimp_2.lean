import HandbookOfPracticalLogicLean.Chapter2.DNF.PureDNFSimp_1


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
  (xs ys : List Formula_)
  (h1 : xs ⊆ ys) :
  eval V (or_ (list_conj xs) (list_conj ys)) = true ↔ eval V (list_conj xs) = true :=
  by
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
  (P : Formula_)
  (xs : List Formula_)
  (h1 : P ∈ xs) :
  eval V (list_disj xs) = true ↔
    eval V (list_disj (List.filter (fun (Q : Formula_) => Q = P ∨ ¬ (eval V Q = true → eval V P = true)) xs)) = true :=
  by
  simp only [eval_list_disj_eq_true_iff_eval_exists_eq_true]
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
  eval V (dnf_list_of_list_to_formula zss) = true ↔
    eval V (dnf_list_of_list_to_formula (List.filter (fun (zs : List Formula_) => ¬ List.SSubset xs zs) zss)) = true :=
  by
  unfold dnf_list_of_list_to_formula
  simp only [eval_list_disj_eq_true_iff_eval_exists_eq_true]
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
  simp only [eval_list_disj_eq_true_iff_eval_exists_eq_true]
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
  eval V (dnf_list_of_list_to_formula [xs, ys]) = true ↔
  eval V (dnf_list_of_list_to_formula [xs]) = true :=
  by
  unfold dnf_list_of_list_to_formula
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
  eval V (dnf_list_of_list_to_formula [xs, ys, zs]) = true ↔
  eval V (dnf_list_of_list_to_formula [xs]) = true :=
  by
  unfold dnf_list_of_list_to_formula
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
  eval V (dnf_list_of_list_to_formula [xs, ys, zs]) = true ↔
  eval V (dnf_list_of_list_to_formula [xs, ys]) = true :=
  by
  unfold dnf_list_of_list_to_formula
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
  simp only [eval_list_disj_eq_true_iff_eval_exists_eq_true]
  simp only [List.mem_dedup]


#eval let xss := [[]]; (List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss).toString

#eval let xss := [[atom_ "P"]]; (List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss).toString

#eval let xss := [[atom_ "P"], []]; (List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss).toString

#eval let xss := [[atom_ "P"], [atom_ "P"]]; (List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss).toString

#eval let xss := [[atom_ "P"], [atom_ "P", atom_ "Q"]]; (List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss).toString


example
  {α : Type}
  [DecidableEq α]
  (l : List (List α))
  (h1 : ¬ l = []) :
  ∃ (xs : List α), xs ∈ l ∧ ∀ (ys : List α), (ys ∈ l ∧ xs ⊆ ys) → xs.toFinset = ys.toFinset :=
  by
  induction l
  case nil =>
    contradiction
  case cons hd tl ih =>
    by_cases c1 : tl = []
    case pos =>
      rewrite [c1]
      apply Exists.intro hd
      constructor
      · simp only [List.mem_singleton]
      · intro ys a1
        obtain ⟨a1_left, a1_right⟩ := a1
        simp only [List.mem_singleton] at a1_left
        rewrite [a1_left]
        rfl
    case neg =>
      specialize ih c1
      obtain ⟨xs, ih_left, ih_right⟩ := ih
      by_cases c2 : xs ⊆ hd
      case pos =>
        simp only [List.mem_cons]
        apply Exists.intro hd
        constructor
        · left
          rfl
        · intro ys a1
          obtain ⟨a1_left, a1_right⟩ := a1
          cases a1_left
          case inl a1_left =>
            rewrite [a1_left]
            rfl
          case inr a1_left =>
            have s1 : xs.toFinset = ys.toFinset :=
            by
              apply ih_right
              constructor
              · exact a1_left
              · trans hd
                · exact c2
                · exact a1_right

            simp only [List.subset_def] at c2
            simp only [← List.mem_toFinset] at c2

            simp only [List.subset_def] at a1_right
            simp only [← List.mem_toFinset] at a1_right

            ext a
            constructor
            · apply a1_right
            · rewrite [← s1]
              apply c2
      case neg =>
        simp only [List.mem_cons]
        apply Exists.intro xs
        constructor
        · right
          exact ih_left
        · intro ys a1
          obtain ⟨a1_left, a1_right⟩ := a1
          cases a1_left
          case inl a1_left =>
            rewrite [a1_left] at a1_right
            contradiction
          case inr a1_left =>
            apply ih_right
            exact ⟨a1_left, a1_right⟩


lemma List.Finite.exists_minimal_subset
  {α : Type}
  [DecidableEq α]
  (l : List (List α))
  (h1 : ¬ l = []) :
  ∃ (xs : List α), xs ∈ l ∧ ∀ (ys : List α), (ys ∈ l ∧ ys ⊆ xs) → xs.toFinset = ys.toFinset :=
  by
  induction l
  case nil =>
    contradiction
  case cons hd tl ih =>
    by_cases c1 : tl = []
    case pos =>
      rewrite [c1]
      apply Exists.intro hd
      constructor
      · simp only [mem_singleton]
      · intro ys a1
        obtain ⟨a1_left, a1_right⟩ := a1
        simp only [mem_singleton] at a1_left
        rewrite [a1_left]
        rfl
    case neg =>
      specialize ih c1
      obtain ⟨xs, ih_left, ih_right⟩ := ih

      simp only [mem_cons]
      sorry


-- xs has a subset in xss that is minimal
lemma aux
  {α : Type}
  [DecidableEq α]
  (xss : List (List α))
  (xs : List α)
  (h1 : xs ∈ xss) :
  ∃ (ys : List α), ys ∈ xss ∧ ys ⊆ xs ∧
    ∀ (zs : List α), (zs ∈ xss ∧ zs ⊆ ys) → ys ⊆ zs :=
  by
  have s1 : ({x | x ∈ xss} ∩ {ys | ys ⊆ xs}).Finite :=
  by
    apply Set.Finite.inter_of_left
    exact List.finite_toSet xss

  have s2 : ∃ (ys : List α), ys ∈ {x | x ∈ xss} ∩ {ys | ys ⊆ xs} ∧ ∀ zs ∈ {x | x ∈ xss} ∩ {ys | ys ⊆ xs}, zs.toFinset ≤ ys.toFinset → ys.toFinset = zs.toFinset :=
  by
    apply Set.Finite.exists_minimal_wrt
    · exact s1
    · unfold Set.Nonempty
      apply Exists.intro xs
      apply Set.mem_inter
      · exact h1
      · exact List.Subset.refl xs

  obtain ⟨ys, ⟨s2_left_left, s2_left_right⟩, s2_right⟩ := s2
  simp only [Set.mem_setOf_eq] at s2_left_left
  simp only [Set.mem_setOf_eq] at s2_left_right

  apply Exists.intro ys
  constructor
  · exact s2_left_left
  · constructor
    · exact s2_left_right
    · intro zs a1
      obtain ⟨a1_left, a1_right⟩ := a1

      have s3 : zs ∈ {x | x ∈ xss} ∩ {ys | ys ⊆ xs} :=
      by
        simp only [Set.mem_inter_iff]
        simp only [Set.mem_setOf_eq]
        constructor
        · exact a1_left
        · trans ys
          · exact a1_right
          · exact s2_left_right

      have s4 : zs.toFinset ≤ ys.toFinset :=
      by
        simp only [Finset.le_eq_subset]
        simp only [Finset.subset_iff]
        simp only [List.mem_toFinset]
        intro x a2
        exact a1_right a2

      specialize s2_right zs s3 s4
      simp only [List.subset_def]
      intro xs a2
      simp only [← List.mem_toFinset]
      rewrite [← s2_right]
      simp only [List.mem_toFinset]
      exact a2


def pure_dnf_simp_2
  (xss : List (List Formula_)) :
  List (List Formula_) :=
  List.filter (fun (zs : List Formula_) => ¬ (∃ (xs : List Formula_), xs ∈ xss ∧ List.SSubset xs zs)) xss


lemma eval_pure_dnf_simp_2_left
  (V : ValuationAsTotalFunction)
  (xss : List (List Formula_))
  (h1 : eval V (dnf_list_of_list_to_formula xss) = true) :
  eval V (dnf_list_of_list_to_formula (pure_dnf_simp_2 xss)) = true :=
  by
  unfold dnf_list_of_list_to_formula at h1
  simp only [eval_list_disj_eq_true_iff_eval_exists_eq_true] at h1
  obtain ⟨F, h1_left, h1_right⟩ := h1
  simp only [List.mem_map] at h1_left
  obtain ⟨zs, h1_left_left, h1_left_right⟩ := h1_left
  rewrite [← h1_left_right] at h1_right

  unfold pure_dnf_simp_2
  unfold dnf_list_of_list_to_formula
  simp only [eval_list_disj_eq_true_iff_eval_exists_eq_true]
  simp only [List.mem_map, List.mem_filter]
  simp only [decide_eq_true_iff]

  simp only [not_exists]
  simp only [not_and]

  obtain ⟨xs, s1_left, ⟨s1_right_left, s1_right_right⟩⟩ := aux xss zs h1_left_left
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
  (h2 : eval V (dnf_list_of_list_to_formula xss) = true) :
  eval V (dnf_list_of_list_to_formula yss) = true :=
  by
  unfold dnf_list_of_list_to_formula at h2
  simp only [eval_list_disj_eq_true_iff_eval_exists_eq_true] at h2
  simp only [List.mem_map] at h2
  obtain ⟨F, ⟨xs, h2_left_left, h2_left_right⟩, h2_right⟩ := h2

  unfold dnf_list_of_list_to_formula
  simp only [eval_list_disj_eq_true_iff_eval_exists_eq_true]
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
  (h1 : eval V (dnf_list_of_list_to_formula (pure_dnf_simp_2 xss)) = true) :
  eval V (dnf_list_of_list_to_formula xss) = true :=
  by
  apply eval_dnf_list_of_list_to_formula_subset V (pure_dnf_simp_2 xss)
  · unfold pure_dnf_simp_2
    simp only [List.filter_subset']
  · exact h1


lemma eval_pure_dnf_simp_2
  (V : ValuationAsTotalFunction)
  (xss : List (List Formula_)) :
  eval V (dnf_list_of_list_to_formula xss) = true ↔
    eval V (dnf_list_of_list_to_formula (pure_dnf_simp_2 xss)) = true :=
  by
  constructor
  · apply eval_pure_dnf_simp_2_left
  · apply eval_pure_dnf_simp_2_right


example
  (xss : List (List Formula_))
  (h1 : is_dnf_ind_v1 (dnf_list_of_list_to_formula xss)) :
  is_dnf_ind_v1 (dnf_list_of_list_to_formula (pure_dnf_simp_2 xss)) :=
  by
  unfold pure_dnf_simp_2
  apply aux_7
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
      let djs : List (List Formula_) := pure_dnf_simp_1 (to_nnf_v1 F)
      (pure_dnf_simp_2 djs)


example
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (dnf_list_of_list_to_formula (simp_dnf F)) = true :=
  by
  unfold simp_dnf
  split_ifs
  case pos c1 =>
    rewrite [c1]
    unfold dnf_list_of_list_to_formula
    simp only [List.map_nil]
    unfold list_disj
    rfl
  case pos c1 c2 =>
    rewrite [c2]
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    rfl
  case neg c1 c2 =>
    simp only
    simp only [← eval_pure_dnf_simp_2]
    simp only [eval_pure_dnf_simp_1]
    simp only [← eval_to_nnf_v1]


example
  (F : Formula_) :
  is_dnf_ind_v1 (dnf_list_of_list_to_formula (simp_dnf F)) :=
  by
  unfold simp_dnf
  split_ifs
  case pos c1 =>
    unfold dnf_list_of_list_to_formula
    simp only [List.map_nil]
    unfold list_disj
    apply is_dnf_ind_v1.rule_2
    apply is_conj_ind_v1.rule_3
    exact is_constant_ind_v1.rule_1
  case pos c1 c2 =>
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    apply is_dnf_ind_v1.rule_2
    apply is_conj_ind_v1.rule_3
    exact is_constant_ind_v1.rule_2
  case neg c1 c2 =>
    simp only
    sorry
