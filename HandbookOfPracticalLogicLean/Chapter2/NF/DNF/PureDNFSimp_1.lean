import HandbookOfPracticalLogicLean.Chapter2.NF.Negate
import HandbookOfPracticalLogicLean.Chapter2.NF.NF
import HandbookOfPracticalLogicLean.Chapter2.NF.DNF.PureDNF


set_option autoImplicit false


open Formula_


/--
  `are_complementary P Q` := True if and only if the formulas `P` and `Q` are literals and `P` is the negation of `Q`.
-/
def are_complementary
  (P Q : Formula_) :
  Prop :=
  P.is_literal_rec ∧ Q.is_literal_rec ∧ negate_literal Q = P

instance
  (P Q : Formula_) :
  Decidable (are_complementary P Q) :=
  by
  unfold are_complementary
  infer_instance


/--
  `has_complementary l` := True if and only if the list of formulas `l` contains a pair of complementary formulas.
-/
def has_complementary
  (l : List Formula_) :
  Prop :=
  ∃ (P : Formula_), P ∈ l ∧ ∃ (Q : Formula_), Q ∈ l ∧ are_complementary P Q

instance
  (l : List Formula_) :
  Decidable (has_complementary l) :=
  by
  unfold has_complementary
  infer_instance


#eval has_complementary []

#eval has_complementary [atom_ "P"]
#eval has_complementary [not_ (atom_ "P")]

#eval has_complementary [atom_ "P", not_ (atom_ "P")]
#eval has_complementary [not_ (atom_ "P"), atom_ "P"]

#eval has_complementary [atom_ "P", atom_ "Q", not_ (atom_ "P")]
#eval has_complementary [not_ (atom_ "P"), atom_ "Q", atom_ "P"]

#eval has_complementary [atom_ "P", atom_ "Q", not_ (atom_ "Q")]
#eval has_complementary [atom_ "P", not_ (atom_ "Q"), atom_ "Q"]

#eval has_complementary [atom_ "P", not_ (atom_ "P"), atom_ "Q"]
#eval has_complementary [not_ (atom_ "P"), atom_ "P", atom_ "Q"]


/--
  `pure_dnf_simp_1 F` := The removal of every list of formulas with complementary literals from `to_dnf_v3_aux_1 F`.
-/
def pure_dnf_simp_1
  (F : Formula_) :
  List (List Formula_) :=
  List.filter (fun (l : List Formula_) => ¬ (has_complementary l)) (to_dnf_v3_aux_1 F)


#eval (to_dnf_v3_aux_1 (Formula_| ((P \/ (Q /\ R)) /\ (~P \/ ~R)))).toString
#eval (pure_dnf_simp_1 (Formula_| ((P \/ (Q /\ R)) /\ (~P \/ ~R)))).toString


lemma not_has_complementary_singleton
  (F : Formula_) :
  ¬ has_complementary [F] :=
  by
  unfold has_complementary
  unfold are_complementary
  intro contra
  obtain ⟨P, P_mem, Q, Q_mem, P_lit, Q_lit, eq⟩ := contra
  simp only [List.mem_singleton] at P_mem
  simp only [List.mem_singleton] at Q_mem
  rewrite [P_mem] at eq
  rewrite [Q_mem] at eq
  apply negate_literal_not_eq_self F
  · rewrite [← P_mem]
    exact P_lit
  · exact eq


lemma filter_not_has_complementary_singleton
  (F : Formula_) :
  List.filter (fun (l : List Formula_) => ¬ has_complementary l) [[F]] = [[F]] :=
  by
  simp only [List.filter_eq_self, List.mem_singleton]
  intro l a1
  rewrite [a1]
  apply decide_eq_true
  apply not_has_complementary_singleton


lemma not_has_complementary_union
  (l1 l2 : List Formula_)
  (h1 : ¬ has_complementary (l1 ∪ l2)) :
  ¬ has_complementary l1 ∧ ¬ has_complementary l2 :=
  by
  unfold has_complementary at h1
  unfold are_complementary at h1
  simp only [List.mem_union_iff] at h1

  unfold has_complementary
  unfold are_complementary
  constructor
  · intro contra
    obtain ⟨P, P_mem, Q, Q_mem, P_lit, Q_lit, eq⟩ := contra
    apply h1
    apply Exists.intro P
    constructor
    · left
      exact P_mem
    · apply Exists.intro Q
      constructor
      · left
        exact Q_mem
      · exact ⟨P_lit, ⟨Q_lit, eq⟩⟩
  · intro contra
    obtain ⟨P, P_mem, Q, Q_mem, P_lit, Q_lit, eq⟩ := contra
    apply h1
    apply Exists.intro P
    constructor
    · right
      exact P_mem
    · apply Exists.intro Q
      constructor
      · right
        exact Q_mem
      · exact ⟨P_lit, ⟨Q_lit, eq⟩⟩


lemma has_complementary_imp_eval_list_conj_false
  (V : ValuationAsTotalFunction)
  (l : List Formula_)
  (h1 : has_complementary l) :
  eval V (list_conj l) = false :=
  by
  unfold has_complementary at h1
  unfold are_complementary at h1
  obtain ⟨P, P_mem, Q, Q_mem, P_lit, Q_lit, eq⟩ := h1

  simp only [← Bool.eq_false_eq_not_eq_true]
  intro contra
  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true] at contra

  obtain s1 := eval_negate_literal_eq_not_eval_literal V Q Q_lit
  rewrite [eq] at s1
  rewrite [contra P P_mem] at s1
  rewrite [contra Q Q_mem] at s1
  simp only [b_not] at s1
  contradiction


lemma eval_to_dnf_v3_aux_2_filter_not_has_complementary
  (V : ValuationAsTotalFunction)
  (ll : List (List Formula_)) :
  eval V (to_dnf_v3_aux_2 (List.filter (fun (l : List Formula_) => ¬ (has_complementary l)) ll)) = true ↔
    eval V (to_dnf_v3_aux_2 ll) = true :=
  by
  unfold to_dnf_v3_aux_2
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · intro a1
    obtain ⟨F, ⟨l, ⟨s3, s4⟩, s2⟩, s1⟩ := a1
    exact ⟨F, ⟨l, s3, s2⟩, s1⟩
  · intro a1
    obtain ⟨F, ⟨l, s3, s2⟩, s1⟩ := a1
    rewrite [← s2] at s1

    apply Exists.intro (list_conj l)
    constructor
    · apply Exists.intro l
      constructor
      · constructor
        · exact s3
        · simp only [decide_eq_true_iff]
          intro contra
          simp only [has_complementary_imp_eval_list_conj_false V l contra] at s1
          contradiction
      · rfl
    · exact s1


lemma eval_pure_dnf_simp_1
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V (to_dnf_v3_aux_2 (pure_dnf_simp_1 F)) = true ↔ eval V F = true :=
  by
  unfold pure_dnf_simp_1
  simp only [eval_eq_eval_to_dnf_v3 V F]
  apply eval_to_dnf_v3_aux_2_filter_not_has_complementary


-------------------------------------------------------------------------------


example
  (xs ys : List Formula_)
  (h1 : is_dnf_ind_v1 (to_dnf_v3_aux_2 [xs, ys])) :
  is_dnf_ind_v1 (to_dnf_v3_aux_2 [xs]) :=
  by
  unfold to_dnf_v3_aux_2 at h1
  simp only [List.map_cons, List.map_nil] at h1
  unfold list_disj at h1
  cases h1
  case rule_1 ih =>
    contradiction
  case rule_2 ih_1 ih_2 =>
    unfold to_dnf_v3_aux_2
    simp only [List.map_cons, List.map_nil]
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    exact ih_1


example
  (xs ys : List Formula_)
  (h1 : is_dnf_ind_v1 (to_dnf_v3_aux_2 [xs, ys])) :
  is_dnf_ind_v1 (to_dnf_v3_aux_2 [ys]) :=
  by
  unfold to_dnf_v3_aux_2 at h1
  simp only [List.map_cons, List.map_nil] at h1
  unfold list_disj at h1
  cases h1
  case rule_1 ih =>
    contradiction
  case rule_2 ih_1 ih_2 =>
    unfold to_dnf_v3_aux_2
    simp only [List.map_cons, List.map_nil]
    exact ih_2


lemma is_dnf_ind_v1_dnf_list_of_list_to_formula_cons_left
  (xs : List Formula_)
  (xss : List (List Formula_))
  (h1 : is_dnf_ind_v1 (to_dnf_v3_aux_2 (xs :: xss))) :
  is_dnf_ind_v1 (to_dnf_v3_aux_2 xss) :=
  by
  unfold to_dnf_v3_aux_2 at h1
  simp only [List.map_cons] at h1
  unfold to_dnf_v3_aux_2
  apply list_disj_cons_is_dnf_ind_v1_imp_list_disj_tail_is_dnf_ind_v1 (list_conj xs)
  exact h1


lemma is_dnf_ind_v1_dnf_list_of_list_to_formula_cons_right
  (xs : List Formula_)
  (xss : List (List Formula_))
  (h1 : is_conj_ind_v1 (list_conj xs))
  (h2 : is_dnf_ind_v1 (to_dnf_v3_aux_2 xss)) :
  is_dnf_ind_v1 (to_dnf_v3_aux_2 (xs :: xss)) :=
  by
  unfold to_dnf_v3_aux_2 at h2

  unfold to_dnf_v3_aux_2
  apply hd_is_conj_ind_v1_and_list_disj_tail_is_dnf_ind_v1_imp_list_disj_cons_is_dnf_ind_v1
  · exact h1
  · exact h2


lemma is_dnf_ind_v1_dnf_list_of_list_to_formula_filter
  (xss : List (List Formula_))
  (pred : List Formula_ → Bool)
  (h1 : is_dnf_ind_v1 (to_dnf_v3_aux_2 xss)) :
  is_dnf_ind_v1 (to_dnf_v3_aux_2 (List.filter pred xss)) :=
  by
  unfold to_dnf_v3_aux_2 at h1

  unfold to_dnf_v3_aux_2
  induction xss
  case nil =>
    simp only [List.filter_nil]
    exact h1
  case cons hd tl ih =>
    simp only [List.filter_cons]
    split_ifs
    case pos c1 =>
      cases tl
      case nil =>
        simp only [List.map_cons, List.map_nil] at h1
        simp only [List.filter_nil, List.map_cons, List.map_nil]
        exact h1
      case cons tl_hd tl_tl =>
        simp only [List.map_cons] at h1
        unfold list_disj at h1
        cases h1
        case rule_1 ih_1 =>
          contradiction
        case rule_2 ih_1 ih_2 =>
          simp only [List.map_cons]
          apply is_dnf_ind_v1_dnf_list_of_list_to_formula_cons_right
          · exact ih_1
          · apply ih
            simp only [List.map_cons]
            exact ih_2
    case neg c1 =>
      apply ih
      exact is_dnf_ind_v1_dnf_list_of_list_to_formula_cons_left hd tl h1


lemma pure_dnf_simp_1_is_dnf_ind_v1
  (F : Formula_)
  (h1 : is_nnf_rec_v1 F) :
  is_dnf_ind_v1 (to_dnf_v3_aux_2 (pure_dnf_simp_1 F)) :=
  by
  unfold pure_dnf_simp_1
  apply is_dnf_ind_v1_dnf_list_of_list_to_formula_filter
  exact is_nnf_rec_v1_imp_to_dnf_v3_is_dnf_ind_v1 F h1


#lint
