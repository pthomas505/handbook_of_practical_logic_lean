import HandbookOfPracticalLogicLean.Chapter2.NF.Negate
import HandbookOfPracticalLogicLean.Chapter2.NF.NF
import HandbookOfPracticalLogicLean.Chapter2.NF.DNF.PureDNF


set_option autoImplicit false


open Formula_


/--
  `has_complementary l` := True if and only if there exists a pair of literal formulas `P` and `Q` in the list of formulas `l` such that `P` is the negation of `Q`.
-/
def has_complementary
  (l : List Formula_) :
  Prop :=
  ∃ (P : Formula_), P ∈ l ∧ P.is_literal_rec ∧ ∃ (Q : Formula_), Q ∈ l ∧ Q.is_literal_rec ∧ negate_literal Q = P

instance
  (l : List Formula_) :
  Decidable (has_complementary l) :=
  by
  induction l
  all_goals
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


#eval (List.filter (fun (l : List Formula_) => ¬ (has_complementary l)) (to_dnf_v3_aux_1 (Formula_| ((P \/ (Q /\ R)) /\ (~P \/ ~R))))).toString


lemma not_has_complementary_singleton
  (F : Formula_) :
  ¬ has_complementary [F] :=
  by
  unfold has_complementary
  intro contra
  obtain ⟨P, mem_P, lit_P, Q, mem_Q, lit_Q, eq⟩ := contra
  simp only [List.mem_singleton] at mem_P
  simp only [List.mem_singleton] at mem_Q
  rewrite [mem_Q] at eq
  rewrite [mem_P] at eq
  apply negate_literal_not_eq_self F
  · rewrite [← mem_P]
    exact lit_P
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
  (xs ys : List Formula_)
  (h1 : ¬ has_complementary (xs ∪ ys)) :
  ¬ has_complementary xs ∧ ¬ has_complementary ys :=
  by
  unfold has_complementary at h1
  simp only [List.mem_union_iff] at h1

  unfold has_complementary
  constructor
  all_goals
    intro contra
    obtain ⟨P, P_mem, P_lit, Q, Q_mem, Q_lit, eq⟩ := contra
    apply h1
    apply Exists.intro P
    constructor
    · first | left; exact P_mem | right; exact P_mem
    · constructor
      · exact P_lit
      · apply Exists.intro Q
        constructor
        · first | left; exact Q_mem | right; exact Q_mem
        · exact ⟨Q_lit, eq⟩


lemma has_complementary_imp_eval_list_conj_false
  (V : ValuationAsTotalFunction)
  (l : List Formula_)
  (h1 : has_complementary l) :
  eval V (list_conj l) = false :=
  by
  induction l
  case nil =>
    unfold has_complementary at h1
    contradiction
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold list_conj at ih

      unfold has_complementary at h1
      obtain ⟨P, P_mem, P_lit, ⟨Q, Q_mem, Q_lit, eq⟩⟩ := h1

      simp only [List.mem_singleton] at P_mem
      simp only [List.mem_singleton] at Q_mem

      rewrite [P_mem] at eq
      rewrite [Q_mem] at eq

      rewrite [P_mem] at P_lit

      obtain s1 := negate_literal_not_eq_self hd P_lit
      contradiction
    case cons tl_hd tl_tl =>
      unfold has_complementary at ih

      unfold has_complementary at h1
      obtain ⟨P, P_mem, P_lit, ⟨Q, Q_mem, Q_lit, eq⟩⟩ := h1

      simp only [List.mem_cons] at P_mem
      simp only [List.mem_cons] at Q_mem

      unfold list_conj
      unfold eval
      apply Bool.bool_eq_false
      simp only [bool_iff_prop_and]
      simp only [not_and]

      cases P_mem
      case inl P_mem =>
        cases Q_mem
        case inl Q_mem =>
          rewrite [P_mem] at eq
          rewrite [Q_mem] at eq

          rewrite [P_mem] at P_lit

          obtain s1 := negate_literal_not_eq_self hd P_lit
          contradiction
        case inr Q_mem =>
          simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
          intro a1

          rewrite [← P_mem] at a1
          rewrite [← eq] at a1
          rewrite [eval_negate_literal_eq_not_eval_literal V Q Q_lit] at a1
          simp only [bool_iff_prop_not] at a1

          intro contra
          apply a1
          apply contra
          simp only [List.mem_cons]
          exact Q_mem
      case inr P_mem =>
        cases Q_mem
        case inl Q_mem =>
          simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
          intro a1

          rewrite [← Q_mem] at a1
          have s1 : ¬ eval V P = true :=
          by
            rewrite [← eq]
            rewrite [eval_negate_literal_eq_not_eval_literal V Q Q_lit]
            simp only [bool_iff_prop_not]
            intro contra
            contradiction

          intro contra
          apply s1
          apply contra
          simp only [List.mem_cons]
          exact P_mem
        case inr Q_mem =>
          intro a1
          simp only [Bool.bool_iff_false]
          apply ih
          simp only [List.mem_cons]
          exact ⟨P, P_mem, P_lit, Q, Q_mem, Q_lit, eq⟩


lemma eval_dnf_list_of_list_to_formula_filter_not_has_complementary
  (V : ValuationAsTotalFunction)
  (ll : List (List Formula_)) :
  eval V (to_dnf_v3_aux_2 (List.filter (fun (l : List Formula_) => ¬ (has_complementary l)) ll)) = true ↔
    eval V (to_dnf_v3_aux_2 ll) :=
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

    have s4 : ¬ has_complementary l :=
    by
      rewrite [← s2] at s1
      intro contra
      rewrite [has_complementary_imp_eval_list_conj_false V l contra] at s1
      contradiction

    simp only [decide_eq_true_iff]
    exact ⟨F, ⟨l, ⟨s3, s4⟩, s2⟩, s1⟩


/--
  `pure_dnf_simp_1 F` := The removal of every list of formulas with complementary literals from `to_dnf_v3_aux_1 F`.
-/
def pure_dnf_simp_1
  (F : Formula_) :
  List (List Formula_) :=
  List.filter (fun (l : List Formula_) => ¬ (has_complementary l)) (to_dnf_v3_aux_1 F)


lemma eval_pure_dnf_simp_1
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V (to_dnf_v3_aux_2 (pure_dnf_simp_1 F)) = true ↔ eval V F = true :=
  by
  unfold pure_dnf_simp_1
  simp only [eval_eq_eval_to_dnf_v3 V F]
  apply eval_dnf_list_of_list_to_formula_filter_not_has_complementary


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
