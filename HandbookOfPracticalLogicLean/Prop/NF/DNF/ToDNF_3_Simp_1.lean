import HandbookOfPracticalLogicLean.Prop.NF.Negate
import HandbookOfPracticalLogicLean.Prop.NF.NF
import HandbookOfPracticalLogicLean.Prop.NF.DNF.ToDNF_3


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
  `has_complementary FS` := True if and only if the list of formulas `FS` contains complementary formulas.
-/
def has_complementary
  (FS : List Formula_) :
  Prop :=
  ∃ (P : Formula_), P ∈ FS ∧ ∃ (Q : Formula_), Q ∈ FS ∧ are_complementary P Q

instance
  (FS : List Formula_) :
  Decidable (has_complementary FS) :=
  by
  unfold has_complementary
  infer_instance


#eval has_complementary []

#eval has_complementary [var_ "P"]
#eval has_complementary [not_ (var_ "P")]

#eval has_complementary [var_ "P", not_ (var_ "P")]
#eval has_complementary [not_ (var_ "P"), var_ "P"]

#eval has_complementary [var_ "P", var_ "Q", not_ (var_ "P")]
#eval has_complementary [not_ (var_ "P"), var_ "Q", var_ "P"]

#eval has_complementary [var_ "P", var_ "Q", not_ (var_ "Q")]
#eval has_complementary [var_ "P", not_ (var_ "Q"), var_ "Q"]

#eval has_complementary [var_ "P", not_ (var_ "P"), var_ "Q"]
#eval has_complementary [not_ (var_ "P"), var_ "P", var_ "Q"]


/--
  `filter_not_has_complementary FSS` := The result of removing every list of formulas that contains complementary formulas from the list of lists of formulas `FSS`.
-/
def filter_not_has_complementary
  (FSS : List (List Formula_)) :
  List (List Formula_) :=
  List.filter (fun (FS : List Formula_) => ¬ (has_complementary FS)) FSS


/--
  `to_dnf_v3_aux_simp_1 F` := The result of removing every list of formulas that contains complementary formulas from the list of lists of formulas given by `to_dnf_v3_aux F`.
-/
def to_dnf_v3_aux_simp_1
  (F : Formula_) :
  List (List Formula_) :=
  filter_not_has_complementary (to_dnf_v3_aux F)


#eval (to_dnf_v3_aux (Formula_| ((P \/ (Q /\ R)) /\ (~P \/ ~R)))).toString
#eval (to_dnf_v3_aux_simp_1 (Formula_| ((P \/ (Q /\ R)) /\ (~P \/ ~R)))).toString


/--
  `to_dnf_v3_simp_1 F` := Translates the formula `F` to a logically equivalent formula. If `F` is in negation normal form then `to_dnf_v3_simp_1 F` is in disjunctive normal form and none of the conjunctive clauses in `to_dnf_v3_simp_1 F` contain complementary formulas.
-/
def to_dnf_v3_simp_1
  (F : Formula_) :
  Formula_ :=
  list_of_lists_to_disjunction_of_conjunctions (to_dnf_v3_aux_simp_1 F)


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
  filter_not_has_complementary [[F]] = [[F]] :=
  by
  unfold filter_not_has_complementary
  simp only [List.filter_eq_self, List.mem_singleton]
  intro FS a1
  rewrite [a1]
  apply decide_eq_true
  apply not_has_complementary_singleton


lemma not_has_complementary_union
  (PS QS : List Formula_)
  (h1 : ¬ has_complementary (PS ∪ QS)) :
  ¬ has_complementary PS ∧ ¬ has_complementary QS :=
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
  (FS : List Formula_)
  (h1 : has_complementary FS) :
  eval V (list_conj FS) = false :=
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


lemma eval_list_of_lists_to_disjunction_of_conjunctions_eq_eval_list_of_lists_to_disjunction_of_conjunctions_filter_not_has_complementary
  (V : ValuationAsTotalFunction)
  (FSS : List (List Formula_)) :
  eval V (list_of_lists_to_disjunction_of_conjunctions FSS) = true ↔
  eval V (list_of_lists_to_disjunction_of_conjunctions (filter_not_has_complementary FSS)) = true :=
  by
  unfold filter_not_has_complementary
  unfold list_of_lists_to_disjunction_of_conjunctions
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · intro a1
    obtain ⟨F, ⟨FS, s3, s2⟩, s1⟩ := a1
    rewrite [← s2] at s1

    apply Exists.intro (list_conj FS)
    constructor
    · apply Exists.intro FS
      constructor
      · constructor
        · exact s3
        · simp only [decide_eq_true_iff]
          intro contra
          simp only [has_complementary_imp_eval_list_conj_false V FS contra] at s1
          contradiction
      · rfl
    · exact s1
  · intro a1
    obtain ⟨F, ⟨FS, ⟨s3, s4⟩, s2⟩, s1⟩ := a1
    exact ⟨F, ⟨FS, s3, s2⟩, s1⟩


lemma eval_eq_eval_to_dnf_v3_simp_1_aux
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (list_of_lists_to_disjunction_of_conjunctions (to_dnf_v3_aux_simp_1 F)) = true :=
  by
  unfold to_dnf_v3_aux_simp_1
  unfold filter_not_has_complementary
  simp only [eval_eq_eval_to_dnf_v3 V F]
  apply eval_list_of_lists_to_disjunction_of_conjunctions_eq_eval_list_of_lists_to_disjunction_of_conjunctions_filter_not_has_complementary


lemma eval_eq_eval_to_dnf_v3_simp_1
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (to_dnf_v3_simp_1 F) = true :=
  by
  unfold to_dnf_v3_simp_1
  apply eval_eq_eval_to_dnf_v3_simp_1_aux


-------------------------------------------------------------------------------


example
  (PS QS : List Formula_)
  (h1 : is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions [PS, QS])) :
  is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions [PS]) :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions at h1
  simp only [List.map_cons, List.map_nil] at h1
  unfold list_disj at h1

  cases h1
  case rule_1 ih =>
    contradiction
  case rule_2 ih_1 ih_2 =>
    unfold list_of_lists_to_disjunction_of_conjunctions
    simp only [List.map_cons, List.map_nil]
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    exact ih_1


example
  (PS QS : List Formula_)
  (h1 : is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions [PS, QS])) :
  is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions [QS]) :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions at h1
  simp only [List.map_cons, List.map_nil] at h1
  unfold list_disj at h1

  cases h1
  case rule_1 ih =>
    contradiction
  case rule_2 ih_1 ih_2 =>
    unfold list_of_lists_to_disjunction_of_conjunctions
    simp only [List.map_cons, List.map_nil]
    exact ih_2


lemma is_dnf_ind_v1_list_of_lists_to_disjunction_of_conjunctions_cons_left
  (hd : List Formula_)
  (tl : List (List Formula_))
  (h1 : is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions (hd :: tl))) :
  is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions tl) :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions at h1
  simp only [List.map_cons] at h1

  unfold list_of_lists_to_disjunction_of_conjunctions
  apply list_disj_cons_is_dnf_ind_v1_imp_list_disj_tail_is_dnf_ind_v1 (list_conj hd)
  exact h1


lemma is_dnf_ind_v1_list_of_lists_to_disjunction_of_conjunctions_cons_right
  (hd : List Formula_)
  (tl : List (List Formula_))
  (h1 : is_conj_ind_v1 (list_conj hd))
  (h2 : is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions tl)) :
  is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions (hd :: tl)) :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions at h2

  unfold list_of_lists_to_disjunction_of_conjunctions
  apply hd_is_conj_ind_v1_and_list_disj_tail_is_dnf_ind_v1_imp_list_disj_cons_is_dnf_ind_v1
  · exact h1
  · exact h2


lemma is_dnf_ind_v1_list_of_lists_to_disjunction_of_conjunctions_filter
  (FSS : List (List Formula_))
  (pred : List Formula_ → Bool)
  (h1 : is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions FSS)) :
  is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions (List.filter pred FSS)) :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions at h1

  unfold list_of_lists_to_disjunction_of_conjunctions
  induction FSS
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
          apply is_dnf_ind_v1_list_of_lists_to_disjunction_of_conjunctions_cons_right
          · exact ih_1
          · apply ih
            simp only [List.map_cons]
            exact ih_2
    case neg c1 =>
      apply ih
      exact is_dnf_ind_v1_list_of_lists_to_disjunction_of_conjunctions_cons_left hd tl h1


lemma is_dnf_ind_v1_to_dnf_v3_simp_1_aux
  (F : Formula_)
  (h1 : is_nnf_rec_v1 F) :
  is_dnf_ind_v1 (list_of_lists_to_disjunction_of_conjunctions (to_dnf_v3_aux_simp_1 F)) :=
  by
  unfold to_dnf_v3_aux_simp_1
  unfold filter_not_has_complementary
  apply is_dnf_ind_v1_list_of_lists_to_disjunction_of_conjunctions_filter
  exact is_nnf_rec_v1_imp_to_dnf_v3_is_dnf_ind_v1 F h1


lemma is_dnf_ind_v1_to_dnf_v3_simp_1
  (F : Formula_)
  (h1 : is_nnf_rec_v1 F) :
  is_dnf_ind_v1 (to_dnf_v3_simp_1 F) :=
  by
  unfold to_dnf_v3_simp_1
  apply is_dnf_ind_v1_to_dnf_v3_simp_1_aux
  exact h1


#lint
