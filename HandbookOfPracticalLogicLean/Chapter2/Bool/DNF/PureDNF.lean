import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.ToDNF
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.AllPairs


set_option autoImplicit false


namespace Bool_


open Formula_


def pure_dnf :
  Formula_ → List (List Formula_)
  | and_ p q => all_pairs_v4 List.union (pure_dnf p) (pure_dnf q)
  | or_ p q => (pure_dnf p) ∪ (pure_dnf q)
  | F => [[F]]

#eval (pure_dnf (Formula_| ((p \/ (q /\ r)) /\ (~p \/ ~ r)))).toString


def dnf_list_of_list_to_formula
  (l : List (List Formula_)) :
  Formula_ :=
  list_disj (List.map list_conj l)


#eval (dnf_list_of_list_to_formula [[atom_ "P", atom_ "Q"], [not_ (atom_ "P"), atom_ "R"]]).toString


lemma dnf_list_of_list_to_formula_singleton
  (F : Formula_) :
  dnf_list_of_list_to_formula [[F]] = F :=
  by
  unfold dnf_list_of_list_to_formula
  simp only [List.map_cons, List.map_nil]
  unfold list_conj
  unfold list_disj
  rfl


lemma mem_list_mem_pure_dnf_of_nnf_imp_is_constant_or_literal
  (F : Formula_)
  (l : List Formula_)
  (P : Formula_)
  (h1 : is_nnf F)
  (h2 : l ∈ pure_dnf F)
  (h3 : P ∈ l) :
  is_constant_ind P ∨ is_literal_ind P :=
  by
  induction F generalizing l
  case false_ =>
    unfold pure_dnf at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    left
    apply is_constant_ind.rule_1
  case true_ =>
    unfold pure_dnf at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    left
    apply is_constant_ind.rule_2
  case atom_ X =>
    unfold pure_dnf at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    right
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    unfold pure_dnf at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    cases phi
    case atom_ X =>
      right
      apply is_literal_ind.rule_2
    all_goals
      unfold is_nnf at h1
      contradiction
  case and_ phi psi phi_ih psi_ih =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold pure_dnf at h2

    obtain s1 := mem_all_pairs_v4_union_imp_eq_union (pure_dnf phi) (pure_dnf psi) l h2
    obtain ⟨xs, ys, xs_mem, ys_mem, eq⟩ := s1
    rewrite [← eq] at h3

    simp only [List.mem_union_iff] at h3
    cases h3
    case inl h3 =>
      apply phi_ih xs
      · exact h1_left
      · exact xs_mem
      · exact h3
    case inr h3 =>
      apply psi_ih ys
      · exact h1_right
      · exact ys_mem
      · exact h3
  case or_ phi psi phi_ih psi_ih =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold pure_dnf at h2
    simp only [List.mem_union_iff] at h2

    cases h2
    case inl h2 =>
      apply phi_ih l
      · exact h1_left
      · exact h2
      · exact h3
    case inr h2 =>
      apply psi_ih l
      · exact h1_right
      · exact h2
      · exact h3
  all_goals
    unfold is_nnf at h1
    contradiction


example
  (F : Formula_)
  (h1 : is_nnf F) :
  is_dnf_ind (dnf_list_of_list_to_formula (pure_dnf F)) :=
  by
  cases F
  case false_ =>
    unfold pure_dnf
    simp only [dnf_list_of_list_to_formula_singleton]
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_1
  case true_ =>
    unfold pure_dnf
    simp only [dnf_list_of_list_to_formula_singleton]
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_2
  case atom_ X =>
    unfold pure_dnf
    simp only [dnf_list_of_list_to_formula_singleton]
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_4
    apply is_literal_ind.rule_1
  case not_ phi =>
    unfold pure_dnf
    simp only [dnf_list_of_list_to_formula_singleton]
    cases phi
    case atom_ X =>
      apply is_dnf_ind.rule_2
      apply is_conj_ind.rule_4
      apply is_literal_ind.rule_2
    all_goals
      unfold is_nnf at h1
      contradiction
  case and_ phi psi =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    apply list_disj_of_is_conj_ind_is_dnf_ind
    intro F a1
    simp only [List.mem_map] at a1
    obtain ⟨l, a1_left, a1_right⟩ := a1
    rewrite [← a1_right]
    apply list_conj_of_is_constant_ind_or_is_literal_ind_is_conj_ind
    intro P a2

    obtain s1 := mem_all_pairs_v4_union_imp_eq_union (pure_dnf phi) (pure_dnf psi) l a1_left
    obtain ⟨xs, ys, xs_mem, ys_mem, eq⟩ := s1
    rewrite [← eq] at a2
    simp only [List.mem_union_iff] at a2

    cases a2
    case inl a2 =>
      apply mem_list_mem_pure_dnf_of_nnf_imp_is_constant_or_literal phi xs
      · exact h1_left
      · exact xs_mem
      · exact a2
    case inr a2 =>
      apply mem_list_mem_pure_dnf_of_nnf_imp_is_constant_or_literal psi ys
      · exact h1_right
      · exact ys_mem
      · exact a2
  case or_ phi psi =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    apply list_disj_of_is_conj_ind_is_dnf_ind
    intro F a1
    simp only [List.mem_map, List.mem_union_iff] at a1
    obtain ⟨l, a1_left, a1_right⟩ := a1
    rewrite [← a1_right]
    apply list_conj_of_is_constant_ind_or_is_literal_ind_is_conj_ind
    intro P a2

    cases a1_left
    case inl a1_left =>
      apply mem_list_mem_pure_dnf_of_nnf_imp_is_constant_or_literal phi l
      · exact h1_left
      · exact a1_left
      · exact a2
    case inr a1_left =>
      apply mem_list_mem_pure_dnf_of_nnf_imp_is_constant_or_literal psi l
      · exact h1_right
      · exact a1_left
      · exact a2
  all_goals
    unfold is_nnf at h1
    contradiction


lemma eval_dnf_list_of_list_to_formula_pure_dnf_eq_eval
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V (dnf_list_of_list_to_formula (pure_dnf F)) = true ↔ eval V F = true :=
  by
  induction F
  case and_ phi psi phi_ih psi_ih =>
    unfold dnf_list_of_list_to_formula at phi_ih
    unfold dnf_list_of_list_to_formula at psi_ih

    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [eval]
    simp only [bool_iff_prop_and]
    rewrite [← phi_ih]
    rewrite [← psi_ih]
    simp only [← eval_exists_eq_true_iff_eval_list_disj_eq_true]
    simp only [List.mem_map]
    simp only [mem_all_pairs_v4_union_iff_eq_union]
    constructor
    · intro a1
      obtain ⟨F, ⟨P, ⟨xs, ys, ⟨xs_mem, ys_mem, eq⟩⟩, a1_left⟩, a1_right⟩ := a1
      rewrite [← a1_left] at a1_right
      rewrite [← eq] at a1_right
      simp only [eval_list_conj_union] at a1_right
      obtain ⟨a1_right_left, a1_right_right⟩ := a1_right
      constructor
      · apply Exists.intro (list_conj xs)
        constructor
        · apply Exists.intro xs
          exact ⟨xs_mem, rfl⟩
        · exact a1_right_left
      · apply Exists.intro (list_conj ys)
        constructor
        · apply Exists.intro ys
          exact ⟨ys_mem, rfl⟩
        · exact a1_right_right
    · intro a1
      obtain ⟨⟨P, ⟨xs, xs_mem, a1_left_left⟩, a1_left_right⟩ , ⟨Q, ⟨ys, ys_mem, a1_right_left⟩, a1_right_right⟩ ⟩ := a1
      rewrite [← a1_left_left] at a1_left_right
      rewrite [← a1_right_left] at a1_right_right
      apply Exists.intro (list_conj (xs ∪ ys))
      constructor
      · apply Exists.intro (xs ∪ ys)
        constructor
        · apply Exists.intro xs
          apply Exists.intro ys
          exact ⟨xs_mem, ys_mem, rfl⟩
        · rfl
      · simp only [eval_list_conj_union]
        exact ⟨a1_left_right, a1_right_right⟩
  case or_ phi psi phi_ih psi_ih =>
    unfold dnf_list_of_list_to_formula at phi_ih
    unfold dnf_list_of_list_to_formula at psi_ih

    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [eval]
    simp only [bool_iff_prop_or]
    rewrite [← phi_ih]
    rewrite [← psi_ih]
    simp only [← eval_exists_eq_true_iff_eval_list_disj_eq_true]
    simp only [List.mem_map, List.mem_union_iff]
    constructor
    · intro a1
      obtain ⟨F, ⟨l, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
      cases a1_left_left
      case inl a1_left_left =>
        left
        apply Exists.intro F
        constructor
        · apply Exists.intro l
          exact ⟨a1_left_left, a1_left_right⟩
        · exact a1_right
      case inr a1_left_left =>
        right
        apply Exists.intro F
        constructor
        · apply Exists.intro l
          exact ⟨a1_left_left, a1_left_right⟩
        · exact a1_right
    · intro a1
      cases a1
      case inl a1 =>
        obtain ⟨F, ⟨l, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
        apply Exists.intro F
        constructor
        · apply Exists.intro l
          constructor
          · left
            exact a1_left_left
          · exact a1_left_right
        · exact a1_right
      case inr a1 =>
        obtain ⟨F, ⟨l, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
        apply Exists.intro F
        constructor
        · apply Exists.intro l
          constructor
          · right
            exact a1_left_left
          · exact a1_left_right
        · exact a1_right
  all_goals
    rfl


-------------------------------------------------------------------------------

/-
def has_complementary :
  List Formula_ → Prop
  | [] => False
  | (P :: tl) =>
      (P.is_literal ∧ ∃ (Q : Formula_), Q ∈ tl ∧ Q.is_literal ∧ negate_literal Q = P) ∨
      has_complementary tl
-/


def has_complementary
  (l : List Formula_) :
  Prop :=
  ∃ (P : Formula_), P ∈ l ∧ P.is_literal ∧ ∃ (Q : Formula_), Q ∈ l ∧ Q.is_literal ∧ negate_literal Q = P

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


#eval (List.filter (fun (l : List Formula_) => ¬ (has_complementary l)) (pure_dnf (Formula_| ((P \/ (Q /\ R)) /\ (~P \/ ~R))))).toString


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
          simp only [← eval_all_eq_true_iff_eval_list_conj_eq_true]
          intro a1

          rewrite [← P_mem] at a1
          rewrite [← eq] at a1
          rewrite [eval_negate_literal V Q Q_lit] at a1
          simp only [bool_iff_prop_not] at a1

          intro contra
          apply a1
          apply contra
          simp only [List.mem_cons]
          exact Q_mem
      case inr P_mem =>
        cases Q_mem
        case inl Q_mem =>
          simp only [← eval_all_eq_true_iff_eval_list_conj_eq_true]
          intro a1

          rewrite [← Q_mem] at a1
          have s1 : ¬ eval V P = true :=
          by
            rewrite [← eq]
            rewrite [eval_negate_literal V Q Q_lit]
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
  eval V (dnf_list_of_list_to_formula (List.filter (fun (l : List Formula_) => ¬ (has_complementary l)) ll)) = true ↔
    eval V (dnf_list_of_list_to_formula ll) :=
  by
  unfold dnf_list_of_list_to_formula
  simp only [← eval_exists_eq_true_iff_eval_list_disj_eq_true]
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


example
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V (dnf_list_of_list_to_formula (List.filter (fun (l : List Formula_) => ¬ (has_complementary l)) (pure_dnf F))) = true ↔ eval V F = true :=
  by
  simp only [← eval_dnf_list_of_list_to_formula_pure_dnf_eq_eval V F]
  apply eval_dnf_list_of_list_to_formula_filter_not_has_complementary
