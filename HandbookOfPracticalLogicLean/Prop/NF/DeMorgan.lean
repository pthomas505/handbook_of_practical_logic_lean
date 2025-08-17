import HandbookOfPracticalLogicLean.Prop.NF.ListOfListsTo

import HandbookOfPracticalLogicLean.Prop.NF.ListConj.Semantics
import HandbookOfPracticalLogicLean.Prop.NF.ListDisj.Semantics


set_option autoImplicit false


open Formula_


/--
  `map_map_not FSS` := Transforms every formula `F` in the list of lists of formulas `FSS` to `not_ F`.
-/
def map_map_not
  (FSS : List (List Formula_)) :
  List (List Formula_) :=
  List.map (List.map not_) FSS

#eval map_map_not ([[var_ "P", var_ "Q"], [var_ "R", var_ "S"]])


lemma de_morgan_1
  (V : ValuationAsTotalFunction)
  (P Q : Formula_) :
  eval V (not_ (and_ P Q)) = true ↔
    eval V (or_ (not_ P) (not_ Q)) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_or]
  simp only [bool_iff_prop_not]
  simp only [bool_iff_prop_and]
  constructor
  · intro a1
    by_cases c1 : eval V P = true
    case pos =>
      right
      intro contra
      apply a1
      exact ⟨c1, contra⟩
    case neg =>
      left
      exact c1
  · intro a1
    intro contra
    obtain ⟨contra_left, contra_right⟩ := contra
    cases a1
    case inl a1 =>
      apply a1
      exact contra_left
    case inr a1 =>
      apply a1
      exact contra_right


lemma de_morgan_2
  (V : ValuationAsTotalFunction)
  (P Q : Formula_) :
  eval V (not_ (or_ P Q)) = true ↔
    eval V (and_ (not_ P) (not_ Q)) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_and]
  simp only [bool_iff_prop_not]
  simp only [bool_iff_prop_or]
  constructor
  · intro a1
    constructor
    · intro contra
      apply a1
      left
      exact contra
    · intro contra
      apply a1
      right
      exact contra
  · intro a1 contra
    obtain ⟨a1_left, a1_right⟩ := a1
    cases contra
    case inl contra =>
      apply a1_left
      exact contra
    case inr contra =>
      apply a1_right
      exact contra


lemma de_morgan_list_1
  (V : ValuationAsTotalFunction)
  (FS : List Formula_) :
  eval V (not_ (list_conj FS)) = true ↔
    eval V (list_disj (List.map not_ FS)) = true :=
  by
  induction FS
  case nil =>
    simp only [List.map_nil]
    simp only [list_conj]
    simp only [list_disj]
    simp only [eval]
    simp only [b_not]
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      unfold list_disj
      rfl
    case cons tl_hd tl_tl =>
      simp only [List.map_cons] at ih

      simp only [List.map_cons]
      unfold list_conj
      unfold list_disj
      simp only [de_morgan_1]
      unfold eval
      simp only [bool_iff_prop_or]
      rewrite [ih]
      rfl


lemma de_morgan_list_2
  (V : ValuationAsTotalFunction)
  (FS : List Formula_) :
  eval V (not_ (list_disj FS)) = true ↔
    eval V (list_conj (List.map not_ FS)) = true :=
  by
  induction FS
  case nil =>
    simp only [List.map_nil]
    simp only [list_disj]
    simp only [list_conj]
    simp only [eval]
    simp only [b_not]
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [List.map_cons, List.map_nil]
      unfold list_disj
      unfold list_conj
      rfl
    case cons tl_hd tl_tl =>
      simp only [List.map_cons] at ih

      simp only [List.map_cons]
      unfold list_disj
      unfold list_conj
      simp only [de_morgan_2]
      unfold eval
      simp only [bool_iff_prop_and]
      rewrite [ih]
      rfl


lemma de_morgan_list_alt_1
  (V : ValuationAsTotalFunction)
  (FS : List Formula_) :
  eval V (list_conj FS) = true ↔
    eval V (not_ (list_disj (List.map not_ FS))) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_not]
  rewrite [← de_morgan_list_1]
  simp only [eval]
  simp only [bool_iff_prop_not]
  simp only [Bool.not_eq_true, Bool.not_eq_false]


lemma de_morgan_list_alt_2
  (V : ValuationAsTotalFunction)
  (FS : List Formula_) :
  eval V (list_disj FS) = true ↔
    eval V (not_ (list_conj (List.map not_ FS))) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_not]
  rewrite [← de_morgan_list_2]
  simp only [eval]
  simp only [bool_iff_prop_not]
  simp only [Bool.not_eq_true, Bool.not_eq_false]


lemma de_morgan_list_of_lists_1
  (V : ValuationAsTotalFunction)
  (FSS : List (List Formula_)) :
  eval V (not_ (list_of_lists_to_disjunction_of_conjunctions FSS)) = true ↔
    eval V (list_of_lists_to_conjunction_of_disjunctions (map_map_not FSS)) :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions
  unfold list_of_lists_to_conjunction_of_disjunctions
  unfold map_map_not
  rewrite [de_morgan_list_2]
  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
  simp only [List.map_map, List.mem_map, Function.comp_apply]
  constructor
  · intro a1 F a2
    obtain ⟨FS, a2_left, a2_right⟩ := a2
    rewrite [← a2_right]
    rewrite [← de_morgan_list_1]
    apply a1
    apply Exists.intro FS
    constructor
    · exact a2_left
    · rfl
  · intro a1 F a2
    obtain ⟨FS, a2_left, a2_right⟩ := a2
    rewrite [← a2_right]
    rewrite [de_morgan_list_1]
    apply a1
    apply Exists.intro FS
    constructor
    · exact a2_left
    · rfl


lemma de_morgan_list_of_lists_2
  (V : ValuationAsTotalFunction)
  (FSS : List (List Formula_)) :
  eval V (not_ (list_of_lists_to_conjunction_of_disjunctions FSS)) = true ↔
    eval V (list_of_lists_to_disjunction_of_conjunctions (map_map_not FSS)) :=
  by
  unfold list_of_lists_to_conjunction_of_disjunctions
  unfold list_of_lists_to_disjunction_of_conjunctions
  unfold map_map_not
  rewrite [de_morgan_list_1]
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.map_map, List.mem_map, Function.comp_apply]
  simp only [exists_exists_and_eq_and]
  constructor
  · intro a1
    obtain ⟨FS, a1_left, a1_right⟩ := a1
    rewrite [de_morgan_list_2] at a1_right
    apply Exists.intro FS
    exact ⟨a1_left, a1_right⟩
  · intro a1
    obtain ⟨FS, a1_left, a1_right⟩ := a1
    rewrite [← de_morgan_list_2] at a1_right
    apply Exists.intro FS
    exact ⟨a1_left, a1_right⟩


#lint
