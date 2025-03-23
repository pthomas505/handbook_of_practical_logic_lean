import MathlibExtraLean.FunctionUpdateFromListOfPairsITE

import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.IsDNF
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.ListConj
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.MkLits
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.ListDisj
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.GenAllValuations

import Mathlib.Tactic


set_option autoImplicit false


namespace Bool_


open Formula_


def gen_all_satisfying_valuations_as_list_of_total_functions
  (init : ValuationAsTotalFunction)
  (F : Formula_) :
  List ValuationAsTotalFunction :=
  (gen_all_valuations_as_list_of_total_functions init F.atom_list.dedup).filter (fun (V : ValuationAsTotalFunction) => eval V F = true)


-------------------------------------------------------------------------------


def to_dnf
  (init : ValuationAsTotalFunction)
  (F : Formula_) :
  Formula_ :=
  list_disj ((gen_all_satisfying_valuations_as_list_of_total_functions init F).map (mk_lits F.atom_list.dedup))


#eval (to_dnf (fun _ => false) (Formula_| ((P \/ (Q /\ R)) /\ (~P \/ ~R)))).toString

#eval (to_dnf (fun _ => true) (Formula_| ((P \/ (Q /\ R)) /\ (~P \/ ~R)))).toString


example
  (init : ValuationAsTotalFunction)
  (F : Formula_) :
  is_dnf_ind (to_dnf init F) :=
  by
  unfold to_dnf
  apply list_disj_of_is_conj_ind_is_dnf_ind
  intro F' a1
  simp only [List.mem_map] at a1
  obtain ⟨V, ⟨a1_left, a1_right⟩⟩ := a1
  rewrite [← a1_right]
  apply mk_lits_is_conj_ind


lemma eval_eq_true_imp_eval_to_dnf_eq_true
  (init : ValuationAsTotalFunction)
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : ∀ (X : String), X ∉ F.atom_list.dedup → V X = init X)
  (h2 : eval V F = true) :
  eval V (to_dnf init F) = true :=
  by
  unfold to_dnf
  apply eval_exists_eq_true_imp_eval_list_disj_eq_true
  simp only [List.mem_map]
  apply Exists.intro (mk_lits F.atom_list.dedup V)
  constructor
  · apply Exists.intro V
    constructor
    · unfold gen_all_satisfying_valuations_as_list_of_total_functions
      simp only [List.mem_filter]
      constructor
      · apply gen_all_valuations_as_list_of_total_functions_is_complete
        exact h1
      · simp only [Bool.decide_eq_true]
        exact h2
    · rfl
  · apply eval_mk_lits_eq_true


lemma eval_to_dnf_eq_true_imp_eval_eq_true
  (init : ValuationAsTotalFunction)
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : eval V (to_dnf init F) = true) :
  eval V F = true :=
  by
  unfold to_dnf at h1
  rewrite [← eval_exists_eq_true_iff_eval_list_disj_eq_true] at h1
  obtain ⟨F', ⟨h1_left, h1_right⟩⟩ := h1
  unfold gen_all_satisfying_valuations_as_list_of_total_functions at h1_left
  simp only [Bool.decide_eq_true, List.mem_map, List.mem_filter] at h1_left
  obtain ⟨V', ⟨h1_left_left_left, h1_left_left_right⟩, h1_left_right⟩ := h1_left
  rewrite [← h1_left_right] at h1_right
  clear h1_left_right
  obtain s1 := eval_mk_lits_eq_true_imp_valuations_eq_on_atom_list V V' F.atom_list.dedup h1_right
  rewrite [← h1_left_left_right]
  apply theorem_2_2
  intro X a1
  apply s1
  simp only [List.mem_dedup]
  rewrite [← atom_occurs_in_iff_mem_atom_list]
  exact a1


lemma aux_2
  {α β γ : Type}
  (f : α → γ)
  (g : β → γ)
  (xs : List α)
  (ys : List β)
  (h1 : xs.length = ys.length)
  (h2 : ∀ (p : α × β), p ∈ List.zip xs ys → f p.fst = g p.snd) :
  List.map f xs = List.map g ys :=
  by
  induction xs generalizing ys f g
  case nil =>
    cases ys
    case nil =>
      simp only [List.map_nil]
    case cons ys_hd ys_tl =>
      simp only [List.length_nil, List.length_cons] at h1
      simp only [Nat.zero_ne_add_one] at h1
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.length_cons, List.length_nil] at h1
      simp only [Nat.add_one_ne_zero] at h1
    case cons ys_hd ys_tl =>
      simp only [List.length_cons, add_left_inj] at h1

      simp only [List.zip_cons_cons, List.mem_cons] at h2

      simp only [List.map_cons, List.cons.injEq]
      constructor
      · specialize h2 (xs_hd, ys_hd)
        apply h2
        left
        rfl
      · apply xs_ih
        · exact h1
        · intro p a1
          apply h2
          right
          exact a1


lemma aux_3
  {α : Type}
  (xs ys : List α)
  (pred : α → Bool)
  (p : α × α)
  (h1 : p ∈ List.zip (List.filter pred xs) (List.filter pred ys))
  (h2 : ∀ (q : α × α), q ∈ List.zip xs ys → pred q.1 = pred q.2) :
  p ∈ List.zip xs ys :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [List.filter_nil, List.zip_nil_left, List.not_mem_nil] at h1
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.filter_nil, List.zip_nil_right, List.not_mem_nil] at h1
    case cons ys_hd ys_tl =>
      simp only [List.filter_cons] at h1

      simp only [List.zip_cons_cons, List.mem_cons] at h2

      simp only [List.zip_cons_cons, List.mem_cons]
      split_ifs at h1
      case pos c1 c2 =>
        simp only [List.zip_cons_cons, List.mem_cons] at h1
        cases h1
        case inl h1 =>
          left
          exact h1
        case inr h1 =>
          right
          apply xs_ih
          · exact h1
          · intro q a1
            apply h2
            right
            exact a1
      case neg c1 c2 =>
        exfalso
        apply c2
        rewrite [← c1]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        rewrite [← h2]
        · rfl
        · left
          exact trivial
      case pos c1 c2 =>
        exfalso
        apply c1
        rewrite [← c2]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        apply h2
        left
        exact trivial
      case neg c1 c2 =>
        right
        apply xs_ih
        · exact h1
        · intro q a1
          apply h2
          right
          exact a1


lemma pred_eq_all_mem_zip_imp_filter_length_eq
  {α : Type}
  (xs ys : List α)
  (pred : α → Bool)
  (h1 : xs.length = ys.length)
  (h2 : ∀ (p : α × α), p ∈ List.zip xs ys → pred p.1 = pred p.2) :
  (List.filter pred xs).length = (List.filter pred ys).length :=
  by
  induction xs generalizing ys
  case nil =>
    cases ys
    case nil =>
      simp only [List.filter_nil, List.length_nil]
    case cons ys_hd ys_tl =>
      simp only [List.length_nil, List.length_cons] at h1
      simp only [Nat.zero_ne_add_one] at h1
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.length_cons, List.length_nil] at h1
      simp only [Nat.add_one_ne_zero] at h1
    case cons ys_hd ys_tl =>
      simp only [List.length_cons, add_left_inj] at h1

      simp only [List.zip_cons_cons, List.mem_cons] at h2

      simp only [List.filter_cons]
      split_ifs
      case pos c1 c2 =>
        simp only [List.length_cons, add_left_inj]
        apply xs_ih
        · exact h1
        · intro p a1
          apply h2
          right
          exact a1
      case neg c1 c2 =>
        exfalso
        apply c2
        rewrite [← c1]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        rewrite [← h2]
        · rfl
        · left
          exact trivial
      case pos c1 c2 =>
        exfalso
        apply c1
        rewrite [← c2]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        apply h2
        left
        exact trivial
      case neg c1 c2 =>
        apply xs_ih
        · exact h1
        · intro p a1
          apply h2
          right
          exact a1


example
  (init_1 init_2 : ValuationAsTotalFunction)
  (atom_list : List String) :
  List.map (mk_lits atom_list)
  (gen_all_valuations_as_list_of_total_functions init_1 atom_list) =
  List.map (mk_lits atom_list)
  (gen_all_valuations_as_list_of_total_functions init_2 atom_list) :=
  by
  apply aux_2
  · apply gen_all_valuations_as_list_of_total_functions_length_eq
  · intro p a1
    apply eq_on_mem_imp_mk_lits_eq
    intro X a2
    apply gen_all_valuations_as_list_of_total_functions_eq_on_atom_list init_1 init_2 atom_list
    · exact a1
    · exact a2


lemma aux_4
  (init_1 init_2 : ValuationAsTotalFunction)
  (F : Formula_) :
  List.map (mk_lits F.atom_list.dedup)
    (List.filter (fun V ↦ eval V F) (gen_all_valuations_as_list_of_total_functions init_1 F.atom_list.dedup)) =
  List.map (mk_lits F.atom_list.dedup)
    (List.filter (fun V ↦ eval V F) (gen_all_valuations_as_list_of_total_functions init_2 F.atom_list.dedup)) :=
  by
  apply aux_2
  · apply pred_eq_all_mem_zip_imp_filter_length_eq
    · apply gen_all_valuations_as_list_of_total_functions_length_eq
    · intro p a1
      apply theorem_2_2
      intro X a2
      apply gen_all_valuations_as_list_of_total_functions_eq_on_atom_list init_1 init_2 F.atom_list.dedup
      · exact a1
      · simp only [List.mem_dedup]
        simp only [← atom_occurs_in_iff_mem_atom_list]
        exact a2
  · intro p a1
    apply eq_on_mem_imp_mk_lits_eq
    intro X a2
    apply gen_all_valuations_as_list_of_total_functions_eq_on_atom_list init_1 init_2 F.atom_list.dedup
    · apply aux_3 (gen_all_valuations_as_list_of_total_functions init_1 F.atom_list.dedup) (gen_all_valuations_as_list_of_total_functions init_2 F.atom_list.dedup) (fun V => eval V F)
      · exact a1
      · intro q a3
        apply mem_zip_gen_all_valuations_as_list_of_total_functions_imp_eval_eq init_1 init_2
        exact a3
    · exact a2


example
  (init_1 init_2 : ValuationAsTotalFunction)
  (F : Formula_)
  (X : String)
  (p : ValuationAsTotalFunction × ValuationAsTotalFunction)
  (h1 : p ∈ List.zip
    (List.filter (fun (V : ValuationAsTotalFunction) => eval V F) (gen_all_valuations_as_list_of_total_functions init_1 F.atom_list.dedup))
    (List.filter (fun (V : ValuationAsTotalFunction) => eval V F) (gen_all_valuations_as_list_of_total_functions init_2 F.atom_list.dedup)))
  (h2 : X ∈ F.atom_list.dedup) :
  p.1 X = p.2 X :=
  by
  apply gen_all_valuations_as_list_of_total_functions_eq_on_atom_list init_1 init_2 F.atom_list.dedup
  · apply aux_3 (gen_all_valuations_as_list_of_total_functions init_1 F.atom_list.dedup) (gen_all_valuations_as_list_of_total_functions init_2 F.atom_list.dedup) (fun (V : ValuationAsTotalFunction) => eval V F)
    · exact h1
    · intro q a1
      apply mem_zip_gen_all_valuations_as_list_of_total_functions_imp_eval_eq
      exact a1
  · exact h2


example
  (init_1 init_2 : ValuationAsTotalFunction)
  (F : Formula_) :
  to_dnf init_1 F = to_dnf init_2 F :=
  by
  unfold to_dnf
  unfold gen_all_satisfying_valuations_as_list_of_total_functions
  congr 1
  simp only [Bool.decide_eq_true]
  apply aux_4
