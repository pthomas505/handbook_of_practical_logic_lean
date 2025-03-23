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




-------------------------------------------------------------------------------




-------------------------------------------------------------------------------




-------------------------------------------------------------------------------




-------------------------------------------------------------------------------




-------------------------------------------------------------------------------


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


-------------------------------------------------------------------------------


def distrib :
  Formula_ → Formula_
  | and_ p (or_ q r) => or_ (distrib (and_ p q)) (distrib (and_ p r))
  | and_ (or_ p q) r => or_ (distrib (and_ p r)) (distrib (and_ q r))
  | F => F


def raw_dnf :
  Formula_ → Formula_
  | and_ p q => distrib (and_ (raw_dnf p) (raw_dnf q))
  | or_ p q => or_ (raw_dnf p) (raw_dnf q)
  | F => F


#eval (raw_dnf (Formula_| ((p \/ (q /\ r)) /\ (~p \/ ~ r)))).toString


/-
https://www.cl.cam.ac.uk/~jrh13/atp/OCaml/lib.ml

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;
-/

def itlist
  {α β : Type}
  (f : α → β → β)
  (l : List α)
  (b : β) :
  β :=
  match l with
  | [] => b
  | h :: t => f h (itlist f t b)


example
  {α β : Type}
  (f : α → β → β)
  (l : List α)
  (b : β) :
  itlist f l b = List.foldr f b l :=
  by
  induction l
  case nil =>
    unfold itlist
    unfold List.foldr
    rfl
  case cons hd tl ih =>
    unfold itlist
    unfold List.foldr
    rewrite [ih]
    rfl


/-
https://www.cl.cam.ac.uk/~jrh13/atp/OCaml/lib.ml

let rec allpairs f l1 l2 =
  match l1 with
   h1::t1 ->  itlist (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> [];;
-/

def all_pairs
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  List (List α) :=
  match l1 with
  | [] => []
  | hd :: tl =>
    List.foldr
      (fun (next : List α) (prev : List (List α)) => (f hd next) :: prev)
        (all_pairs f tl l2)
          l2


#eval all_pairs List.append [[1]] []
#eval all_pairs List.append [[1], [2]] []
#eval all_pairs List.append [[1]] [[4]]
#eval all_pairs List.append [[1], [2]] [[4]]
#eval all_pairs List.append [[1], [2]] [[4], [5]]
#eval all_pairs List.append [[1]] [[4], [5]]
#eval all_pairs List.append [[1]] [[4], [5], [6]]
#eval all_pairs List.append [] [[4], [5]]


-- (a + b) * (c + d)
-- a * c + a * d + b * c + b * d


lemma all_pairs_nil_right
  {α : Type}
  (f : List α → List α → List α)
  (l : List (List α)) :
  all_pairs f l [] = [] :=
  by
  induction l
  case nil =>
    unfold all_pairs
    rfl
  case cons hd tl ih =>
    unfold all_pairs
    simp only [List.foldr_nil]
    exact ih


lemma all_pairs_singleton_left_cons_right
  {α : Type}
  (f : List α → List α → List α)
  (xs : List α)
  (ys : List α)
  (yss : List (List α)) :
  all_pairs f [xs] (ys :: yss) = all_pairs f [xs] [ys] ++ all_pairs f [xs] yss :=
  by
  simp only [all_pairs]
  simp only [List.foldr_cons, List.foldr_nil, List.singleton_append]


def distrib_one
  {α : Type}
  (f : List α → List α → List α)
  (xs : List α)
  (xss : List (List α)) :
  List (List α) :=
    List.foldr
      (fun (next : List α) (prev : List (List α)) => (f xs next) :: prev) [] xss

#eval distrib_one List.append [0] [[1], [2], [3]]


def all_pairs_alt
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  List (List α) :=
  match l1 with
  | [] => []
  | hd :: tl => distrib_one f hd l2 ++ all_pairs_alt f tl l2


lemma List.foldr_cons_append_init
  {α β : Type}
  (f : α → β)
  (xs_left xs_right : List β)
  (ys : List α) :
  List.foldr (fun (next : α) (prev : List β) => (f next) :: prev) (xs_left ++ xs_right) ys =
    (List.foldr (fun (next : α) (prev : List β) => (f next) :: prev) xs_left ys) ++ xs_right :=
  by
  induction ys
  case nil =>
    simp only [List.foldr_nil]
  case cons hd tl ih =>
    simp only [List.foldr_cons, List.cons_append]
    rewrite [ih]
    rfl


example
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  all_pairs f l1 l2 = all_pairs_alt f l1 l2 :=
  by
  induction l1
  case nil =>
    unfold all_pairs
    unfold all_pairs_alt
    rfl
  case cons l1_hd l1_tl l1_ih =>
    unfold all_pairs
    unfold all_pairs_alt
    unfold distrib_one
    rewrite [l1_ih]

    obtain s1 := List.foldr_cons_append_init (f l1_hd) [] (all_pairs_alt f l1_tl l2) l2
    simp only [List.nil_append] at s1
    exact s1


def all_pairs_alt_alt
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  List (List α) :=
  match l1 with
  | [] => []
  | hd :: tl => List.map (f hd) l2 ++ all_pairs_alt_alt f tl l2


example
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  all_pairs_alt f l1 l2 = all_pairs_alt_alt f l1 l2 :=
  by
  induction l1
  case nil =>
    unfold all_pairs_alt_alt
    unfold all_pairs_alt
    rfl
  case cons hd tl ih =>
    unfold all_pairs_alt_alt
    unfold all_pairs_alt
    unfold distrib_one
    simp only [List.map_eq_foldr]
    rewrite [ih]
    rfl


lemma all_pairs_alt_nil_right
  {α : Type}
  (f : List α → List α → List α)
  (l : List (List α)) :
  all_pairs_alt f l [] = [] :=
  by
  induction l
  case nil =>
    unfold all_pairs_alt
    rfl
  case cons hd tl ih =>
    unfold all_pairs_alt
    unfold distrib_one
    simp only [List.foldr_nil, List.nil_append]
    exact ih


def pure_dnf :
  Formula_ → List (List Formula_)
  | and_ p q => all_pairs_alt_alt List.union (pure_dnf p) (pure_dnf q)
  | or_ p q => (pure_dnf p) ∪ (pure_dnf q)
  | F => [[F]]

#eval (pure_dnf (Formula_| ((p \/ (q /\ r)) /\ (~p \/ ~ r)))).toString


def dnf_list_of_list_to_formula
  (l : List (List Formula_)) :
  Formula_ :=
  list_disj (List.map list_conj l)


#eval (dnf_list_of_list_to_formula [[atom_ "P", atom_ "Q"], [not_ (atom_ "P"), atom_ "R"]]).toString


example
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f : α → β)
  (l1 l2 : List α)
  (h1 : Function.Injective f) :
  List.map f (l1 ∪ l2) = (List.map f l1) ∪ (List.map f l2) :=
  by
  induction l1
  case nil =>
    simp only [List.map_nil]
    simp only [List.nil_union]
  case cons hd tl ih =>
    simp only [List.cons_union, List.map_cons]
    rewrite [← ih]
    unfold List.insert

    have s1 : List.elem (f hd) (List.map f (tl ∪ l2)) = true ↔ List.elem hd (tl ∪ l2) = true :=
    by
      simp only [List.elem_eq_mem, decide_eq_true_eq]
      apply List.mem_map_of_injective
      exact h1

    simp only [s1]
    split_ifs
    case pos c1 =>
      rfl
    case neg c1 =>
      simp only [List.map_cons]


lemma mem_all_pairs_alt_alt_imp_eq_union
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List (List α))
  (l : List α)
  (h1 : l ∈ all_pairs_alt_alt List.union l1 l2) :
  ∃ (xs : List α) (ys : List α), xs ∈ l1 ∧ ys ∈ l2 ∧ xs ∪ ys = l :=
  by
  induction l1
  case nil =>
    unfold all_pairs_alt_alt at h1
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    unfold all_pairs_alt_alt at h1
    simp only [List.mem_append, List.mem_map] at h1
    cases h1
    case inl h1 =>
      obtain ⟨a, h1⟩ := h1
      apply Exists.intro hd
      apply Exists.intro a
      constructor
      · simp only [List.mem_cons]
        left
        exact trivial
      · exact h1
    case inr h1 =>
      specialize ih h1
      obtain ⟨xs, ys, ih_left, ih_right⟩ := ih
      apply Exists.intro xs
      apply Exists.intro ys
      constructor
      · simp only [List.mem_cons]
        right
        exact ih_left
      · exact ih_right


lemma eq_union_imp_mem_all_pairs_alt_alt
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List (List α))
  (l : List α)
  (h1 : ∃ (xs : List α) (ys : List α), xs ∈ l1 ∧ ys ∈ l2 ∧ xs ∪ ys = l) :
  l ∈ all_pairs_alt_alt List.union l1 l2 :=
  by
  obtain ⟨xs, ys, xs_mem, ys_mem, eq⟩ := h1
  induction l1
  case nil =>
    simp only [List.not_mem_nil] at xs_mem
  case cons l1_hd l1_tl l1_ih =>
    simp only [List.mem_cons] at xs_mem

    unfold all_pairs_alt_alt
    simp only [List.mem_append, List.mem_map]
    cases xs_mem
    case inl xs_mem =>
      left
      apply Exists.intro ys
      constructor
      · exact ys_mem
      · rewrite [← xs_mem]
        exact eq
    case inr xs_mem =>
      right
      apply l1_ih
      exact xs_mem


lemma mem_all_pairs_alt_alt_iff_eq_union
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List (List α))
  (l : List α) :
  l ∈ all_pairs_alt_alt List.union l1 l2 ↔
    ∃ (xs : List α) (ys : List α), xs ∈ l1 ∧ ys ∈ l2 ∧ xs ∪ ys = l :=
  by
  constructor
  · apply mem_all_pairs_alt_alt_imp_eq_union
  · apply eq_union_imp_mem_all_pairs_alt_alt


lemma aux_5
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

    obtain s1 := mem_all_pairs_alt_alt_imp_eq_union (pure_dnf phi) (pure_dnf psi) l h2
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
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_1
  case true_ =>
    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_2
  case atom_ X =>
    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_4
    apply is_literal_ind.rule_1
  case not_ phi =>
    cases phi
    case atom_ X =>
      unfold pure_dnf
      unfold dnf_list_of_list_to_formula
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      unfold list_disj
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

    obtain s1 := mem_all_pairs_alt_alt_imp_eq_union (pure_dnf phi) (pure_dnf psi) l a1_left
    obtain ⟨xs, ys, xs_mem, ys_mem, eq⟩ := s1
    rewrite [← eq] at a2
    simp only [List.mem_union_iff] at a2

    cases a2
    case inl a2 =>
      apply aux_5 phi xs
      · exact h1_left
      · exact xs_mem
      · exact a2
    case inr a2 =>
      apply aux_5 psi ys
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
      apply aux_5 phi l
      · exact h1_left
      · exact a1_left
      · exact a2
    case inr a1_left =>
      apply aux_5 psi l
      · exact h1_right
      · exact a1_left
      · exact a2
  all_goals
    unfold is_nnf at h1
    contradiction


example
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : is_nnf F) :
  eval V (dnf_list_of_list_to_formula (pure_dnf F)) = true ↔ eval V F = true :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    rfl
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      unfold pure_dnf
      unfold dnf_list_of_list_to_formula
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      unfold list_disj
      rfl
    all_goals
      unfold is_nnf at h1
      contradiction
  case and_ phi psi phi_ih psi_ih =>
    unfold dnf_list_of_list_to_formula at phi_ih
    unfold dnf_list_of_list_to_formula at psi_ih

    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    specialize phi_ih h1_left
    specialize psi_ih h1_right

    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [eval]
    simp only [bool_iff_prop_and]
    rewrite [← phi_ih]
    rewrite [← psi_ih]
    simp only [← eval_exists_eq_true_iff_eval_list_disj_eq_true]
    simp only [List.mem_map]
    simp only [mem_all_pairs_alt_alt_iff_eq_union]
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

    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    specialize phi_ih h1_left
    specialize psi_ih h1_right

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
    unfold is_nnf at h1
    contradiction
