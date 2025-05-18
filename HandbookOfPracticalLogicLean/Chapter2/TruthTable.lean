import MathlibExtraLean.FunctionUpdateFromListOfPairsITE

import HandbookOfPracticalLogicLean.Chapter2.Semantics


import Mathlib.Tactic


set_option autoImplicit false


open Formula_


def ValuationAsListOfPairs : Type := List (String × Bool)
  deriving Inhabited


def gen_all_valuations_as_list_of_list_of_pairs :
  List String → List (ValuationAsListOfPairs)
| [] => [[]]
| hd :: tl =>
  let prev := gen_all_valuations_as_list_of_list_of_pairs tl

  let left := List.map (fun (l : ValuationAsListOfPairs) => (hd, false) :: l) prev
  let right := List.map (fun (l : ValuationAsListOfPairs) => (hd, true) :: l) prev

  left ++ right


def all_valuations_as_set_of_list_of_pairs
  (atoms : List String) :
  Set (ValuationAsListOfPairs) :=
  { V : ValuationAsListOfPairs | (V.map Prod.fst) = atoms }


example
  (V : ValuationAsListOfPairs)
  (atoms : List String)
  (h1 : (V.map Prod.fst) = atoms) :
  V ∈ gen_all_valuations_as_list_of_list_of_pairs atoms :=
  by
  induction atoms generalizing V
  case nil =>
    cases V
    case nil =>
      unfold gen_all_valuations_as_list_of_list_of_pairs
      simp only [List.mem_singleton]
    case cons V_hd V_tl =>
      simp only [List.map_cons] at h1
      contradiction
  case cons hd tl ih =>
    cases V
    case nil =>
      simp only [List.map_nil] at h1
      contradiction
    case cons V_hd V_tl =>
      simp only [List.map_cons, List.cons.injEq] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold gen_all_valuations_as_list_of_list_of_pairs
      simp only [List.mem_append, List.mem_map]

      cases c1 : V_hd.2
      case false =>
        left
        apply Exists.intro V_tl
        constructor
        · apply ih
          exact h1_right
        · rewrite [← h1_left]
          rewrite [← c1]
          rfl
      case true =>
        right
        apply Exists.intro V_tl
        constructor
        · apply ih
          exact h1_right
        · rewrite [← h1_left]
          rewrite [← c1]
          rfl


example
  (atoms : List String)
  (l : ValuationAsListOfPairs)
  (h1 : l ∈ gen_all_valuations_as_list_of_list_of_pairs atoms) :
  (l.map Prod.fst) = atoms :=
  by
  induction atoms generalizing l
  case nil =>
    cases l
    case nil =>
      simp only [List.map_nil]
    case cons l_hd l_tl =>
      unfold gen_all_valuations_as_list_of_list_of_pairs at h1
      simp only [List.mem_singleton] at h1
      contradiction
  case cons hd tl ih =>
    cases l
    case nil =>
      unfold gen_all_valuations_as_list_of_list_of_pairs at h1
      simp only [List.mem_append, List.mem_map] at h1
      cases h1
      case inl h1 | inr h1 =>
        obtain ⟨V, h1_left, h1_right⟩ := h1
        contradiction
    case cons l_hd l_tl =>
      unfold gen_all_valuations_as_list_of_list_of_pairs at h1
      simp only [List.mem_append, List.mem_map] at h1

      simp only [List.map_cons, List.cons.injEq]
      cases h1
      case inr h1 | inl h1 =>
        obtain ⟨V, h1_left, h1_right⟩ := h1
        injection h1_right
        case _ hd_eq tl_eq =>
          constructor
          · rewrite [← hd_eq]
            simp only
          · rewrite [← tl_eq]
            apply ih
            exact h1_left


-------------------------------------------------------------------------------


/--
  `gen_all_valuations_as_list_of_total_functions init atoms` := A list of all of the functions from strings to booleans that map the strings not in `atoms` to the same values as `init`.
-/
def gen_all_valuations_as_list_of_total_functions
  (init : ValuationAsTotalFunction) :
  List String → List (ValuationAsTotalFunction)
| [] => [init]
| hd :: tl =>
  let left := List.map (fun (V : ValuationAsTotalFunction) => Function.updateITE V hd false) (gen_all_valuations_as_list_of_total_functions init tl)

  let right := List.map (fun (V : ValuationAsTotalFunction) => Function.updateITE V hd true) (gen_all_valuations_as_list_of_total_functions init tl)

  left ++ right


def all_valuations_as_set_of_total_functions
  (init : ValuationAsTotalFunction)
  (atoms : List String) :
  Set ValuationAsTotalFunction :=
  { V : ValuationAsTotalFunction | ∀ (X : String), X ∉ atoms → V X = init X }


example
  (init : ValuationAsTotalFunction)
  (atoms : List String)
  (V : ValuationAsTotalFunction)
  (h1 : V ∈ gen_all_valuations_as_list_of_total_functions init atoms) :
  V ∈ all_valuations_as_set_of_total_functions init atoms :=
  by
  sorry


-------------------------------------------------------------------------------


lemma gen_all_valuations_as_list_of_list_of_pairs_is_complete
  (atom_list : List String)
  (f : String → Bool) :
  Function.toListOfPairs atom_list f ∈ gen_all_valuations_as_list_of_list_of_pairs atom_list :=
  by
  induction atom_list
  case nil =>
    unfold Function.toListOfPairs
    unfold gen_all_valuations_as_list_of_list_of_pairs
    simp only [List.map_nil, List.mem_singleton]
  case cons hd tl ih =>
    unfold Function.toListOfPairs at ih

    unfold Function.toListOfPairs
    unfold gen_all_valuations_as_list_of_list_of_pairs
    simp only [List.map_cons, List.mem_append, List.mem_map, List.cons.injEq, Prod.mk.injEq]
    cases f hd
    case false =>
      left
      apply Exists.intro (List.map (fun x => (x, f x)) tl)
      constructor
      · exact ih
      · constructor
        · constructor
          · exact trivial
          · rfl
        · rfl
    case true =>
      right
      apply Exists.intro (List.map (fun x => (x, f x)) tl)
      constructor
      · exact ih
      · constructor
        · constructor
          · exact trivial
          · rfl
        · rfl


-------------------------------------------------------------------------------


example
  (init : String → Bool)
  (atom_list : List String)
  (V : ValuationAsTotalFunction)
  (X : String)
  (h1 : V ∈ gen_all_valuations_as_list_of_total_functions init atom_list)
  (h2 : X ∉ atom_list) :
  V X = init X :=
  by
  sorry


lemma gen_all_valuations_as_list_of_total_functions_is_complete
  (init : String → Bool)
  (atom_list : List String)
  (V : ValuationAsTotalFunction)
  (h1 : ∀ (X : String), X ∉ atom_list → V X = init X) :
  V ∈ gen_all_valuations_as_list_of_total_functions init atom_list :=
  by
  induction atom_list generalizing V
  case nil =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.mem_singleton]
    funext X
    apply h1
    simp only [List.not_mem_nil]
    intro contra
    exact contra
  case cons hd tl ih =>
    simp only [List.mem_cons, not_or] at h1

    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.mem_append, List.mem_map]
    cases c1 : V hd
    case false =>
      left
      apply Exists.intro (fun (X : String) => if X ∈ tl then V X else init X)
      constructor
      · apply ih
        intro X a2
        split_ifs
        rfl
      · funext X
        unfold Function.updateITE
        split_ifs
        case pos c2 =>
          rewrite [← c1]
          rewrite [c2]
          rfl
        case neg c2 =>
          simp only
          split_ifs
          case pos c3 =>
            rfl
          case neg c3 =>
            rewrite [h1]
            · rfl
            · exact ⟨c2, c3⟩
    case true =>
      right
      apply Exists.intro (fun (X : String) => if X ∈ tl then V X else init X)
      constructor
      · apply ih
        intro X a2
        split_ifs
        rfl
      · funext X
        unfold Function.updateITE
        split_ifs
        case pos c2 =>
          rewrite [← c1]
          rewrite [c2]
          rfl
        case neg c2 =>
          simp only
          split_ifs
          case pos c3 =>
            rfl
          case neg c3 =>
            rewrite [h1]
            · rfl
            · exact ⟨c2, c3⟩


-------------------------------------------------------------------------------


lemma gen_all_valuations_as_list_of_total_functions_length_pos
  (init : String → Bool)
  (atom_list : List String) :
  0 < (gen_all_valuations_as_list_of_total_functions init atom_list).length :=
  by
  induction atom_list
  case nil =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.length_singleton]
    exact Nat.one_pos
  case cons hd tl ih =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.length_append, List.length_map]
    apply Nat.add_pos_left
    exact ih


lemma gen_all_valuations_as_list_of_total_functions_length_cons
  (init : String → Bool)
  (X : String)
  (atom_list : List String) :
  (gen_all_valuations_as_list_of_total_functions init atom_list).length < (gen_all_valuations_as_list_of_total_functions init (X :: atom_list)).length :=
  by
  conv => right; unfold gen_all_valuations_as_list_of_total_functions
  simp only [List.length_append, List.length_map]
  apply Nat.lt_add_of_pos_left
  apply gen_all_valuations_as_list_of_total_functions_length_pos


lemma gen_all_valuations_as_list_of_total_functions_length_eq
  (init_1 init_2 : String → Bool)
  (atom_list : List String) :
  (gen_all_valuations_as_list_of_total_functions init_1 atom_list).length = (gen_all_valuations_as_list_of_total_functions init_2 atom_list).length :=
  by
  induction atom_list
  case nil =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.length_singleton]
  case cons hd tl ih =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.length_append, List.length_map]
    rewrite [ih]
    rfl


-------------------------------------------------------------------------------


def valuation_as_list_of_pairs_to_valuation_as_total_function
  (init : ValuationAsTotalFunction)
  (l : ValuationAsListOfPairs) :
  ValuationAsTotalFunction :=
  Function.updateFromListOfPairsITE init l


def valuation_as_total_function_to_valuation_as_list_of_pairs
  (atom_list : List String)
  (V : ValuationAsTotalFunction) :
  ValuationAsListOfPairs :=
  Function.toListOfPairs atom_list V


-------------------------------------------------------------------------------


example
  (init : ValuationAsTotalFunction)
  (atom_list : List String) :
  (gen_all_valuations_as_list_of_list_of_pairs atom_list).map (valuation_as_list_of_pairs_to_valuation_as_total_function init) = gen_all_valuations_as_list_of_total_functions init atom_list :=
  by
  induction atom_list
  case nil =>
    unfold gen_all_valuations_as_list_of_list_of_pairs
    simp only [List.map_cons, List.map_nil]
    unfold valuation_as_list_of_pairs_to_valuation_as_total_function
    unfold Function.updateFromListOfPairsITE
    unfold gen_all_valuations_as_list_of_total_functions
    rfl
  case cons hd tl ih =>
    unfold valuation_as_list_of_pairs_to_valuation_as_total_function at ih

    unfold gen_all_valuations_as_list_of_list_of_pairs
    simp only [List.map_append, List.map_map]
    unfold valuation_as_list_of_pairs_to_valuation_as_total_function
    unfold gen_all_valuations_as_list_of_total_functions
    simp only
    congr 1
    all_goals
      rewrite [← ih]
      simp only [List.map_map, List.map_inj_left, Function.comp_apply]
      intro l a1
      funext X
      unfold Function.updateITE
      split_ifs
      case pos c1 =>
        unfold Function.updateFromListOfPairsITE
        simp only
        unfold Function.updateITE
        split_ifs
        rfl
      case neg c1 =>
        conv => left; unfold Function.updateFromListOfPairsITE
        simp only
        unfold Function.updateITE
        split_ifs
        rfl


example
  (init : ValuationAsTotalFunction)
  (atom_list : List String)
  (h1 : atom_list.Nodup) :
  (gen_all_valuations_as_list_of_total_functions init atom_list).map (valuation_as_total_function_to_valuation_as_list_of_pairs atom_list) = gen_all_valuations_as_list_of_list_of_pairs atom_list :=
  by
  induction atom_list
  case nil =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.map_cons, List.map_nil]
    unfold valuation_as_total_function_to_valuation_as_list_of_pairs
    unfold Function.toListOfPairs
    simp only [List.map_nil]
    unfold gen_all_valuations_as_list_of_list_of_pairs
    rfl
  case cons hd tl ih =>
    unfold valuation_as_total_function_to_valuation_as_list_of_pairs at ih

    simp only [List.nodup_cons] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.map_append, List.map_map]
    unfold valuation_as_total_function_to_valuation_as_list_of_pairs
    unfold gen_all_valuations_as_list_of_list_of_pairs
    simp only
    congr 1
    all_goals
      rewrite [← ih h1_right]
      simp only [List.map_map, List.map_inj_left, Function.comp_apply]
      intro V a1
      unfold Function.toListOfPairs
      simp only [List.map_cons]
      congr! 1
      · unfold Function.updateITE
        simp only [if_pos]
      · simp only [List.map_inj_left]
        intro X a2
        simp only [Prod.mk.injEq]
        constructor
        · exact trivial
        · unfold Function.updateITE
          split_ifs
          case pos c1 =>
            rewrite [c1] at a2
            contradiction
          case neg c1 =>
            rfl


-------------------------------------------------------------------------------


lemma gen_all_valuations_as_list_of_total_functions_eq_on_atom_list
  (init_1 init_2 : ValuationAsTotalFunction)
  (atom_list : List String)
  (p : ValuationAsTotalFunction × ValuationAsTotalFunction)
  (X : String)
  (h1 : p ∈ List.zip
    (gen_all_valuations_as_list_of_total_functions init_1 atom_list)
    (gen_all_valuations_as_list_of_total_functions init_2 atom_list))
  (h2 : X ∈ atom_list) :
  p.1 X = p.2 X :=
  by
  induction atom_list generalizing p
  case nil =>
    simp only [List.not_mem_nil] at h2
  case cons hd tl ih =>
    simp only [List.mem_cons] at h2

    unfold gen_all_valuations_as_list_of_total_functions at h1
    simp only at h1

    rewrite [List.zip_append] at h1
    · simp only [List.mem_append] at h1

      cases h2
      case inl h2 =>
        cases h1
        case inl h1 | inr h1 =>
          obtain s1 := List.of_mem_zip h1
          obtain ⟨s1_left, s1_right⟩ := s1

          simp only [List.mem_map] at s1_left
          obtain ⟨V_1, ⟨s1_left_left, s1_left_right⟩⟩ := s1_left

          simp only [List.mem_map] at s1_right
          obtain ⟨V_2, ⟨s1_right_left, s1_right_right⟩⟩ := s1_right

          rewrite [← s1_left_right]
          rewrite [← s1_right_right]
          unfold Function.updateITE
          split_ifs
          rfl
      case inr h2 =>
        cases h1
        case inl h1 | inr h1 =>
          simp only [List.zip_map] at h1
          simp only [List.mem_map, Prod.exists, Prod.map_apply] at h1
          obtain ⟨a, b, ⟨h1_left, h1_right⟩⟩ := h1
          rewrite [← h1_right]
          simp only
          unfold Function.updateITE
          split_ifs
          case pos c1 =>
            rfl
          case neg c1 =>
            specialize ih (a, b)
            simp only at ih
            apply ih
            · exact h1_left
            · exact h2
    · simp only [List.length_map]
      apply gen_all_valuations_as_list_of_total_functions_length_eq


lemma mem_zip_gen_all_valuations_as_list_of_total_functions_imp_eval_eq
  (init_1 init_2 : ValuationAsTotalFunction)
  (F : Formula_)
  (p : ValuationAsTotalFunction × ValuationAsTotalFunction)
  (h1 : p ∈ List.zip
    (gen_all_valuations_as_list_of_total_functions init_1 F.atom_list.dedup)
    (gen_all_valuations_as_list_of_total_functions init_2 F.atom_list.dedup)) :
  eval p.1 F = eval p.2 F :=
  by
  apply theorem_2_2
  intro X a1
  apply gen_all_valuations_as_list_of_total_functions_eq_on_atom_list init_1 init_2 F.atom_list.dedup
  · exact h1
  · simp only [List.mem_dedup]
    rewrite [← atom_occurs_in_iff_mem_atom_list]
    exact a1


-------------------------------------------------------------------------------


def find_valuation (pred : ValuationAsListOfPairs → Bool) :
  List String → ValuationAsListOfPairs → Option ValuationAsListOfPairs
| [], v => if pred v then some v else none
| hd :: tl, v =>
  find_valuation pred tl ((hd, false) :: v) <|>
  find_valuation pred tl ((hd, true) :: v)

#eval find_valuation (fun (v : List _) => ("P", true) ∈ v ∧ ("Q", false) ∈ v) ["P", "Q"] []


def find_satisfying_valuation
  (F : Formula_) :
  Option ValuationAsListOfPairs :=
  let pred := fun (v : List (String × Bool)) => eval (valuation_as_list_of_pairs_to_valuation_as_total_function (fun _ => false) v) F

  find_valuation pred F.atom_list.dedup []


def check_tautology
  (F : Formula_) :
  Prop :=
  (find_satisfying_valuation (not_ F)).isNone

instance
  (F : Formula_) :
  Decidable (check_tautology F) :=
  by
  unfold check_tautology
  infer_instance


#eval find_satisfying_valuation (atom_ "P")
#eval find_satisfying_valuation (not_ (atom_ "P"))
#eval find_satisfying_valuation (and_ (atom_ "P") (not_ (atom_ "P")))
#eval find_satisfying_valuation (or_ (atom_ "P") (not_ (atom_ "P")))
#eval find_satisfying_valuation (imp_ (atom_ "P") (atom_ "Q"))

#eval check_tautology (or_ (atom_ "P") (not_ (atom_ "P")))
#eval check_tautology (imp_ (atom_ "P") (atom_ "Q"))


def cartesian_product
  {α : Type} :
  List (List α) → List (List α)
| [] => [[]]
| xs :: xss =>
  let sub_products := cartesian_product xss
  (xs.map (fun val => sub_products.map (fun sub => val :: sub))).flatten

#eval cartesian_product [[0, 1]]
#eval cartesian_product [[0, 1], [0, 1], [0, 1]]


def all_sublists
  {α : Type} :
  List α → List (List α)
  | [] => [[]]
  | (a :: as) =>
      let recval := all_sublists as
      recval.map (a :: .) ++ recval

#eval all_sublists [0, 1, 2]
#eval [0, 1, 2].sublists
#eval [0, 1, 2].sublistsFast
