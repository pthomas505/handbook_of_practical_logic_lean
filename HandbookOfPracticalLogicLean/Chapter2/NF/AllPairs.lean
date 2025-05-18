import MathlibExtraLean.List


set_option autoImplicit false


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


lemma itlist_eq_foldr
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

def all_pairs_v1
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  List (List α) :=
  match l1 with
  | h1 :: t1 =>
    itlist (fun (x : List α) (a : List (List α)) => (f h1 x) :: a)
      l2 (all_pairs_v1 f t1 l2)
  | [] => []


-------------------------------------------------------------------------------


def all_pairs_v2
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  List (List α) :=
  match l1 with
  | [] => []
  | hd :: tl =>
    List.foldr
      (fun (next : List α) (prev : List (List α)) => (f hd next) :: prev)
        (all_pairs_v2 f tl l2)
          l2


example
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  all_pairs_v1 f l1 l2 = all_pairs_v2 f l1 l2 :=
  by
  induction l1
  case nil =>
    unfold all_pairs_v1
    unfold all_pairs_v2
    rfl
  case cons hd tl ih =>
    unfold all_pairs_v1
    unfold all_pairs_v2
    rewrite [itlist_eq_foldr]
    rewrite [ih]
    rfl


#eval all_pairs_v2 List.append [[1]] []
#eval all_pairs_v2 List.append [[1], [2]] []
#eval all_pairs_v2 List.append [[1]] [[4]]
#eval all_pairs_v2 List.append [[1], [2]] [[4]]
#eval all_pairs_v2 List.append [[1], [2]] [[4], [5]]
#eval all_pairs_v2 List.append [[1]] [[4], [5]]
#eval all_pairs_v2 List.append [[1]] [[4], [5], [6]]
#eval all_pairs_v2 List.append [] [[4], [5]]


-- (a + b) * (c + d)
-- a * c + a * d + b * c + b * d


-------------------------------------------------------------------------------


def distrib_one
  {α : Type}
  (f : List α → List α → List α)
  (xs : List α)
  (xss : List (List α)) :
  List (List α) :=
    List.foldr
      (fun (next : List α) (prev : List (List α)) => (f xs next) :: prev) [] xss

#eval distrib_one List.append [0] [[1], [2], [3]]


def all_pairs_v3
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  List (List α) :=
  match l1 with
  | [] => []
  | hd :: tl => distrib_one f hd l2 ++ all_pairs_v3 f tl l2


example
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  all_pairs_v2 f l1 l2 = all_pairs_v3 f l1 l2 :=
  by
  induction l1
  case nil =>
    unfold all_pairs_v2
    unfold all_pairs_v3
    rfl
  case cons l1_hd l1_tl l1_ih =>
    unfold all_pairs_v2
    unfold all_pairs_v3
    unfold distrib_one
    rewrite [l1_ih]

    obtain s1 := List.foldr_cons_append_init (f l1_hd) [] (all_pairs_v3 f l1_tl l2) l2
    simp only [List.nil_append] at s1
    exact s1


-------------------------------------------------------------------------------


def all_pairs_v4
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  List (List α) :=
  match l1 with
  | [] => []
  | hd :: tl => List.map (f hd) l2 ++ all_pairs_v4 f tl l2


example
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  all_pairs_v3 f l1 l2 = all_pairs_v4 f l1 l2 :=
  by
  induction l1
  case nil =>
    unfold all_pairs_v4
    unfold all_pairs_v3
    rfl
  case cons hd tl ih =>
    unfold all_pairs_v4
    unfold all_pairs_v3
    unfold distrib_one
    simp only [List.map_eq_foldr]
    rewrite [ih]
    rfl


-------------------------------------------------------------------------------


lemma all_pairs_v4_nil_right
  {α : Type}
  (f : List α → List α → List α)
  (l : List (List α)) :
  all_pairs_v4 f l [] = [] :=
  by
  induction l
  case nil =>
    unfold all_pairs_v4
    rfl
  case cons hd tl ih =>
    unfold all_pairs_v4
    simp only [List.map_nil, List.nil_append]
    exact ih


lemma all_pairs_v4_singleton_left_cons_right
  {α : Type}
  (f : List α → List α → List α)
  (xs : List α)
  (ys : List α)
  (yss : List (List α)) :
  all_pairs_v4 f [xs] (ys :: yss) = all_pairs_v4 f [xs] [ys] ++ all_pairs_v4 f [xs] yss :=
  by
  simp only [all_pairs_v4]
  simp only [List.map_cons, List.append_nil, List.map_nil, List.singleton_append]


-------------------------------------------------------------------------------


lemma mem_all_pairs_v4_union_imp_eq_union
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List (List α))
  (l : List α)
  (h1 : l ∈ all_pairs_v4 List.union l1 l2) :
  ∃ (xs : List α) (ys : List α), xs ∈ l1 ∧ ys ∈ l2 ∧ xs ∪ ys = l :=
  by
  induction l1
  case nil =>
    unfold all_pairs_v4 at h1
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    unfold all_pairs_v4 at h1
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


lemma eq_union_imp_mem_all_pairs_v4_union
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List (List α))
  (l : List α)
  (h1 : ∃ (xs : List α) (ys : List α), xs ∈ l1 ∧ ys ∈ l2 ∧ xs ∪ ys = l) :
  l ∈ all_pairs_v4 List.union l1 l2 :=
  by
  obtain ⟨xs, ys, xs_mem, ys_mem, eq⟩ := h1
  induction l1
  case nil =>
    simp only [List.not_mem_nil] at xs_mem
  case cons l1_hd l1_tl l1_ih =>
    simp only [List.mem_cons] at xs_mem

    unfold all_pairs_v4
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


lemma mem_all_pairs_v4_union_iff_eq_union
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List (List α))
  (l : List α) :
  l ∈ all_pairs_v4 List.union l1 l2 ↔
    ∃ (xs : List α) (ys : List α), xs ∈ l1 ∧ ys ∈ l2 ∧ xs ∪ ys = l :=
  by
  constructor
  · apply mem_all_pairs_v4_union_imp_eq_union
  · apply eq_union_imp_mem_all_pairs_v4_union
