import MathlibExtraLean.FunctionUpdateFromListOfPairsITE

import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.IsDNF
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.ListConj
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.MkLits
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.ListDisj
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.GenAllValuations
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.ToDNF

import Mathlib.Tactic


set_option autoImplicit false


namespace Bool_


open Formula_


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
