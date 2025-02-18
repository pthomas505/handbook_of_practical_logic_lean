import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.Bool.Atom
import HandbookOfPracticalLogicLean.Chapter2.Bool.Bool

import Mathlib.Tactic


set_option autoImplicit false


def Function.updateZipListITE
  {α β : Type}
  [DecidableEq α]
  (f : α → β) :
  List (α × β) → (α → β)
  | [] => f
  | hd :: tl => Function.updateITE (Function.updateZipListITE f tl) hd.fst hd.snd


def Function.updateZipListITE_foldl
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (l : List (α × β)) :
  α → β :=
  List.foldl (fun (prev : α → β) (next : α × β) => Function.updateITE prev next.fst next.snd) f l


def Function.updateZipListITE_foldr
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (l : List (α × β)) :
  α → β :=
  List.foldr (fun (next : α × β) (prev : α → β) => Function.updateITE prev next.fst next.snd) f l


#eval Function.updateZipListITE (fun _ => 0) [(2, 8), (1, 2), (1, 5), (2, 3)] 3

#eval Function.updateZipListITE_foldr (fun _ => 0) [(2, 8), (1, 2), (1, 5), (2, 3)] 3


example
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (l : List (α × β)) :
  Function.updateZipListITE f l = Function.updateZipListITE_foldr f l :=
  by
  induction l
  case nil =>
    unfold Function.updateZipListITE
    unfold Function.updateZipListITE_foldr
    simp only [List.foldr_nil]
  case cons hd tl ih =>
    unfold Function.updateZipListITE_foldr at ih

    unfold Function.updateZipListITE
    unfold Function.updateZipListITE_foldr
    simp only [List.foldr_cons]
    rewrite [ih]
    rfl
