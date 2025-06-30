import HandbookOfPracticalLogicLean.Chapter2.Replace


set_option autoImplicit false


open Formula_


def is_unifier
  (τ : String → Formula_)
  (pairs : List (Formula_ × Formula_)) :
  Prop :=
  ∀ (p : (Formula_ × Formula_)), p ∈ pairs →
    replace_atom_all_rec τ p.fst =
      replace_atom_all_rec τ p.snd


lemma replace_atom_all_rec_compose
  (F : Formula_)
  (σ τ : String → Formula_) :
  replace_atom_all_rec ((replace_atom_all_rec τ) ∘ σ) F =
    replace_atom_all_rec τ (replace_atom_all_rec σ F) :=
  by
  induction F
  case false_ | true_ =>
    simp only [replace_atom_all_rec]
  case atom_ X =>
    simp only [replace_atom_all_rec]
    exact Function.comp_apply
  case not_ phi ih =>
    simp only [replace_atom_all_rec]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [replace_atom_all_rec]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


example
  (σ τ : String → Formula_)
  (pairs : List (Formula_ × Formula_))
  (h1 : is_unifier σ pairs) :
  is_unifier ((replace_atom_all_rec τ) ∘ σ) pairs :=
  by
  unfold is_unifier at h1
  unfold is_unifier
  intro p a1
  simp only [replace_atom_all_rec_compose]
  rewrite [h1 p a1]
  rfl


def pattern_match_aux
  (σ : List (String × Formula_)) :
  Formula_ → Formula_ → Option (List (String × Formula_))
  | false_, false_ => some σ
  | true_, true_ => some σ
  | atom_ X, F =>
    match List.find? (fun (e : String × Formula_) => e.fst = X) σ with
    | none => some ((X, F) :: σ)
    | some e => if e.snd = F then some σ else none
  | not_ phi, not_ phi' => pattern_match_aux σ phi phi'
  | and_ phi psi, and_ phi' psi' =>
    match pattern_match_aux σ phi phi' with
    | none => none
    | some σ' => pattern_match_aux σ' psi psi'
  | or_ phi psi, or_ phi' psi' =>
    match pattern_match_aux σ phi phi' with
    | none => none
    | some σ' => pattern_match_aux σ' psi psi'
  | imp_ phi psi, imp_ phi' psi' =>
    match pattern_match_aux σ phi phi' with
    | none => none
    | some σ' => pattern_match_aux σ' psi psi'
  | iff_ phi psi, iff_ phi' psi' =>
    match pattern_match_aux σ phi phi' with
    | none => none
    | some σ' => pattern_match_aux σ' psi psi'
  | _, _ => none


def pattern_match
  (P Q : Formula_) :
  Option (List (String × Formula_)) :=
  pattern_match_aux [] P Q

#eval pattern_match (and_ (atom_ "P") (atom_ "Q")) (atom_ "R")
#eval pattern_match (atom_ "R") (and_ (atom_ "P") (atom_ "Q"))
#eval pattern_match (and_ (atom_ "R") (atom_ "S")) (and_ (atom_ "P") (or_ (atom_ "Q") (atom_ "R")))
