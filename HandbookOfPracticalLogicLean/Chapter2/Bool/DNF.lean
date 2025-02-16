import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.Bool.NNF

import Mathlib.Tactic


set_option autoImplicit false


namespace Bool_


open Formula_


inductive is_constant_ind : Formula_ → Prop
| rule_1 :
  is_constant_ind false_

| rule_2 :
  is_constant_ind true_


inductive is_literal_ind : Formula_ → Prop
| rule_1
  (X : String) :
  is_literal_ind (atom_ X)

| rule_2
  (X : String) :
  is_literal_ind (not_ (atom_ X))


inductive is_conj_ind : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_constant_ind phi →
  is_conj_ind psi →
  is_conj_ind (and_ phi psi)

| rule_2
  (phi psi : Formula_) :
  is_literal_ind phi →
  is_conj_ind psi →
  is_conj_ind (and_ phi psi)

| rule_3
  (F : Formula_) :
  is_constant_ind F →
  is_conj_ind F

| rule_4
  (F : Formula_) :
  is_literal_ind F →
  is_conj_ind F


inductive is_dnf_ind : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_conj_ind phi →
  is_dnf_ind psi →
  is_dnf_ind (or_ phi psi)

| rule_2
  (F : Formula_) :
  is_conj_ind F →
  is_dnf_ind F


-------------------------------------------------------------------------------


lemma is_literal_ind_imp_is_literal
  (F : Formula_)
  (h1 : is_literal_ind F) :
  F.is_literal :=
  by
  cases h1
  all_goals
    simp only [is_literal]


lemma is_literal_imp_is_literal_ind
  (F : Formula_)
  (h1 : F.is_literal) :
  is_literal_ind F :=
  by
  cases F
  case atom_ X =>
    apply is_literal_ind.rule_1
  case not_ phi =>
    cases phi
    case atom_ X =>
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_literal] at h1
  all_goals
    simp only [is_literal] at h1


lemma is_literal_ind_iff_is_literal
  (F : Formula_) :
  is_literal_ind F ↔ F.is_literal:=
  by
  constructor
  · intro a1
    exact is_literal_ind_imp_is_literal F a1
  · intro a1
    exact is_literal_imp_is_literal_ind F a1


-------------------------------------------------------------------------------


def Formula_.is_conj_rec_v1 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_conj_rec_v1 ∧ psi.is_conj_rec_v1
  | _ => False


lemma is_conj_rec_v1_imp_is_nnf
  (F : Formula_)
  (h1 : F.is_conj_rec_v1) :
  F.is_nnf :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    simp only [is_nnf]
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      simp only [is_nnf]
    all_goals
      simp only [is_conj_rec_v1] at h1
  case and_ phi psi phi_ih psi_ih =>
    simp only [is_conj_rec_v1] at h1

    simp only [is_nnf]
    tauto
  all_goals
    simp only [is_conj_rec_v1] at h1


-------------------------------------------------------------------------------


def Formula_.is_conj_rec_v2 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ (false_) psi => psi.is_conj_rec_v2
  | and_ (true_) psi => psi.is_conj_rec_v2
  | and_ (atom_ _) psi => psi.is_conj_rec_v2
  | and_ (not_ (atom_ _)) psi => psi.is_conj_rec_v2
  | _ => False


example
  (F : Formula_)
  (h1 : is_conj_rec_v2 F) :
  is_conj_rec_v1 F :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    simp only [is_conj_rec_v1]
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      simp only [is_conj_rec_v1]
    all_goals
      simp only [is_conj_rec_v2] at h1
  case and_ phi psi phi_ih psi_ih =>
    cases phi
    case false_ | true_ | atom_ X =>
      simp only [is_conj_rec_v2] at h1

      simp only [is_conj_rec_v1]
      tauto
    case not_ phi =>
      cases phi
      case atom_ X =>
        simp only [is_conj_rec_v1]
        simp only [is_conj_rec_v2] at h1
        tauto
      all_goals
        simp only [is_conj_rec_v2] at h1
    all_goals
      simp only [is_conj_rec_v2] at h1
  all_goals
    simp only [is_conj_rec_v2] at h1


example
  (F : Formula_)
  (h1 : is_conj_rec_v2 F) :
  is_conj_ind F :=
  by
  induction F
  case false_ =>
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_2
  case atom_ X =>
    apply is_conj_ind.rule_4
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      apply is_conj_ind.rule_4
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_conj_rec_v2] at h1
  case and_ phi psi phi_ih psi_ih =>
    cases phi
    case false_ =>
      simp only [is_conj_rec_v2] at h1
      apply is_conj_ind.rule_1
      · apply is_constant_ind.rule_1
      · apply psi_ih
        exact h1
    case true_ =>
      simp only [is_conj_rec_v2] at h1
      apply is_conj_ind.rule_1
      · apply is_constant_ind.rule_2
      · apply psi_ih
        exact h1
    case atom_ X =>
      simp only [is_conj_rec_v2] at h1
      apply is_conj_ind.rule_2
      · apply is_literal_ind.rule_1
      · apply psi_ih
        exact h1
    case not_ phi =>
      cases phi
      case atom_ X =>
        simp only [is_conj_rec_v2] at h1
        simp only [is_conj_rec_v2] at phi_ih
        apply is_conj_ind.rule_2
        · apply is_literal_ind.rule_2
        · apply psi_ih
          exact h1
      all_goals
        simp only [is_conj_rec_v2] at h1
    all_goals
      simp only [is_conj_rec_v2] at h1
  all_goals
    simp only [is_conj_rec_v2] at h1


example
  (F : Formula_)
  (h1 : is_conj_ind F) :
  is_conj_rec_v2 F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 =>
    cases ih_1
    case rule_1 =>
      simp only [is_conj_rec_v2]
      exact ih_3
    case rule_2 =>
      simp only [is_conj_rec_v2]
      exact ih_3
  case rule_2 phi psi ih_1 ih_2 ih_3 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_conj_rec_v2]
      exact ih_3
    case rule_2 X =>
      simp only [is_conj_rec_v2]
      exact ih_3
  case rule_3 phi ih_1 =>
    cases ih_1
    case rule_1 =>
      simp only [is_conj_rec_v2]
    case rule_2 =>
      simp only [is_conj_rec_v2]
  case rule_4 phi ih_1 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_conj_rec_v2]
    case rule_2 X =>
      simp only [is_conj_rec_v2]


-------------------------------------------------------------------------------


def list_conj :
  List Formula_ → Formula_
  | [] => true_
  | [P] => P
  | hd :: tl => and_ hd (list_conj tl)


def list_disj :
  List Formula_ → Formula_
  | [] => false_
  | [P] => P
  | hd :: tl => or_ hd (list_disj tl)


def gen_all_assignments :
  List String → List (List (String × Bool))
| [] => [[]]
| hd :: tl =>
  let left := List.map (fun (l : List (String × Bool)) => (hd, false) :: l) (gen_all_assignments tl)

  let right := List.map (fun (l : List (String × Bool)) => (hd, true) :: l) (gen_all_assignments tl)

  left ++ right


def gen_valuation :
  List (String × Bool) → Valuation
  | [] => default
  | hd :: tl => Function.updateITE (gen_valuation tl) hd.fst hd.snd


def gen_all_valuations
  (atoms : List String) :
  List Valuation :=
  (gen_all_assignments atoms).map gen_valuation


lemma gen_all_valuations_nil :
  gen_all_valuations [] = [default] :=
  by
  unfold gen_all_valuations
  unfold gen_all_assignments
  unfold List.map
  unfold gen_valuation
  simp only [List.map_nil]


def gen_all_satisfying_valuations
  (F : Formula_) :
  List Valuation :=
  -- let atoms := List.insertionSort (fun (s1 s2 : String) => s1 < s2) F.atom_list.dedup
  -- let atoms := F.atom_list.dedup
  -- (gen_all_valuations atoms).filter (fun (V : Valuation) => satisfies V F)
  (gen_all_valuations F.atom_list.dedup).filter (fun (V : Valuation) => satisfies V F)


lemma gen_all_satisfying_valuations_false_ :
  gen_all_satisfying_valuations false_ = [] :=
  by
  unfold gen_all_satisfying_valuations
  unfold satisfies
  simp only [eval]
  simp only [Bool.false_eq_true, decide_false, List.filter_false]


lemma gen_all_satisfying_valuations_true_ :
  gen_all_satisfying_valuations true_ = [default] :=
  by
  unfold gen_all_satisfying_valuations
  unfold satisfies
  simp only [eval]
  unfold atom_list
  simp only [List.dedup_nil]
  simp only [gen_all_valuations_nil]
  simp only [decide_true, List.filter_true]


def mk_lits
  (atoms : List String)
  (V : Valuation) :
  Formula_ :=
  let f : String → Formula_ := fun (A : String) =>
    if V A = true
    then atom_ A
    else not_ (atom_ A)
  list_conj (atoms.map f)


lemma mk_lits_nil
  (V : Valuation) :
  mk_lits [] V = true_ :=
  by
  unfold mk_lits
  simp only [List.map_nil]
  unfold list_conj
  rfl


def to_dnf_v1
  (F : Formula_) :
  Formula_ :=
  -- let atoms := List.insertionSort (fun (s1 s2 : String) => s1 < s2) F.atom_list.dedup
  -- let atoms := F.atom_list.dedup
  -- list_disj ((gen_all_satisfying_valuations F).map (mk_lits atoms))
  list_disj ((gen_all_satisfying_valuations F).map (mk_lits F.atom_list.dedup))


#eval (to_dnf_v1 (Formula_| ((P \/ (Q /\ R)) /\ (~ P \/ ~ R)))).toString


example :
  to_dnf_v1 false_ = false_ :=
  by
  unfold to_dnf_v1
  simp only [gen_all_satisfying_valuations_false_]
  simp only [List.map_nil]
  unfold list_disj
  rfl


example :
  to_dnf_v1 true_ = true_ :=
  by
  unfold to_dnf_v1
  simp only [gen_all_satisfying_valuations_true_]
  simp only [List.map_cons, List.map_nil]
  unfold atom_list
  simp only [List.dedup_nil]
  simp only [mk_lits_nil]
  unfold list_disj
  rfl


lemma List.dedup_singleton
  {α : Type}
  [DecidableEq α]
  (x : α) :
  [x].dedup = [x] := rfl


example
  (X : String) :
  to_dnf_v1 (atom_ X) = atom_ X :=
  by
  unfold to_dnf_v1
  simp only [gen_all_satisfying_valuations]
  unfold atom_list
  simp only [List.dedup_singleton]
  unfold satisfies
  simp only [eval]
  simp only [gen_all_valuations]
  simp only [gen_all_assignments]
  simp only [List.map_cons, List.map_nil, List.singleton_append]
  simp only [gen_valuation]
  simp only [List.filter]
  simp only [Bool.decide_eq_true]
  simp only [Function.updateITE]
  simp only [if_pos]
  simp only [List.map_cons, List.map_nil]
  simp only [mk_lits]
  simp only [List.map_cons, List.map_nil]
  simp only [Function.updateITE]
  simp only [if_pos]
  unfold list_conj
  unfold list_disj
  rfl


lemma mk_lits_is_conj_ind
  (atoms : List String)
  (V : Valuation) :
  is_conj_ind (mk_lits atoms V) :=
  by
  induction atoms
  case nil =>
    simp only [mk_lits_nil]
    apply is_conj_ind.rule_3
    exact is_constant_ind.rule_2
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [mk_lits]
      simp only [List.map_cons, List.map_nil]
      simp only [list_conj]
      split_ifs
      case pos c1 =>
        apply is_conj_ind.rule_4
        apply is_literal_ind.rule_1
      case neg c1 =>
        apply is_conj_ind.rule_4
        apply is_literal_ind.rule_2
    case cons tl_hd tl_tl =>
      simp only [mk_lits] at ih

      simp only [mk_lits]

      simp only [list_conj]
      apply is_conj_ind.rule_2
      · split_ifs
        case pos c1 =>
          apply is_literal_ind.rule_1
        case neg c1 =>
          apply is_literal_ind.rule_2
      · simp only [List.map_cons] at ih
        apply ih


lemma meh
  (atoms : List String)
  (vs : List Valuation)
  (F : Formula_)
  (h1 : F ∈ (List.map (mk_lits atoms) vs)) :
  is_conj_ind F :=
  by
    simp only [List.mem_map] at h1
    obtain ⟨V, h1⟩ := h1
    obtain ⟨h1_left, h1_right⟩ := h1
    rewrite [← h1_right]
    apply mk_lits_is_conj_ind


lemma blah
  (xs : List Formula_)
  (h1 : ∀ (F : Formula_), F ∈ xs → is_conj_ind F) :
  is_dnf_ind (list_disj xs) :=
  by
  induction xs
  case nil =>
    unfold list_disj
    apply is_dnf_ind.rule_2 false_
    apply is_conj_ind.rule_3 false_
    exact is_constant_ind.rule_1
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold list_disj
      apply is_dnf_ind.rule_2 hd
      apply h1
      simp
    case cons tl_hd tl_tl =>
      unfold list_disj
      apply is_dnf_ind.rule_1
      · apply h1
        simp only [List.mem_cons]
        left
        trivial
      · apply ih
        intro F a1
        apply h1
        simp only [List.mem_cons]
        right
        simp only [List.mem_cons] at a1
        exact a1


example
  (F : Formula_) :
  is_dnf_ind (to_dnf_v1 F) :=
  by
  unfold to_dnf_v1
  apply blah
  intro phi
  apply meh
