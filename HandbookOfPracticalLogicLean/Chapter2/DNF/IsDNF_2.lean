import HandbookOfPracticalLogicLean.Chapter2.NNF


set_option autoImplicit false


open Formula_


inductive is_constant_ind_v2 : Formula_ → Prop
| rule_1 :
  is_constant_ind_v2 false_

| rule_2 :
  is_constant_ind_v2 true_


inductive is_literal_ind_v2 : Formula_ → Prop
| rule_1
  (X : String) :
  is_literal_ind_v2 (atom_ X)

| rule_2
  (X : String) :
  is_literal_ind_v2 (not_ (atom_ X))


inductive is_conj_ind_v2 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_conj_ind_v2 phi →
  is_conj_ind_v2 psi →
  is_conj_ind_v2 (and_ phi psi)

| rule_2
  (F : Formula_) :
  is_constant_ind_v2 F →
  is_conj_ind_v2 F

| rule_3
  (F : Formula_) :
  is_literal_ind_v2 F →
  is_conj_ind_v2 F


inductive is_dnf_ind_v2 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_dnf_ind_v2 phi →
  is_dnf_ind_v2 psi →
  is_dnf_ind_v2 (or_ phi psi)

| rule_2
  (F : Formula_) :
  is_conj_ind_v2 F →
  is_dnf_ind_v2 F
