import HandbookOfPracticalLogicLean.Chapter2.DNF.IsDNF_2

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


inductive is_disj_ind_v2 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_disj_ind_v2 phi →
  is_disj_ind_v2 psi →
  is_disj_ind_v2 (or_ phi psi)

| rule_2
  (F : Formula_) :
  is_constant_ind_v2 F →
  is_disj_ind_v2 F

| rule_3
  (F : Formula_) :
  is_literal_ind_v2 F →
  is_disj_ind_v2 F


inductive is_cnf_ind_v2 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_cnf_ind_v2 phi →
  is_cnf_ind_v2 psi →
  is_cnf_ind_v2 (and_ phi psi)

| rule_2
  (F : Formula_) :
  is_disj_ind_v2 F →
  is_cnf_ind_v2 F
