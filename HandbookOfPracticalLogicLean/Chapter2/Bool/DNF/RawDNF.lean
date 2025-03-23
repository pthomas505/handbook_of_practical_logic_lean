import HandbookOfPracticalLogicLean.Chapter2.Bool.Formula


set_option autoImplicit false


namespace Bool_


open Formula_


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
