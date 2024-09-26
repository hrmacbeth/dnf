import Mathlib.Data.Matrix.Notation
import Mathlib.Util.Time
import DNF.Theory.ProveFalseFromSAT

set_option maxHeartbeats 500 in
example (P Q : Prop) (h1 : P ∨ Q) (h2 : ¬ P) (h3 : ¬ Q) : False :=
  let l : List (SAT (Fin 2)) :=
    [(SAT.atom 0).or (SAT.atom 1), (SAT.atom 0).not, (SAT.atom 1).not]; by
  refine proveFalseFromSAT l ?_ ![P, Q] ⟨h1, h2, h3⟩
  eq_refl

example (p q r : Prop)
    (h : (( (p ∨ (q ∧ r)) ∧ ¬((p ∨ q) ∧ (r ∨ p ∨ r)))
       ∨  (¬(p ∨ (q ∧ r)) ∧  ((p ∨ q) ∧ (r ∨ p ∨ r))))) :
    False :=
  let a : SAT (Fin 3) := (SAT.atom 0).or ((SAT.atom 1).and (SAT.atom 2))
  let b1 : SAT (Fin 3) := (SAT.atom 0).or (SAT.atom 1)
  let b2 : SAT (Fin 3) := (SAT.atom 2).or ((SAT.atom 0).or (SAT.atom 2))
  let b : SAT (Fin 3) := b1.and b2
  let e : SAT (Fin 3) := (a.and b.not).or (a.not.and b)
  let l : List (SAT (Fin 3)) := [e]; by
  refine proveFalseFromSAT l ?_ ![p, q, r] h
  delta determineSAT List.dnf SAT.dnf
  dsimp only -- times out without this
  eq_refl
