import Mathlib.Data.Matrix.Notation
import Mathlib.Util.Time
import DNF.Theory.ProveFalseFromSAT

set_option maxHeartbeats 400 in
example : True := by
  let l := [(SAT.atom (0:Fin 2)).or (SAT.atom 1), (SAT.atom 0).not, (SAT.atom 1).not]
  have : determineSAT l = false := by
    delta determineSAT List.dnf
    dsimp only
    eq_refl
  trivial

set_option maxHeartbeats 300 in
-- #time
example (P Q : Prop) (h1 : P ∨ Q) (h2 : ¬ P) (h3 : ¬ Q) : False := by
  let l : List (SAT (Fin 2)) :=
    [(SAT.atom 0).or (SAT.atom 1), (SAT.atom 0).not, (SAT.atom 1).not]
  refine proveFalseFromSAT l ?_ ![P, Q] ⟨h1, h2, h3⟩
  delta determineSAT List.dnf
  dsimp only
  eq_refl

set_option maxHeartbeats 2000 in
-- #time
example (p q r : Prop)
    (h : (( (p ∨ (q ∧ r)) ∧ ¬((p ∨ q) ∧ (r ∨ p ∨ r)))
       ∨  (¬(p ∨ (q ∧ r)) ∧  ((p ∨ q) ∧ (r ∨ p ∨ r))))) :
    False := by
  let a : SAT (Fin 3) := (SAT.atom 0).or ((SAT.atom 1).and (SAT.atom 2))
  let b1 : SAT (Fin 3) := (SAT.atom 0).or (SAT.atom 1)
  let b2 : SAT (Fin 3) := (SAT.atom 2).or ((SAT.atom 0).or (SAT.atom 2))
  let b : SAT (Fin 3) := b1.and b2
  let e : SAT (Fin 3) := (a.and b.not).or (a.not.and b)
  let l : List (SAT (Fin 3)) := [e]
  refine proveFalseFromSAT l ?_ ![p, q, r] h
  delta determineSAT List.dnf SAT.dnf
  dsimp only
  eq_refl
