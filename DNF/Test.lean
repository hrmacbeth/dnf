/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import DNF.Tactic
import Mathlib.Util.Time

variable (P Q R S : Prop)

#time
example (h1 : P ∧ ¬ P) : False := by prove_false_from_sat

#time
example (h1 : P ∨ Q) (h2 : ¬ P) (h3 : ¬ Q) : False := by prove_false_from_sat

#time
example (h : P ∧ Q) (h' : ¬ (P ∨ Q)) : False := by prove_false_from_sat

#time
example
    (h : (( (P ∨ (Q ∧ R)) ∧ ¬((P ∨ Q) ∧ (R ∨ P ∨ R)))
       ∨  (¬(P ∨ (Q ∧ R)) ∧  ((P ∨ Q) ∧ (R ∨ P ∨ R))))) :
    False := by
  prove_false_from_sat

#time
example (h1 : (P ∧ Q ∨ (R ∧ (P ∨ (S ∧ Q ∨ P))))) (h2 : ¬(P ∧ Q) ∧ (¬R ∨ ¬P ∧ (¬S ∨ ¬Q) ∧ ¬P)) :
    False := by
  prove_false_from_sat

#time
example (h : P ∧ Q) : P ∨ Q := by tauto2

#time
example (h1 : ¬ P ∨ Q) (h2 : ¬ P ∨ R) (h3 : P) : Q ∧ R := by tauto2

#time
example : ¬(P ∧ ¬ P) := by tauto2

#time
example (h1 : P ∨ Q) (h2 : ¬ Q ∨ P) : P := by tauto2

#time
example (h : ¬(P ∨ Q)) : (¬P ∧ ¬Q) := by tauto2
