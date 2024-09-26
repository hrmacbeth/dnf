import Mathlib.Data.Matrix.Notation
import Mathlib.Util.Time
import DNF.Theory.ProveFalseFromSAT

#eval insertAndDedup (0, true) []
#eval insertAndDedup (0, true) [(1, true)]
#eval insertAndDedup (0, true) [(0, false), (1, true)]
#eval insertAndDedup (0, true) [(0, false)]

/-- info: none -/
#guard_msgs in #eval combine ([(0, true)], [(0, false)])

/-- info: [[(1, false), (0, true)]] -/
#guard_msgs in #eval negate [[(0, false)], [(1, true)]]

#eval SAT.dnf <| (SAT.atom 0).or (SAT.atom 1)
#eval SAT.dnf (SAT.atom 0).not
#eval SAT.dnf <| ((SAT.atom 0).or (SAT.atom 1)).and (SAT.atom 0).not
#eval SAT.dnf <| (((SAT.atom 0).or (SAT.atom 1)).and (SAT.atom 0).not).and (SAT.atom 1).not

/-- info: [] -/
#guard_msgs in #eval List.dnf [(SAT.atom 0).or (SAT.atom 1), (SAT.atom 0).not, (SAT.atom 1).not]

/-- info: true -/
#guard_msgs in #eval determineSAT <| [(SAT.atom 0), (SAT.atom 1).not]

/-- info: false -/
#guard_msgs in #eval determineSAT <| [(SAT.atom 0), (SAT.atom 0).not, (SAT.atom 1).not]

/-- info: false -/
#guard_msgs in
#eval determineSAT <| [(SAT.atom 0).or (SAT.atom 1), (SAT.atom 0).not, (SAT.atom 1).not]

#reduce determineSAT [(SAT.atom 0).or (SAT.atom 1), (SAT.atom 0).not, (SAT.atom 1).not]

set_option maxHeartbeats 200 in
example : True :=
  let l := [(SAT.atom (0:Fin 2)).or (SAT.atom 1), (SAT.atom 0).not, (SAT.atom 1).not]
  have : determineSAT l = false := by eq_refl
  trivial

set_option maxHeartbeats 500 in
example (P Q : Prop) (h1 : P ∨ Q) (h2 : ¬ P) (h3 : ¬ Q) : False :=
  let l : List (SAT (Fin 2)) :=
    [(SAT.atom 0).or (SAT.atom 1), (SAT.atom 0).not, (SAT.atom 1).not]; by
  refine proveFalseFromSAT l ?_ ![P, Q] ⟨h1, h2, h3⟩
  eq_refl

-- #time #eval
#time #reduce
  let a : SAT (Fin 3) := (SAT.atom 0).or ((SAT.atom 1).and (SAT.atom 2))
  let b1 : SAT (Fin 3) := (SAT.atom 0).or (SAT.atom 1)
  let b2 : SAT (Fin 3) := ((SAT.atom 2).or (SAT.atom 0)).or (SAT.atom 2)
  let b : SAT (Fin 3) := b1.and b2
  let e : SAT (Fin 3) := (a.and b.not).or (a.not.and b)
  let l : List (SAT (Fin 3)) := [e]
  determineSAT l

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
