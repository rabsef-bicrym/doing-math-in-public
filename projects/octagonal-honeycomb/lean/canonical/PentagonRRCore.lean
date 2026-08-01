import Mathlib

/-! A Presburger certificate for the only combinatorial fact needed to choose an RR edge
from a dangerous pentagon. -/

namespace PentagonRRCore

/-- Five 0/1 labels with exactly three `1`s contain adjacent `1`s on the 5-cycle. -/
theorem three_of_five_has_adjacent
    (b0 b1 b2 b3 b4 : ℕ)
    (h0 : b0 ≤ 1) (h1 : b1 ≤ 1) (h2 : b2 ≤ 1) (h3 : b3 ≤ 1) (h4 : b4 ≤ 1)
    (hsum : b0 + b1 + b2 + b3 + b4 = 3) :
    (b0 = 1 ∧ b1 = 1) ∨
    (b1 = 1 ∧ b2 = 1) ∨
    (b2 = 1 ∧ b3 = 1) ∨
    (b3 = 1 ∧ b4 = 1) ∨
    (b4 = 1 ∧ b0 = 1) := by
  omega

/-- Turn-unit formulation: a dangerous pentagon has three right-angle corners
(turn 2) and two H-corners (turn 1), hence total exterior turn eight and an RR side. -/
theorem dangerous_pentagon_has_RR
    (t0 t1 t2 t3 t4 : ℕ)
    (h0 : t0 = 1 ∨ t0 = 2) (h1 : t1 = 1 ∨ t1 = 2)
    (h2 : t2 = 1 ∨ t2 = 2) (h3 : t3 = 1 ∨ t3 = 2)
    (h4 : t4 = 1 ∨ t4 = 2)
    (hsum : t0 + t1 + t2 + t3 + t4 = 8) :
    (t0 = 2 ∧ t1 = 2) ∨
    (t1 = 2 ∧ t2 = 2) ∨
    (t2 = 2 ∧ t3 = 2) ∨
    (t3 = 2 ∧ t4 = 2) ∨
    (t4 = 2 ∧ t0 = 2) := by
  omega

end PentagonRRCore
