import Mathlib

/-! Local turn arithmetic excluding two dangerous RR owners on one physical edge. -/

namespace CollisionCore

/-- At a trivalent crystalline vertex the three exterior-turn units sum to four.
If the two cells across one edge both contribute an R-corner (turn 2), the third
cell is straight (turn 0). -/
theorem two_R_force_straight
    (a b c : ℕ) (ha : a = 2) (hb : b = 2) (hsum : a + b + c = 4) : c = 0 := by
  omega

/-- Consequently, in a region with no straight incidence, the two sides of one
physical edge cannot both be RR. -/
theorem not_RR_on_both_sides
    (a b c : ℕ) (hc : 0 < c) (hsum : a + b + c = 4) :
    ¬ (a = 2 ∧ b = 2) := by
  intro hab
  have := two_R_force_straight a b c hab.1 hab.2 hsum
  omega

end CollisionCore
