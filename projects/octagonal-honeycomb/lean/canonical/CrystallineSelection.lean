import DischargeCounting

/-!
# Crystalline turn budget and selected-edge geometry

This module isolates the finite combinatorics behind the statement that a cell
can meet at most eight selected edges.  Angles are measured in units of 45
degrees.  At a trivalent vertex the three exterior-turn units sum to four; around
a convex crystalline cell the positive exterior turns sum to eight.
-/

namespace CrystallineSelection

noncomputable section

open scoped BigOperators

variable {Cell Edge : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype Edge] [DecidableEq Edge]

/-- A directed side incidence: a physical edge together with one of its two
incident-cell sides. -/
abbrev SideIncidence (cell : Edge → Bool → Cell) (c : Cell) :=
  {p : Edge × Bool // cell p.1 p.2 = c}

/-- The opposite side of a physical edge. -/
def opposite (b : Bool) : Bool := !b

@[simp] lemma opposite_false : opposite false = true := rfl
@[simp] lemma opposite_true : opposite true = false := rfl

lemma opposite_ne_self (b : Bool) : opposite b ≠ b := by
  cases b <;> decide

/-- Abstract edge-to-edge, trivalent crystalline cellulation data.  `turnStart`
and `turnEnd` are the exterior-turn units at the two endpoints of an oriented
side incidence.  The third incident cell at each endpoint has the recorded
positive turn. -/
structure CoreData (Cell Edge : Type*) [Fintype Cell] [DecidableEq Cell]
    [Fintype Edge] [DecidableEq Edge] where
  cell : Edge → Bool → Cell
  turnStart : Edge → Bool → ℕ
  turnEnd : Edge → Bool → ℕ
  thirdStart : Edge → ℕ
  thirdEnd : Edge → ℕ
  turnStart_pos : ∀ e b, 0 < turnStart e b
  turnEnd_pos : ∀ e b, 0 < turnEnd e b
  thirdStart_pos : ∀ e, 0 < thirdStart e
  thirdEnd_pos : ∀ e, 0 < thirdEnd e
  start_vertex_sum : ∀ e,
    turnStart e false + turnStart e true + thirdStart e = 4
  end_vertex_sum : ∀ e,
    turnEnd e false + turnEnd e true + thirdEnd e = 4
  cell_turn_sum : ∀ c,
    (∑ p : SideIncidence cell c, turnEnd p.1.1 p.1.2) = 8

variable (D : CoreData Cell Edge)

/-- Positive crystalline turns summing to eight imply at most eight genuine
sides, even without naming the eight directions. -/
theorem side_count_le_eight (c : Cell) :
    Fintype.card (SideIncidence D.cell c) ≤ 8 := by
  calc
    Fintype.card (SideIncidence D.cell c) =
        ∑ _p : SideIncidence D.cell c, 1 := by simp
    _ ≤ ∑ p : SideIncidence D.cell c, D.turnEnd p.1.1 p.1.2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact D.turnEnd_pos p.1.1 p.1.2
    _ = 8 := D.cell_turn_sum c

/-- At a trivalent crystalline vertex, if one incident cell has a right-angle
corner (turn two), then each of the other two cells has an H-corner (turn one).
Applied at both endpoints, an RR side is HH on its opposite side. -/
theorem rr_forces_opposite_hh {e : Edge} {b : Bool}
    (hstart : D.turnStart e b = 2)
    (hend : D.turnEnd e b = 2) :
    D.turnStart e (opposite b) = 1 ∧
      D.turnEnd e (opposite b) = 1 := by
  cases b with
  | false =>
      constructor
      · have hsum := D.start_vertex_sum e
        have hop := D.turnStart_pos e true
        have hthird := D.thirdStart_pos e
        simp at hstart ⊢
        omega
      · have hsum := D.end_vertex_sum e
        have hop := D.turnEnd_pos e true
        have hthird := D.thirdEnd_pos e
        simp at hend ⊢
        omega
  | true =>
      constructor
      · have hsum := D.start_vertex_sum e
        have hop := D.turnStart_pos e false
        have hthird := D.thirdStart_pos e
        simp at hstart ⊢
        omega
      · have hsum := D.end_vertex_sum e
        have hop := D.turnEnd_pos e false
        have hthird := D.thirdEnd_pos e
        simp at hend ⊢
        omega

end

end CrystallineSelection
