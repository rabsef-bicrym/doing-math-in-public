import NegativeChargeSelectionStandalone

set_option linter.unusedSectionVars false

/-!
# Grouping collision-owner debt by physical edge

Collision cells are exactly the negative cells whose selected physical edge has
two selected owners. Distinct edge fibers are disjoint, so their debts may be
summed either ownerwise or edgewise. This is the bridge needed to apply one
local two-owner collision inequality per physical collision edge.
-/

namespace CollisionDebtGroupingStandalone

noncomputable section

open scoped BigOperators
open NegativeChargeSelectionStandalone

variable {Cell Edge : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype Edge] [DecidableEq Edge]
variable {charge : Cell → ℝ}
variable (S : Selection (Cell := Cell) (Edge := Edge) charge)

/-- Combined debt of the two selected owners of a collision edge. -/
def collisionDebt (e : Edge) : ℝ :=
  ∑ c ∈ fiber S e, debt charge c

/-- Collision debt grouped by cells equals collision debt grouped by physical
edges. -/
theorem collision_debt_grouped :
    (∑ c ∈ collisionCells S, debt charge c) =
      ∑ e ∈ collisionEdges S, collisionDebt S e := by
  classical
  symm
  calc
    (∑ e ∈ collisionEdges S, collisionDebt S e) =
        ∑ e ∈ collisionEdges S,
          ∑ c ∈ negativeCells charge,
            if S.edge c = e then debt charge c else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      dsimp [collisionDebt, fiber]
      rw [Finset.sum_filter]
    _ = ∑ c ∈ negativeCells charge,
          ∑ e ∈ collisionEdges S,
            if S.edge c = e then debt charge c else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c ∈ negativeCells charge,
          if fiberCount S (S.edge c) = 2 then debt charge c else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hcol : fiberCount S (S.edge c) = 2
      · rw [if_pos hcol]
        have hedge : S.edge c ∈ collisionEdges S :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcol⟩
        calc
          (∑ e ∈ collisionEdges S,
              if S.edge c = e then debt charge c else 0) =
              (if S.edge c = S.edge c then debt charge c else 0) := by
            apply Finset.sum_eq_single (S.edge c)
            · intro e he hne
              have hneq : S.edge c ≠ e := Ne.symm hne
              simp [hneq]
            · intro hnot
              exact (hnot hedge).elim
          _ = debt charge c := by simp
      · rw [if_neg hcol]
        apply Finset.sum_eq_zero
        intro e he
        have hecol : fiberCount S e = 2 := (Finset.mem_filter.mp he).2
        have hneq : S.edge c ≠ e := by
          intro hEq
          apply hcol
          rw [hEq]
          exact hecol
        simp [hneq]
    _ = ∑ c ∈ collisionCells S, debt charge c := by
      dsimp [collisionCells]
      rw [Finset.sum_filter]

end

end CollisionDebtGroupingStandalone
