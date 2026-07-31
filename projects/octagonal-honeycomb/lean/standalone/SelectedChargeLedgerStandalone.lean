import NegativeChargeSelectionStandalone
import CollisionDebtGroupingStandalone

set_option linter.unusedSectionVars false

/-!
# Finite net-charge closure with a derived debt partition

The abstract terminal ledger previously assumed an equality partitioning all
negative charge into ordinary and collision debt. Here that equality is derived
from the sign of the cell charges and the selected-edge fibers. Local ordinary
and collision payments plus a globally safe resource bound therefore imply
nonnegative total charge directly.
-/

namespace SelectedChargeLedgerStandalone

noncomputable section

open scoped BigOperators
open NegativeChargeSelectionStandalone
open CollisionDebtGroupingStandalone

variable {Cell Edge : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype Edge] [DecidableEq Edge]
variable {charge : Cell → ℝ}

lemma charge_eq_pos_sub (x : ℝ) : x = pos x - pos (-x) := by
  by_cases hx : 0 ≤ x
  · have hneg : -x ≤ 0 := neg_nonpos.mpr hx
    simp [pos, max_eq_left hx, max_eq_right hneg]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hneg : 0 ≤ -x := neg_nonneg.mpr hx'
    simp [pos, max_eq_right hx', max_eq_left hneg]

lemma sum_charge_identity (charge : Cell → ℝ) :
    (∑ c : Cell, charge c) =
      (∑ c : Cell, pos (charge c)) -
        (∑ c : Cell, pos (-charge c)) := by
  calc
    (∑ c : Cell, charge c) =
        ∑ c : Cell, (pos (charge c) - pos (-charge c)) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact charge_eq_pos_sub (charge c)
    _ = (∑ c : Cell, pos (charge c)) -
        (∑ c : Cell, pos (-charge c)) := by
      rw [Finset.sum_sub_distrib]

/-- Once every ordinary and collision owner receives a local payment and the
combined use is bounded by total positive charge, the finite total charge is
nonnegative. The debt partition is no longer an input hypothesis. -/
theorem finite_charge_nonneg_of_selected_payments
    (S : Selection (Cell := Cell) (Edge := Edge) charge)
    (ordinaryUse collisionUse : Cell → ℝ)
    (hordinary : ∀ c ∈ ordinaryCells S, debt charge c ≤ ordinaryUse c)
    (hcollision : ∀ c ∈ collisionCells S, debt charge c ≤ collisionUse c)
    (huse :
      (∑ c ∈ ordinaryCells S, ordinaryUse c) +
          (∑ c ∈ collisionCells S, collisionUse c) ≤
        ∑ c : Cell, pos (charge c)) :
    0 ≤ ∑ c : Cell, charge c := by
  have hord :
      (∑ c ∈ ordinaryCells S, debt charge c) ≤
        ∑ c ∈ ordinaryCells S, ordinaryUse c := by
    exact Finset.sum_le_sum fun c hc => hordinary c hc
  have hcol :
      (∑ c ∈ collisionCells S, debt charge c) ≤
        ∑ c ∈ collisionCells S, collisionUse c := by
    exact Finset.sum_le_sum fun c hc => hcollision c hc
  have hneg := total_negative_partition S
  rw [sum_charge_identity]
  rw [hneg]
  nlinarith

/-- Edge-grouped version matching the geometric collision argument: one local
inequality pays the combined debt of the two owners of each collision edge. -/
theorem finite_charge_nonneg_of_edge_grouped_payments
    (S : Selection (Cell := Cell) (Edge := Edge) charge)
    (ordinaryUse : Cell → ℝ) (collisionUse : Edge → ℝ)
    (hordinary : ∀ c ∈ ordinaryCells S, debt charge c ≤ ordinaryUse c)
    (hcollision : ∀ e ∈ collisionEdges S,
      collisionDebt S e ≤ collisionUse e)
    (huse :
      (∑ c ∈ ordinaryCells S, ordinaryUse c) +
          (∑ e ∈ collisionEdges S, collisionUse e) ≤
        ∑ c : Cell, pos (charge c)) :
    0 ≤ ∑ c : Cell, charge c := by
  have hord :
      (∑ c ∈ ordinaryCells S, debt charge c) ≤
        ∑ c ∈ ordinaryCells S, ordinaryUse c := by
    exact Finset.sum_le_sum fun c hc => hordinary c hc
  have hcol :
      (∑ e ∈ collisionEdges S, collisionDebt S e) ≤
        ∑ e ∈ collisionEdges S, collisionUse e := by
    exact Finset.sum_le_sum fun e he => hcollision e he
  have hneg := total_negative_partition S
  have hgroup := collision_debt_grouped S
  rw [sum_charge_identity]
  rw [hneg, hgroup]
  nlinarith

end

end SelectedChargeLedgerStandalone
