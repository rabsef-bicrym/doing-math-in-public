import PhaseGapBridgeStandalone

/-!
# Summing the geometric gap package around one convex cell

This module packages a finite cyclic normal fan after each support direction has
been reduced to an octagonal phase.  The only geometric input is the elementary
no-wrap/wrap representation of each consecutive phase pair.  The local gap
bridge then sums to the complete tangent-area lower bound and the mandatory
small-corner reserve.
-/

namespace ReducedFanBridgeStandalone

noncomputable section

open Real
open scoped BigOperators
open OctagonBase
open AllSectorDefectStandalone
open PhaseGapBridgeStandalone
open SmallGapReserveStandalone

/-- Affine tangent-area baseline for an `n`-gap fan. -/
def phaseBase (n : ℕ) : ℝ :=
  phaseSlope * 2 - (n : ℝ) * cap

/-- Reduced-phase data extracted from one cyclic normal fan. -/
structure FanData (n : ℕ) where
  gap : Fin n → ℝ
  leftPhase : Fin n → ℝ
  rightPhase : Fin n → ℝ
  tangentArea : ℝ
  gapPos : ∀ i, 0 < gap i
  gapLtPi : ∀ i, gap i < Real.pi
  gapSum : (∑ i, gap i) = 2 * Real.pi
  representation : ∀ i,
    (rightPhase i = leftPhase i + residual (gap i) ∧
      -(Real.pi / 8) ≤ leftPhase i ∧
      leftPhase i + residual (gap i) ≤ Real.pi / 8) ∨
    (rightPhase i = leftPhase i + residual (gap i) - Real.pi / 4 ∧
      Real.pi / 8 - residual (gap i) ≤ leftPhase i ∧
      leftPhase i ≤ Real.pi / 8)
  areaEq : tangentArea =
    ∑ i, phaseWedge (gap i) (leftPhase i) (rightPhase i)

/-- Normalized exterior turns sum to two. -/
lemma normalized_gap_sum {n : ℕ} (F : FanData n) :
    (∑ i, F.gap i / Real.pi) = 2 := by
  calc
    (∑ i, F.gap i / Real.pi) = (∑ i, F.gap i) / Real.pi := by
      rw [Finset.sum_div]
    _ = (2 * Real.pi) / Real.pi := by rw [F.gapSum]
    _ = 2 := by field_simp [Real.pi_ne_zero]

/-- The local package for one actual gap of the fan. -/
lemma local_package {n : ℕ} (F : FanData n) (i : Fin n) :
    phaseSlope * (F.gap i / Real.pi) - cap + actualDefect (F.gap i) ≤
        phaseWedge (F.gap i) (F.leftPhase i) (F.rightPhase i) ∧
      requiredReserve (F.gap i) ≤ actualDefect (F.gap i) := by
  exact reduced_gap_package (F.gap i) (F.leftPhase i) (F.rightPhase i)
    (F.gapPos i) (F.gapLtPi i) (F.representation i)

/-- Every phase defect in an actual fan is nonnegative. -/
lemma defect_nonneg {n : ℕ} (F : FanData n) (i : Fin n) :
    0 ≤ actualDefect (F.gap i) := by
  exact all_sector_defect_nonneg (F.gap i) (F.gapPos i).le (F.gapLtPi i)

/-- Summing the local tangent-wedge estimates gives the cell-level area bound. -/
theorem tangent_area_lower {n : ℕ} (F : FanData n) :
    phaseBase n + (∑ i, actualDefect (F.gap i)) ≤ F.tangentArea := by
  have hsum :
      (∑ i, (phaseSlope * (F.gap i / Real.pi) - cap +
        actualDefect (F.gap i))) ≤
        ∑ i, phaseWedge (F.gap i) (F.leftPhase i) (F.rightPhase i) := by
    exact Finset.sum_le_sum fun i hi => (local_package F i).1
  have hnorm := normalized_gap_sum F
  have hid :
      (∑ i, (phaseSlope * (F.gap i / Real.pi) - cap +
        actualDefect (F.gap i))) =
        phaseBase n + (∑ i, actualDefect (F.gap i)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp [phaseBase, hnorm]
  rw [hid] at hsum
  rw [F.areaEq]
  exact hsum

/-- Total required reserve is funded by total actual phase defect. -/
theorem reserve_sum_le_defect_sum {n : ℕ} (F : FanData n) :
    (∑ i, requiredReserve (F.gap i)) ≤
      ∑ i, actualDefect (F.gap i) := by
  exact Finset.sum_le_sum fun i hi => (local_package F i).2

/-- Fans with more than eight corners carry a mandatory linear defect reserve. -/
theorem mandatory_defect {n : ℕ} (F : FanData n) :
    ((n : ℝ) - 8) * smallGapReserve ≤
      ∑ i, actualDefect (F.gap i) := by
  have hnorm := normalized_gap_sum F
  have hpoint :
      (∑ i, (1 - 4 * (F.gap i / Real.pi))) ≤
        ∑ i, max (1 - 4 * (F.gap i / Real.pi)) 0 := by
    exact Finset.sum_le_sum fun i hi => le_max_left _ _
  have hid :
      (∑ i, (1 - 4 * (F.gap i / Real.pi))) = (n : ℝ) - 8 := by
    simp only [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp [hnorm]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hpoint
    (by norm_num [smallGapReserve] : 0 ≤ smallGapReserve)
  rw [hid] at hscaled
  have hreserve :
      smallGapReserve *
          (∑ i, max (1 - 4 * (F.gap i / Real.pi)) 0) ≤
        ∑ i, actualDefect (F.gap i) := by
    calc
      smallGapReserve *
          (∑ i, max (1 - 4 * (F.gap i / Real.pi)) 0) =
        ∑ i, requiredReserve (F.gap i) := by
          rw [Finset.mul_sum]
          rfl
      _ ≤ ∑ i, actualDefect (F.gap i) := reserve_sum_le_defect_sum F
  have hscaled' :
      ((n : ℝ) - 8) * smallGapReserve ≤
        smallGapReserve *
          (∑ i, max (1 - 4 * (F.gap i / Real.pi)) 0) := by
    simpa [mul_comm] using hscaled
  exact le_trans hscaled' hreserve

end

end ReducedFanBridgeStandalone
