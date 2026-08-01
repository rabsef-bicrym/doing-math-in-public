import OctagonalCornerBank

/-!
# Summing the phase-snapping gap inequalities

Angles are normalized by `π`, so the exterior-turn gaps of a convex polygon
sum to `2`.  For each gap the local phase-snapping estimate has the form

  `phaseSlope * gap - cap + defect ≤ tangentAreaContribution`.

This module proves the global tangent-area bound and sums the sharp rational
small-gap reserve

  `(4/25) * (1 - 4 gap)₊ ≤ defect`.

The coefficient `4/25 = 0.16` is deliberately smaller than
`cap = (sqrt 2 - 1)^2`; using `cap` here would be false for very small positive
gaps.  The statements below isolate the exact analytic hypotheses still needed
from the one-gap phase calculation.
-/

namespace PhaseSnappingSum

noncomputable section

open Real
open scoped BigOperators
open PairGapCore
open NoncrystallineDomainReduction
open ContinuousCornerBank
open OctagonalCornerBank

/-- Coefficient of a normalized turn in the affine tangent-area baseline. -/
def phaseSlope : ℝ := 4 * (2 - s)

/-- Uniform reserve supplied by a gap shorter than one octagonal sector. -/
def smallGapReserve : ℝ := (4 : ℝ) / 25

/-- Tangent-area baseline for an `n`-gap fan.  For `4 ≤ n ≤ 8` this is exactly
`Aₙ`; for `n > 8` it is `A₈ - (n-8) cap`. -/
def phaseBase (n : ℕ) : ℝ := A8 - ((n : ℝ) - 8) * cap

lemma phaseSlope_pos : 0 < phaseSlope := by
  dsimp [phaseSlope]
  nlinarith [s_upper]

lemma smallGapReserve_pos : 0 < smallGapReserve := by
  norm_num [smallGapReserve]

lemma smallGapReserve_nonneg : 0 ≤ smallGapReserve :=
  smallGapReserve_pos.le

lemma phase_base_identity (n : ℕ) :
    phaseSlope * 2 - (n : ℝ) * cap = phaseBase n := by
  dsimp [phaseSlope, phaseBase, A8, cap, d]
  nlinarith [s_sq]

/-- Summing the local one-gap tangent-area bounds gives the global
phase-snapping area lower bound. -/
theorem tangent_area_lower
    {ι : Type*} (corners : Finset ι)
    (gap defect contribution : ι → ℝ)
    (hgap : (∑ i ∈ corners, gap i) = 2)
    (hlocal : ∀ i ∈ corners,
      phaseSlope * gap i - cap + defect i ≤ contribution i) :
    phaseBase corners.card + (∑ i ∈ corners, defect i) ≤
      ∑ i ∈ corners, contribution i := by
  have hsum :
      (∑ i ∈ corners, (phaseSlope * gap i - cap + defect i)) ≤
        ∑ i ∈ corners, contribution i := by
    exact Finset.sum_le_sum fun i hi => hlocal i hi
  have hid :
      (∑ i ∈ corners, (phaseSlope * gap i - cap + defect i)) =
        phaseBase corners.card + (∑ i ∈ corners, defect i) := by
    rw [← phase_base_identity corners.card]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp [hgap]
  rw [← hid]
  exact hsum

/-- The correct pointwise small-gap reserve gives a linear mandatory total
reserve for fans with more than eight gaps. -/
theorem mandatory_defect
    {ι : Type*} (corners : Finset ι)
    (gap defect : ι → ℝ)
    (hgap : (∑ i ∈ corners, gap i) = 2)
    (hlocal : ∀ i ∈ corners,
      smallGapReserve * pos (1 - 4 * gap i) ≤ defect i) :
    ((corners.card : ℝ) - 8) * smallGapReserve ≤
      ∑ i ∈ corners, defect i := by
  have hpos :
      (∑ i ∈ corners, (1 - 4 * gap i)) ≤
        ∑ i ∈ corners, pos (1 - 4 * gap i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact le_pos _
  have hscaled :
      smallGapReserve * (∑ i ∈ corners, pos (1 - 4 * gap i)) ≤
        ∑ i ∈ corners, defect i := by
    calc
      smallGapReserve * (∑ i ∈ corners, pos (1 - 4 * gap i)) =
          ∑ i ∈ corners, smallGapReserve * pos (1 - 4 * gap i) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ corners, defect i :=
        Finset.sum_le_sum fun i hi => hlocal i hi
  have hid :
      (∑ i ∈ corners, (1 - 4 * gap i)) =
        (corners.card : ℝ) - 8 := by
    simp only [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp [hgap]
    norm_num
  have hreserve :=
    mul_le_mul_of_nonneg_left hpos smallGapReserve_nonneg
  rw [hid] at hreserve
  have hreserve' :
      ((corners.card : ℝ) - 8) * smallGapReserve ≤
        smallGapReserve * ∑ i ∈ corners, pos (1 - 4 * gap i) := by
    simpa [mul_comm] using hreserve
  exact le_trans hreserve' hscaled

/-- Monotonicity transfers a tangent-area lower bound into the perimeter lower
bound used by the corner bank. -/
theorem perimeter_lower_from_area
    (n : ℕ) (D tangentArea P : ℝ)
    (hbase : 0 ≤ phaseBase n + D)
    (harea : phaseBase n + D ≤ tangentArea)
    (hperimeter : 2 * Real.sqrt tangentArea ≤ P) :
    2 * Real.sqrt (phaseBase n + D) ≤ P := by
  have htangent : 0 ≤ tangentArea := le_trans hbase harea
  have hsqrt : Real.sqrt (phaseBase n + D) ≤ Real.sqrt tangentArea :=
    Real.sqrt_le_sqrt harea
  nlinarith

/-- Combined scalar bridge from the local one-gap inequalities. -/
theorem phase_snapping_bridge
    {ι : Type*} (corners : Finset ι)
    (gap defect contribution : ι → ℝ)
    (tangentArea P : ℝ)
    (hgap : (∑ i ∈ corners, gap i) = 2)
    (hgapArea : ∀ i ∈ corners,
      phaseSlope * gap i - cap + defect i ≤ contribution i)
    (hgapDefect : ∀ i ∈ corners,
      smallGapReserve * pos (1 - 4 * gap i) ≤ defect i)
    (hareaEq : tangentArea = ∑ i ∈ corners, contribution i)
    (hbase : 0 ≤ phaseBase corners.card + ∑ i ∈ corners, defect i)
    (hperimeter : 2 * Real.sqrt tangentArea ≤ P) :
    phaseBase corners.card + (∑ i ∈ corners, defect i) ≤ tangentArea ∧
      ((corners.card : ℝ) - 8) * smallGapReserve ≤
        ∑ i ∈ corners, defect i ∧
      2 * Real.sqrt
          (phaseBase corners.card + ∑ i ∈ corners, defect i) ≤ P := by
  have harea := tangent_area_lower corners gap defect contribution hgap hgapArea
  rw [← hareaEq] at harea
  have hmandatory := mandatory_defect corners gap defect hgap hgapDefect
  have hP := perimeter_lower_from_area corners.card
    (∑ i ∈ corners, defect i) tangentArea P hbase harea hperimeter
  exact ⟨harea, hmandatory, hP⟩

end

end PhaseSnappingSum
