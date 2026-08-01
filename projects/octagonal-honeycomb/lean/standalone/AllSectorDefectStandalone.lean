import SmallGapReserveStandalone
import FirstSectorDefectStandalone
import SecondSectorDefectStandalone
import ThirdSectorDefectStandalone

set_option linter.unusedVariables false

/-!
# Exhaustive octagonal phase-defect theorem

Every convex normal gap lies in one of the four intervals cut out by the
regular-octagon sector width `pi/4`.  This module combines the four local
estimates into one theorem and retains the stronger `4/25` reserve on gaps
shorter than one sector.
-/

namespace AllSectorDefectStandalone

noncomputable section

open Real
open OctagonBase
open SmallGapReserveStandalone

/-- Residual endpoint phase after reducing a gap modulo one octagonal sector. -/
def residual (alpha : ℝ) : ℝ :=
  if alpha ≤ Real.pi / 4 then alpha
  else if alpha ≤ Real.pi / 2 then alpha - Real.pi / 4
  else if alpha ≤ 3 * Real.pi / 4 then alpha - Real.pi / 2
  else alpha - 3 * Real.pi / 4

/-- Excess of the sector boundary minimum over the affine phase baseline. -/
def phaseDefect (alpha beta : ℝ) : ℝ :=
  sectorMinimum alpha beta -
    (phaseSlope * (alpha / Real.pi) - cap)

/-- Required continuous corner reserve.  It vanishes once the gap reaches
one octagonal sector. -/
def requiredReserve (alpha : ℝ) : ℝ :=
  smallGapReserve * max (1 - 4 * (alpha / Real.pi)) 0

lemma small_boundary_wedge
    (alpha : ℝ) (hsin : Real.sin alpha ≠ 0) :
    sectorMinimum alpha alpha =
      d * Real.sin alpha * (Real.cos alpha + Real.sin alpha) := by
  have htrig := Real.sin_sq_add_cos_sq alpha
  have hd := d_quadratic
  dsimp [sectorMinimum, wedge]
  field_simp [hsin]
  linear_combination
    (-Real.cos alpha - 2 * Real.sin alpha * d) * htrig +
    (-Real.cos alpha * Real.sin alpha ^ 2) * hd

lemma phaseDefect_small_eq
    (alpha : ℝ) (hsin : Real.sin alpha ≠ 0) :
    phaseDefect alpha alpha = smallPhaseDefect (alpha / Real.pi) := by
  have hpi : Real.pi * (alpha / Real.pi) = alpha := by
    field_simp [Real.pi_ne_zero]
  dsimp [phaseDefect, smallPhaseDefect]
  rw [small_boundary_wedge alpha hsin, hpi]
  ring

lemma residual_nonneg
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (haπ : alpha < Real.pi) :
    0 ≤ residual alpha := by
  by_cases h1 : alpha ≤ Real.pi / 4
  · simp [residual, h1, ha0]
  by_cases h2 : alpha ≤ Real.pi / 2
  · simp [residual, h1, h2]
    linarith
  by_cases h3 : alpha ≤ 3 * Real.pi / 4
  · simp [residual, h1, h2, h3]
    linarith
  · simp [residual, h1, h2, h3]
    linarith

lemma residual_le_quarter
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (haπ : alpha < Real.pi) :
    residual alpha ≤ Real.pi / 4 := by
  by_cases h1 : alpha ≤ Real.pi / 4
  · simp [residual, h1]
  by_cases h2 : alpha ≤ Real.pi / 2
  · simp [residual, h1, h2]
    linarith
  by_cases h3 : alpha ≤ 3 * Real.pi / 4
  · simp [residual, h1, h2, h3]
    linarith
  · simp [residual, h1, h2, h3]
    linarith

/-- Every gap in `[0,pi)` has nonnegative octagonal phase defect. -/
theorem all_sector_defect_nonneg
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (haπ : alpha < Real.pi) :
    0 ≤ phaseDefect alpha (residual alpha) := by
  by_cases h1 : alpha ≤ Real.pi / 4
  · have hres : residual alpha = alpha := by simp [residual, h1]
    rw [hres]
    rcases ha0.eq_or_lt with rfl | hapos
    · simpa [phaseDefect, sectorMinimum, wedge] using cap_nonneg
    · have hsin : 0 < Real.sin alpha :=
        Real.sin_pos_of_pos_of_lt_pi hapos haπ
      have hu0 : 0 ≤ alpha / Real.pi := div_nonneg hapos.le Real.pi_pos.le
      have huq : alpha / Real.pi ≤ (1 : ℝ) / 4 := by
        apply (div_le_iff₀ Real.pi_pos).2
        nlinarith
      have hreserve := small_gap_reserve (alpha / Real.pi) hu0 huq
      have hfactor : 0 ≤ 1 - 4 * (alpha / Real.pi) := by nlinarith
      have hleft : 0 ≤ smallGapReserve * (1 - 4 * (alpha / Real.pi)) := by
        exact mul_nonneg (by norm_num [smallGapReserve]) hfactor
      rw [phaseDefect_small_eq alpha hsin.ne']
      linarith
  · by_cases h2 : alpha ≤ Real.pi / 2
    · let beta : ℝ := alpha - Real.pi / 4
      have hb0 : 0 ≤ beta := by dsimp [beta]; linarith
      have hbq : beta ≤ Real.pi / 4 := by dsimp [beta]; linarith
      have h := FirstSectorDefectStandalone.first_sector_defect_nonneg beta hb0 hbq
      have halpha : Real.pi / 4 + beta = alpha := by dsimp [beta]; ring
      have hres : residual alpha = beta := by simp [residual, h1, h2, beta]
      rw [hres]
      simpa [phaseDefect, halpha] using h
    · by_cases h3 : alpha ≤ 3 * Real.pi / 4
      · let beta : ℝ := alpha - Real.pi / 2
        have hb0 : 0 ≤ beta := by dsimp [beta]; linarith
        have hbq : beta ≤ Real.pi / 4 := by dsimp [beta]; linarith
        have h := SecondSectorDefectStandalone.second_sector_defect_nonneg beta hb0 hbq
        have halpha : Real.pi / 2 + beta = alpha := by dsimp [beta]; ring
        have hres : residual alpha = beta := by simp [residual, h1, h2, h3, beta]
        rw [hres]
        simpa [phaseDefect, halpha] using h
      · let beta : ℝ := alpha - 3 * Real.pi / 4
        have hb0 : 0 ≤ beta := by dsimp [beta]; linarith
        have hbq : beta < Real.pi / 4 := by dsimp [beta]; linarith
        have h := ThirdSectorDefectStandalone.third_sector_defect_nonneg beta hb0 hbq
        have halpha : 3 * Real.pi / 4 + beta = alpha := by dsimp [beta]; ring
        have hres : residual alpha = beta := by simp [residual, h1, h2, h3, beta]
        rw [hres]
        simpa [phaseDefect, halpha] using h

/-- Unified reserve theorem: below `pi/4` it gives the exact `4/25` reserve;
from `pi/4` onward it reduces to phase-defect nonnegativity. -/
theorem all_sector_reserve
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (haπ : alpha < Real.pi) :
    requiredReserve alpha ≤ phaseDefect alpha (residual alpha) := by
  by_cases h1 : alpha ≤ Real.pi / 4
  · have hres : residual alpha = alpha := by simp [residual, h1]
    rw [hres]
    rcases ha0.eq_or_lt with rfl | hapos
    · have hcap : smallGapReserve ≤ cap := by
        dsimp [smallGapReserve]
        nlinarith [cap_lower]
      simpa [requiredReserve, phaseDefect, sectorMinimum, wedge] using hcap
    · have hsin : 0 < Real.sin alpha :=
        Real.sin_pos_of_pos_of_lt_pi hapos haπ
      have hu0 : 0 ≤ alpha / Real.pi := div_nonneg hapos.le Real.pi_pos.le
      have huq : alpha / Real.pi ≤ (1 : ℝ) / 4 := by
        apply (div_le_iff₀ Real.pi_pos).2
        nlinarith
      have hreserve := small_gap_reserve (alpha / Real.pi) hu0 huq
      have hfactor : 0 ≤ 1 - 4 * (alpha / Real.pi) := by nlinarith
      rw [phaseDefect_small_eq alpha hsin.ne']
      dsimp [requiredReserve]
      rw [max_eq_left hfactor]
      exact hreserve
  · have hquarter : Real.pi / 4 < alpha := lt_of_not_ge h1
    have hstrict : 1 < 4 * (alpha / Real.pi) := by
      rw [show 4 * (alpha / Real.pi) = (4 * alpha) / Real.pi by ring]
      apply (lt_div_iff₀ Real.pi_pos).2
      nlinarith
    have hfactor : 1 - 4 * (alpha / Real.pi) ≤ 0 := by
      nlinarith
    have hzero : requiredReserve alpha = 0 := by
      simp [requiredReserve, max_eq_right hfactor]
    rw [hzero]
    exact all_sector_defect_nonneg alpha ha0 haπ

end

end AllSectorDefectStandalone
