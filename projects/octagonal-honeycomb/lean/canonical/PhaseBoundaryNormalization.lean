import PhaseSectorAlgebra
import PairGapCore

/-!
# Boundary-phase normalization for the regular octagon

The sector minimization theorem is stated for the scale-free pair numerator.
This module restores the exact support scale of the normalized regular-octagonal
isoperimetrix and identifies its boundary value with the phase-snapping
contribution `d sin α (cos α + sin α)`.
-/

namespace PhaseBoundaryNormalization

noncomputable section

open Real
open PairGapCore
open PhaseSectorAlgebra

/-- Squared support scale of the normalized octagonal isoperimetrix. -/
def supportScaleSq : ℝ := 2 * s * d

/-- Tangent-wedge area reconstructed from its scale-free pair numerator. -/
def sectorWedge (sinGap numerator : ℝ) : ℝ :=
  supportScaleSq * numerator / (2 * sinGap)

/-- Boundary pair numerator for a gap `α` shorter than one octagonal sector. -/
def boundaryPairNumerator (alpha : ℝ) : ℝ :=
  pairNumerator (Real.cos alpha) (-(Real.pi / 8))
    (-(Real.pi / 8) + alpha)

/-- The corresponding geometric boundary contribution. -/
def angularBoundaryContribution (alpha : ℝ) : ℝ :=
  d * Real.sin alpha * (Real.cos alpha + Real.sin alpha)

lemma supportScaleSq_pos : 0 < supportScaleSq := by
  dsimp [supportScaleSq]
  exact mul_pos (mul_pos (by norm_num) s_pos) d_pos

lemma sectorWedge_eq_factor (sinGap numerator : ℝ) :
    sectorWedge sinGap numerator =
      (supportScaleSq / (2 * sinGap)) * numerator := by
  dsimp [sectorWedge]
  ring

lemma s_mul_cos_sub_quarter (alpha : ℝ) :
    s * Real.cos (alpha - Real.pi / 4) =
      Real.cos alpha + Real.sin alpha := by
  rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  dsimp [s]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

lemma s_mul_boundaryPairNumerator (alpha : ℝ) :
    s * boundaryPairNumerator alpha =
      Real.sin alpha ^ 2 * (Real.cos alpha + Real.sin alpha) := by
  dsimp [boundaryPairNumerator]
  rw [pairNumerator_identity]
  have hdiff :
      (-(Real.pi / 8) + alpha) - (-(Real.pi / 8)) = alpha := by ring
  have hsum :
      (-(Real.pi / 8)) + (-(Real.pi / 8) + alpha) =
        alpha - Real.pi / 4 := by ring
  rw [hdiff, hsum]
  have hsinSq : 1 - Real.cos alpha ^ 2 = Real.sin alpha ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  rw [sub_self, zero_add, hsinSq]
  calc
    s * (Real.sin alpha ^ 2 * Real.cos (alpha - Real.pi / 4)) =
        Real.sin alpha ^ 2 *
          (s * Real.cos (alpha - Real.pi / 4)) := by ring
    _ = Real.sin alpha ^ 2 *
        (Real.cos alpha + Real.sin alpha) := by
      rw [s_mul_cos_sub_quarter]

/-- Restoring the support scale turns the boundary pair numerator into the
exact phase-snapping boundary contribution. -/
theorem sectorWedge_boundary
    (alpha : ℝ) (hsin : Real.sin alpha ≠ 0) :
    sectorWedge (Real.sin alpha) (boundaryPairNumerator alpha) =
      angularBoundaryContribution alpha := by
  have hnum := s_mul_boundaryPairNumerator alpha
  calc
    sectorWedge (Real.sin alpha) (boundaryPairNumerator alpha) =
        d * (s * boundaryPairNumerator alpha) / Real.sin alpha := by
      dsimp [sectorWedge, supportScaleSq]
      ring
    _ = d * (Real.sin alpha ^ 2 *
        (Real.cos alpha + Real.sin alpha)) / Real.sin alpha := by rw [hnum]
    _ = angularBoundaryContribution alpha := by
      dsimp [angularBoundaryContribution]
      field_simp [hsin]

/-- Any pair-numerator lower bound by the boundary phase immediately becomes
the corresponding geometric tangent-wedge lower bound. -/
theorem angularBoundaryContribution_le_sectorWedge
    (alpha numerator : ℝ)
    (hsin : 0 < Real.sin alpha)
    (hpair : boundaryPairNumerator alpha ≤ numerator) :
    angularBoundaryContribution alpha ≤
      sectorWedge (Real.sin alpha) numerator := by
  have hfactor : 0 ≤ supportScaleSq / (2 * Real.sin alpha) := by
    exact div_nonneg supportScaleSq_pos.le
      (mul_nonneg (by norm_num) hsin.le)
  have hmul := mul_le_mul_of_nonneg_left hpair hfactor
  rw [← sectorWedge_boundary alpha hsin.ne']
  rw [sectorWedge_eq_factor, sectorWedge_eq_factor]
  exact hmul

end

end PhaseBoundaryNormalization
