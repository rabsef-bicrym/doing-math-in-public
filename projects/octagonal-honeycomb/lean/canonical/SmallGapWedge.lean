import PhaseSectorAlgebra
import SmallGapReserve
import HHEdgeAlgebra

/-!
# Geometric one-gap bridge inside an octagonal support sector

For a support phase `t` and a gap `α ≤ π/4`, both support directions either
remain in one octagonal sector or cross exactly one sector boundary.  The
sector-minimization theorem reduces both cases to the same boundary wedge.
This module proves that the boundary wedge is exactly

  `d * sin α * (cos α + sin α)`,

and hence supplies the local phase-defect inequality used by
`PhaseSnappingSum`.

The scale `R` is kept abstract with the two octagonal normalization identities
`R cos(π/8)=1` and `R sin(π/8)=d`.  A later geometric wrapper instantiates
`R` with the circumradius of the normalized regular octagon.
-/

namespace SmallGapWedge

noncomputable section

open Real
open PairGapCore
open OctagonalCornerBank
open PhaseSnappingSum
open CollisionCornerCredit
open PhaseSectorAlgebra

/-- Area contribution of one tangent-fan gap with support values `h,k`. -/
def wedge (alpha h k : ℝ) : ℝ :=
  h * k / Real.sin alpha -
    (h ^ 2 + k ^ 2) * Real.cos alpha / (2 * Real.sin alpha)

/-- Wedge contribution when the octagonal support function in one sector is
`R cos phase`. -/
def phaseWedge (R alpha x y : ℝ) : ℝ :=
  wedge alpha (R * Real.cos x) (R * Real.cos y)

lemma phaseWedge_eq_pair
    (R alpha x y : ℝ) (hsin : Real.sin alpha ≠ 0) :
    phaseWedge R alpha x y =
      (R ^ 2 / (2 * Real.sin alpha)) *
        pairNumerator (Real.cos alpha) x y := by
  dsimp [phaseWedge, wedge, pairNumerator]
  field_simp [hsin]
  ring

lemma boundary_support_left
    (R : ℝ) (hRc : R * Real.cos (Real.pi / 8) = 1) :
    R * Real.cos (-(Real.pi / 8)) = 1 := by
  rw [Real.cos_neg]
  exact hRc

lemma boundary_support_right
    (R alpha : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d) :
    R * Real.cos (-(Real.pi / 8) + alpha) =
      Real.cos alpha + d * Real.sin alpha := by
  have hangle : -(Real.pi / 8) + alpha = alpha - Real.pi / 8 := by ring
  rw [hangle, Real.cos_sub]
  calc
    R * (Real.cos alpha * Real.cos (Real.pi / 8) +
        Real.sin alpha * Real.sin (Real.pi / 8)) =
      Real.cos alpha * (R * Real.cos (Real.pi / 8)) +
        Real.sin alpha * (R * Real.sin (Real.pi / 8)) := by ring
    _ = Real.cos alpha + d * Real.sin alpha := by rw [hRc, hRs]; ring

lemma boundary_support_right_wrap
    (R alpha : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d) :
    R * Real.cos (alpha - Real.pi / 8) =
      Real.cos alpha + d * Real.sin alpha := by
  rw [Real.cos_sub]
  calc
    R * (Real.cos alpha * Real.cos (Real.pi / 8) +
        Real.sin alpha * Real.sin (Real.pi / 8)) =
      Real.cos alpha * (R * Real.cos (Real.pi / 8)) +
        Real.sin alpha * (R * Real.sin (Real.pi / 8)) := by ring
    _ = Real.cos alpha + d * Real.sin alpha := by rw [hRc, hRs]; ring

lemma boundary_wedge_identity
    (alpha : ℝ) (hsin : Real.sin alpha ≠ 0) :
    wedge alpha 1 (Real.cos alpha + d * Real.sin alpha) =
      d * Real.sin alpha * (Real.cos alpha + Real.sin alpha) := by
  have htrig := Real.sin_sq_add_cos_sq alpha
  have hd := HHEdgeAlgebra.d_quadratic
  dsimp [wedge]
  field_simp [hsin]
  ring_nf at htrig hd ⊢
  nlinarith

lemma noWrap_boundary_value
    (R alpha : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d)
    (hsin : Real.sin alpha ≠ 0) :
    phaseWedge R alpha (-(Real.pi / 8))
        (-(Real.pi / 8) + alpha) =
      d * Real.sin alpha * (Real.cos alpha + Real.sin alpha) := by
  dsimp [phaseWedge]
  rw [boundary_support_left R hRc,
    boundary_support_right R alpha hRc hRs]
  exact boundary_wedge_identity alpha hsin

lemma wrap_boundary_value
    (R alpha : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d)
    (hsin : Real.sin alpha ≠ 0) :
    phaseWedge R alpha (Real.pi / 8)
        (alpha - Real.pi / 8) =
      d * Real.sin alpha * (Real.cos alpha + Real.sin alpha) := by
  dsimp [phaseWedge]
  rw [hRc, boundary_support_right_wrap R alpha hRc hRs]
  exact boundary_wedge_identity alpha hsin

lemma phase_factor_nonneg
    (R alpha : ℝ) (hsin : 0 < Real.sin alpha) :
    0 ≤ R ^ 2 / (2 * Real.sin alpha) := by positivity

/-- One-sector, no-wrap phase minimization at wedge level. -/
theorem noWrap_wedge_min
    (R alpha t : ℝ)
    (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ Real.pi / 4)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + alpha ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    phaseWedge R alpha (-(Real.pi / 8))
        (-(Real.pi / 8) + alpha) ≤
      phaseWedge R alpha t (t + alpha) := by
  have hpair := noWrap_min alpha alpha t halpha0 halpha htL htR
  have hfactor := phase_factor_nonneg R alpha hsin
  have hmul := mul_le_mul_of_nonneg_left hpair hfactor
  rw [phaseWedge_eq_pair R alpha (-(Real.pi / 8))
      (-(Real.pi / 8) + alpha) hsin.ne',
    phaseWedge_eq_pair R alpha t (t + alpha) hsin.ne']
  exact hmul

/-- One-sector, one-boundary-wrap phase minimization at wedge level. -/
theorem wrap_wedge_min
    (R alpha t : ℝ)
    (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ Real.pi / 4)
    (htL : Real.pi / 8 - alpha ≤ t)
    (htR : t ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    phaseWedge R alpha (Real.pi / 8)
        (alpha - Real.pi / 8) ≤
      phaseWedge R alpha t (t + alpha - Real.pi / 4) := by
  have hpair := wrap_min alpha alpha t halpha0 halpha htL htR
  have hfactor := phase_factor_nonneg R alpha hsin
  have hmul := mul_le_mul_of_nonneg_left hpair hfactor
  rw [phaseWedge_eq_pair R alpha (Real.pi / 8)
      (alpha - Real.pi / 8) hsin.ne',
    phaseWedge_eq_pair R alpha t (t + alpha - Real.pi / 4) hsin.ne']
  exact hmul

lemma phase_defect_identity
    (alpha : ℝ) :
    phaseSlope * (alpha / Real.pi) - cap +
        smallPhaseDefect (alpha / Real.pi) =
      d * Real.sin alpha * (Real.cos alpha + Real.sin alpha) := by
  have hpi : Real.pi * (alpha / Real.pi) = alpha := by
    field_simp [Real.pi_ne_zero]
  dsimp [smallPhaseDefect, phaseSlope]
  rw [hpi]
  ring

/-- Complete local one-gap estimate in the no-wrap case. -/
theorem noWrap_phase_gap_lower
    (R alpha t : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d)
    (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ Real.pi / 4)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + alpha ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    phaseSlope * (alpha / Real.pi) - cap +
        smallPhaseDefect (alpha / Real.pi) ≤
      phaseWedge R alpha t (t + alpha) := by
  rw [phase_defect_identity]
  rw [← noWrap_boundary_value R alpha hRc hRs hsin.ne']
  exact noWrap_wedge_min R alpha t halpha0 halpha htL htR hsin

/-- Complete local one-gap estimate in the one-boundary-wrap case. -/
theorem wrap_phase_gap_lower
    (R alpha t : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d)
    (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ Real.pi / 4)
    (htL : Real.pi / 8 - alpha ≤ t)
    (htR : t ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    phaseSlope * (alpha / Real.pi) - cap +
        smallPhaseDefect (alpha / Real.pi) ≤
      phaseWedge R alpha t (t + alpha - Real.pi / 4) := by
  rw [phase_defect_identity]
  rw [← wrap_boundary_value R alpha hRc hRs hsin.ne']
  exact wrap_wedge_min R alpha t halpha0 halpha htL htR hsin

end

end SmallGapWedge
