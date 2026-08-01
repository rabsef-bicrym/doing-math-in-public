import PhaseBoundaryNormalization
import OneGapPhasePackage

/-!
# Complete one-sector geometric gap bridge

For a gap of size at most `π/4`, the one-sector minimization theorem puts the
scale-free pair numerator above its boundary value.  Restoring the octagonal
support scale gives the exact phase-snapping boundary contribution, which then
supplies both the local tangent-area inequality and the sharp `4/25` reserve.
-/

namespace OneSectorGapBridge

noncomputable section

open Real
open PairGapCore
open ContinuousCornerBank
open OctagonalCornerBank
open PhaseSnappingSum
open PhaseSectorAlgebra
open PhaseBoundaryNormalization
open OneGapPhasePackage
open CollisionCornerCredit

lemma normalized_boundaryContribution (alpha : ℝ) :
    boundaryContribution (alpha / Real.pi) =
      angularBoundaryContribution alpha := by
  have hpi : Real.pi * (alpha / Real.pi) = alpha := by
    field_simp [Real.pi_ne_zero]
  dsimp [boundaryContribution, angularBoundaryContribution]
  rw [hpi]

/-- No-wrap reduced phase: the geometric wedge is bounded below by the exact
boundary-phase contribution. -/
theorem noWrap_boundary_lower
    (alpha t : ℝ)
    (ha0 : 0 ≤ alpha) (haq : alpha ≤ Real.pi / 4)
    (hsin : 0 < Real.sin alpha)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + alpha ≤ Real.pi / 8) :
    angularBoundaryContribution alpha ≤
      sectorWedge (Real.sin alpha)
        (pairNumerator (Real.cos alpha) t (t + alpha)) := by
  have hpair := noWrap_min alpha alpha t ha0 haq htL htR
  apply angularBoundaryContribution_le_sectorWedge alpha
    (pairNumerator (Real.cos alpha) t (t + alpha)) hsin
  simpa [boundaryPairNumerator] using hpair

/-- Wrap reduced phase: the same lower bound holds after crossing the sector
boundary at `π/8`. -/
theorem wrap_boundary_lower
    (alpha t : ℝ)
    (ha0 : 0 ≤ alpha) (haq : alpha ≤ Real.pi / 4)
    (hsin : 0 < Real.sin alpha)
    (htL : Real.pi / 8 - alpha ≤ t)
    (htR : t ≤ Real.pi / 8) :
    angularBoundaryContribution alpha ≤
      sectorWedge (Real.sin alpha)
        (pairNumerator (Real.cos alpha) t
          (t + alpha - Real.pi / 4)) := by
  have hpair := wrap_min alpha alpha t ha0 haq htL htR
  apply angularBoundaryContribution_le_sectorWedge alpha
    (pairNumerator (Real.cos alpha) t
      (t + alpha - Real.pi / 4)) hsin
  simpa [boundaryPairNumerator] using hpair

/-- Full no-wrap package in normalized-angle coordinates. -/
theorem noWrap_one_gap_package
    (alpha t : ℝ)
    (ha0 : 0 ≤ alpha) (haq : alpha ≤ Real.pi / 4)
    (hsin : 0 < Real.sin alpha)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + alpha ≤ Real.pi / 8) :
    phaseSlope * (alpha / Real.pi) - cap +
        smallPhaseDefect (alpha / Real.pi) ≤
      sectorWedge (Real.sin alpha)
        (pairNumerator (Real.cos alpha) t (t + alpha)) ∧
    smallGapReserve * pos (1 - 4 * (alpha / Real.pi)) ≤
      smallPhaseDefect (alpha / Real.pi) := by
  have hu0 : 0 ≤ alpha / Real.pi := div_nonneg ha0 Real.pi_pos.le
  have huq : alpha / Real.pi ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith
  have hboundary := noWrap_boundary_lower alpha t ha0 haq hsin htL htR
  rw [← normalized_boundaryContribution alpha] at hboundary
  exact one_gap_package (alpha / Real.pi)
    (sectorWedge (Real.sin alpha)
      (pairNumerator (Real.cos alpha) t (t + alpha)))
    hu0 huq hboundary

/-- Full wrap package in normalized-angle coordinates. -/
theorem wrap_one_gap_package
    (alpha t : ℝ)
    (ha0 : 0 ≤ alpha) (haq : alpha ≤ Real.pi / 4)
    (hsin : 0 < Real.sin alpha)
    (htL : Real.pi / 8 - alpha ≤ t)
    (htR : t ≤ Real.pi / 8) :
    phaseSlope * (alpha / Real.pi) - cap +
        smallPhaseDefect (alpha / Real.pi) ≤
      sectorWedge (Real.sin alpha)
        (pairNumerator (Real.cos alpha) t
          (t + alpha - Real.pi / 4)) ∧
    smallGapReserve * pos (1 - 4 * (alpha / Real.pi)) ≤
      smallPhaseDefect (alpha / Real.pi) := by
  have hu0 : 0 ≤ alpha / Real.pi := div_nonneg ha0 Real.pi_pos.le
  have huq : alpha / Real.pi ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith
  have hboundary := wrap_boundary_lower alpha t ha0 haq hsin htL htR
  rw [← normalized_boundaryContribution alpha] at hboundary
  exact one_gap_package (alpha / Real.pi)
    (sectorWedge (Real.sin alpha)
      (pairNumerator (Real.cos alpha) t
        (t + alpha - Real.pi / 4)))
    hu0 huq hboundary

end

end OneSectorGapBridge
