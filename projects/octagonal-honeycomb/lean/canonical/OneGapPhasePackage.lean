import SmallGapReserve
import PhaseSnappingSum

/-!
# One-gap package for the noncrystalline geometric bridge

For a gap shorter than one octagonal sector, the phase-snapping defect is the
exact difference between the affine baseline and the boundary-phase tangent
wedge.  Thus any geometric lower bound by that boundary wedge simultaneously
provides the local tangent-area inequality and the mandatory small-gap reserve.
-/

namespace OneGapPhasePackage

noncomputable section

open Real
open PairGapCore
open ContinuousCornerBank
open OctagonalCornerBank
open PhaseSnappingSum
open CollisionCornerCredit

/-- Boundary-phase tangent-wedge contribution for a normalized gap `u`. -/
def boundaryContribution (u : ℝ) : ℝ :=
  d * Real.sin (Real.pi * u) *
    (Real.cos (Real.pi * u) + Real.sin (Real.pi * u))

lemma defect_identity (u : ℝ) :
    phaseSlope * u - cap + smallPhaseDefect u = boundaryContribution u := by
  dsimp [phaseSlope, cap, smallPhaseDefect, boundaryContribution]
  ring

/-- A lower bound by the boundary-phase wedge is exactly the local area
inequality required by `PhaseSnappingSum`. -/
theorem local_area_of_boundary_lower
    (u contribution : ℝ)
    (hboundary : boundaryContribution u ≤ contribution) :
    phaseSlope * u - cap + smallPhaseDefect u ≤ contribution := by
  rw [defect_identity]
  exact hboundary

/-- Complete one-gap package on `[0,1/4]`: boundary-phase minimization supplies
the local tangent-area estimate, while the independent small-gap theorem
supplies the reserve used for high side counts. -/
theorem one_gap_package
    (u contribution : ℝ)
    (hu : 0 ≤ u) (hub : u ≤ (1 : ℝ) / 4)
    (hboundary : boundaryContribution u ≤ contribution) :
    phaseSlope * u - cap + smallPhaseDefect u ≤ contribution ∧
      smallGapReserve * pos (1 - 4 * u) ≤ smallPhaseDefect u := by
  exact ⟨local_area_of_boundary_lower u contribution hboundary,
    SmallGapReserve.small_gap_reserve u hu hub⟩

end

end OneGapPhasePackage
