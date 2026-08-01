import OctagonSupportNormalization
import SmallGapWedge
import PhaseBoundaryNormalization

/-!
# Identifying the two octagonal wedge normalizations

`SmallGapWedge.phaseWedge` uses the circumradius `R`, whereas the scale-free
sector algebra uses the squared factor `supportScaleSq`.  For the normalized
regular octagon these are exactly the same quantity.
-/

namespace OctagonPhaseWedgeNormalization

noncomputable section

open Real
open PairGapCore
open PhaseSectorAlgebra
open SmallGapWedge
open OctagonSupportNormalization
open PhaseBoundaryNormalization

lemma radius_sq_eq_supportScaleSq : R ^ 2 = supportScaleSq := by
  rw [R_sq]
  dsimp [supportScaleSq, d]
  nlinarith [s_sq]

/-- The geometric phase wedge is exactly the reconstructed sector wedge. -/
theorem phaseWedge_eq_sectorWedge
    (alpha x y : ℝ) (hsin : Real.sin alpha ≠ 0) :
    phaseWedge R alpha x y =
      sectorWedge (Real.sin alpha)
        (pairNumerator (Real.cos alpha) x y) := by
  rw [phaseWedge_eq_pair R alpha x y hsin]
  rw [sectorWedge_eq_factor, radius_sq_eq_supportScaleSq]

/-- Boundary-phase wedge for the normalized octagon. -/
theorem boundary_phaseWedge
    (alpha : ℝ) (hsin : Real.sin alpha ≠ 0) :
    phaseWedge R alpha (-(Real.pi / 8))
        (-(Real.pi / 8) + alpha) =
      angularBoundaryContribution alpha := by
  rw [phaseWedge_eq_sectorWedge alpha (-(Real.pi / 8))
    (-(Real.pi / 8) + alpha) hsin]
  exact sectorWedge_boundary alpha hsin

end

end OctagonPhaseWedgeNormalization
