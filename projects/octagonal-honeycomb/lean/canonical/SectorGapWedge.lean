import SmallGapWedge

/-!
# General octagonal sector-gap bridge

The regular-octagon support function has period `π/4`.  Write an actual normal
gap `α` as an integer number of octagonal sectors plus a residual
`β ∈ [0,π/4]`.  The support phases at the two ends differ by `β` modulo one
sector, while the wedge denominator and cosine retain the full angle `α`.

This module defines the exact boundary minimum

  `sectorMinimum α β = G(1, cos β + d sin β; α)`

and proves that every no-wrap or one-boundary-wrap support phase has wedge
contribution at least that minimum.  Thus the phase defect used by the external
interval certificate is connected directly to the geometric tangent wedge.
-/

namespace SectorGapWedge

noncomputable section

open Real
open PairGapCore
open OctagonalCornerBank
open PhaseSnappingSum
open PhaseSectorAlgebra
open SmallGapWedge

/-- Exact boundary minimum for actual gap `alpha` and residual octagonal-sector
gap `beta`. -/
def sectorMinimum (alpha beta : ℝ) : ℝ :=
  wedge alpha 1 (Real.cos beta + d * Real.sin beta)

/-- Excess above the affine tangent-area baseline. -/
def sectorDefect (alpha beta : ℝ) : ℝ :=
  sectorMinimum alpha beta -
    (phaseSlope * (alpha / Real.pi) - cap)

lemma noWrap_boundary_value_general
    (R alpha beta : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d) :
    phaseWedge R alpha (-(Real.pi / 8))
        (-(Real.pi / 8) + beta) = sectorMinimum alpha beta := by
  dsimp [phaseWedge, sectorMinimum]
  rw [boundary_support_left R hRc,
    boundary_support_right R beta hRc hRs]

lemma wrap_boundary_value_general
    (R alpha beta : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d) :
    phaseWedge R alpha (Real.pi / 8)
        (beta - Real.pi / 8) = sectorMinimum alpha beta := by
  dsimp [phaseWedge, sectorMinimum]
  rw [hRc, boundary_support_right_wrap R beta hRc hRs]

/-- General no-wrap wedge lower bound. -/
theorem noWrap_sector_min
    (R alpha beta t : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d)
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ Real.pi / 4)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + beta ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    sectorMinimum alpha beta ≤ phaseWedge R alpha t (t + beta) := by
  have hpair := noWrap_min alpha beta t hbeta0 hbeta htL htR
  have hfactor := phase_factor_nonneg R alpha hsin
  have hmul := mul_le_mul_of_nonneg_left hpair hfactor
  rw [← noWrap_boundary_value_general R alpha beta hRc hRs]
  rw [phaseWedge_eq_pair R alpha (-(Real.pi / 8))
      (-(Real.pi / 8) + beta) hsin.ne',
    phaseWedge_eq_pair R alpha t (t + beta) hsin.ne']
  exact hmul

/-- General one-boundary-wrap wedge lower bound. -/
theorem wrap_sector_min
    (R alpha beta t : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d)
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ Real.pi / 4)
    (htL : Real.pi / 8 - beta ≤ t)
    (htR : t ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    sectorMinimum alpha beta ≤
      phaseWedge R alpha t (t + beta - Real.pi / 4) := by
  have hpair := wrap_min alpha beta t hbeta0 hbeta htL htR
  have hfactor := phase_factor_nonneg R alpha hsin
  have hmul := mul_le_mul_of_nonneg_left hpair hfactor
  rw [← wrap_boundary_value_general R alpha beta hRc hRs]
  rw [phaseWedge_eq_pair R alpha (Real.pi / 8)
      (beta - Real.pi / 8) hsin.ne',
    phaseWedge_eq_pair R alpha t (t + beta - Real.pi / 4) hsin.ne']
  exact hmul

lemma baseline_add_defect (alpha beta : ℝ) :
    phaseSlope * (alpha / Real.pi) - cap + sectorDefect alpha beta =
      sectorMinimum alpha beta := by
  dsimp [sectorDefect]
  ring

/-- Local phase-gap inequality in the no-wrap support case. -/
theorem noWrap_local_gap
    (R alpha beta t : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d)
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ Real.pi / 4)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + beta ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    phaseSlope * (alpha / Real.pi) - cap + sectorDefect alpha beta ≤
      phaseWedge R alpha t (t + beta) := by
  rw [baseline_add_defect]
  exact noWrap_sector_min R alpha beta t hRc hRs hbeta0 hbeta htL htR hsin

/-- Local phase-gap inequality in the one-boundary-wrap support case. -/
theorem wrap_local_gap
    (R alpha beta t : ℝ)
    (hRc : R * Real.cos (Real.pi / 8) = 1)
    (hRs : R * Real.sin (Real.pi / 8) = d)
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ Real.pi / 4)
    (htL : Real.pi / 8 - beta ≤ t)
    (htR : t ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    phaseSlope * (alpha / Real.pi) - cap + sectorDefect alpha beta ≤
      phaseWedge R alpha t (t + beta - Real.pi / 4) := by
  rw [baseline_add_defect]
  exact wrap_sector_min R alpha beta t hRc hRs hbeta0 hbeta htL htR hsin

/-- On the first sector the general defect is the explicit small-phase defect. -/
theorem sectorDefect_eq_small
    (alpha : ℝ) (hsin : Real.sin alpha ≠ 0) :
    sectorDefect alpha alpha = smallPhaseDefect (alpha / Real.pi) := by
  have hpi : Real.pi * (alpha / Real.pi) = alpha := by
    field_simp [Real.pi_ne_zero]
  dsimp [sectorDefect, sectorMinimum]
  rw [boundary_wedge_identity alpha hsin]
  dsimp [smallPhaseDefect, phaseSlope]
  rw [hpi]
  ring

end

end SectorGapWedge
