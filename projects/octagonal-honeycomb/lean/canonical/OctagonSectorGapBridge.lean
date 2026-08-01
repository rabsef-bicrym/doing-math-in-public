import SectorGapWedge
import OctagonSupportNormalization
import SmallGapReserve

/-!
# Sector-gap bridge for the normalized regular octagon

This module instantiates the abstract sector-gap wedge theorem with the exact
circumradius of the apothem-one regular octagon.  On the first sector it also
attaches the sharp `4/25` small-gap reserve.
-/

namespace OctagonSectorGapBridge

noncomputable section

open Real
open PairGapCore
open ContinuousCornerBank
open OctagonalCornerBank
open PhaseSnappingSum
open CollisionCornerCredit
open SmallGapReserve
open SmallGapWedge
open SectorGapWedge
open OctagonSupportNormalization

/-- General residual-sector gap, no wrap. -/
theorem noWrap_local
    (alpha beta t : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ Real.pi / 4)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + beta ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    phaseSlope * (alpha / Real.pi) - cap + sectorDefect alpha beta ≤
      phaseWedge R alpha t (t + beta) := by
  exact noWrap_local_gap R alpha beta t R_mul_cos_eighth R_mul_sin_eighth
    hbeta0 hbeta htL htR hsin

/-- General residual-sector gap, one-boundary wrap. -/
theorem wrap_local
    (alpha beta t : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ Real.pi / 4)
    (htL : Real.pi / 8 - beta ≤ t)
    (htR : t ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    phaseSlope * (alpha / Real.pi) - cap + sectorDefect alpha beta ≤
      phaseWedge R alpha t (t + beta - Real.pi / 4) := by
  exact wrap_local_gap R alpha beta t R_mul_cos_eighth R_mul_sin_eighth
    hbeta0 hbeta htL htR hsin

/-- First-sector no-wrap package: local area plus small-gap reserve. -/
theorem noWrap_small_package
    (alpha t : ℝ)
    (ha0 : 0 ≤ alpha) (haq : alpha ≤ Real.pi / 4)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + alpha ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    phaseSlope * (alpha / Real.pi) - cap + sectorDefect alpha alpha ≤
        phaseWedge R alpha t (t + alpha) ∧
      smallGapReserve * pos (1 - 4 * (alpha / Real.pi)) ≤
        sectorDefect alpha alpha := by
  have hlocal := noWrap_local alpha alpha t ha0 haq htL htR hsin
  have hu0 : 0 ≤ alpha / Real.pi := div_nonneg ha0 Real.pi_pos.le
  have huq : alpha / Real.pi ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith
  have hreserve := small_gap_reserve (alpha / Real.pi) hu0 huq
  have heq := sectorDefect_eq_small alpha hsin.ne'
  rw [← heq] at hreserve
  exact ⟨hlocal, hreserve⟩

/-- First-sector wrap package: local area plus small-gap reserve. -/
theorem wrap_small_package
    (alpha t : ℝ)
    (ha0 : 0 ≤ alpha) (haq : alpha ≤ Real.pi / 4)
    (htL : Real.pi / 8 - alpha ≤ t)
    (htR : t ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    phaseSlope * (alpha / Real.pi) - cap + sectorDefect alpha alpha ≤
        phaseWedge R alpha t (t + alpha - Real.pi / 4) ∧
      smallGapReserve * pos (1 - 4 * (alpha / Real.pi)) ≤
        sectorDefect alpha alpha := by
  have hlocal := wrap_local alpha alpha t ha0 haq htL htR hsin
  have hu0 : 0 ≤ alpha / Real.pi := div_nonneg ha0 Real.pi_pos.le
  have huq : alpha / Real.pi ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith
  have hreserve := small_gap_reserve (alpha / Real.pi) hu0 huq
  have heq := sectorDefect_eq_small alpha hsin.ne'
  rw [← heq] at hreserve
  exact ⟨hlocal, hreserve⟩

end

end OctagonSectorGapBridge
