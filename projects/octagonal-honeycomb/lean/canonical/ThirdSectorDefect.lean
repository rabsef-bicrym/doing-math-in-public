import SectorGapWedge
import HHEdgeAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Nonnegativity of the phase defect on the third residual sector

For `α = 3π/4 + β`, `0 ≤ β < π/4`, the exact boundary minimum is already
at least `sqrt 2 + 1`, while the affine phase baseline never reaches that
value before `α = π`.  Hence the phase defect is strictly positive throughout
the third sector.
-/

namespace ThirdSectorDefect

noncomputable section

open Real
open PairGapCore
open NoncrystallineDomainReduction
open OctagonalCornerBank
open PhaseSnappingSum
open SmallGapWedge
open SectorGapWedge

lemma sin_beta_nonneg (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta < Real.pi / 4) : 0 ≤ Real.sin beta := by
  exact Real.sin_nonneg_of_nonneg_of_le_pi hb0
    (by nlinarith [hbq, Real.pi_pos])

lemma sin_beta_lt_cos_beta (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta < Real.pi / 4) : Real.sin beta < Real.cos beta := by
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := beta) (y := Real.pi / 2 - beta)
    (by nlinarith [hb0, Real.pi_pos])
    (by nlinarith [hb0])
    (by nlinarith [hbq])
  simpa [Real.sin_pi_div_two_sub] using h

lemma support_sq_ge_one (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta < Real.pi / 4) :
    1 ≤ (Real.cos beta + d * Real.sin beta) ^ 2 := by
  have hs0 := sin_beta_nonneg beta hb0 hbq
  have hsc := (sin_beta_lt_cos_beta beta hb0 hbq).le
  have hd2 : d ^ 2 = 1 - 2 * d := by
    nlinarith [HHEdgeAlgebra.d_quadratic]
  have hc2 : Real.cos beta ^ 2 = 1 - Real.sin beta ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq beta]
  have hid :
      (Real.cos beta + d * Real.sin beta) ^ 2 - 1 =
        2 * d * Real.sin beta * (Real.cos beta - Real.sin beta) := by
    ring_nf
    rw [hd2, hc2]
    ring
  have hright :
      0 ≤ 2 * d * Real.sin beta * (Real.cos beta - Real.sin beta) := by
    positivity
  linarith

lemma third_angle_sin (beta : ℝ) :
    Real.sin (3 * Real.pi / 4 + beta) =
      (s / 2) * (Real.cos beta - Real.sin beta) := by
  have hangle : 3 * Real.pi / 4 + beta =
      Real.pi - (Real.pi / 4 - beta) := by ring
  rw [hangle, Real.sin_pi_sub, Real.sin_sub,
    Real.sin_pi_div_four, Real.cos_pi_div_four]
  dsimp [s]
  ring

lemma third_angle_cos (beta : ℝ) :
    Real.cos (3 * Real.pi / 4 + beta) =
      -(s / 2) * (Real.sin beta + Real.cos beta) := by
  have hangle : 3 * Real.pi / 4 + beta =
      Real.pi - (Real.pi / 4 - beta) := by ring
  rw [hangle, Real.cos_pi_sub, Real.cos_sub,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  dsimp [s]
  ring

lemma sectorMinimum_third_formula
    (beta : ℝ) (hdiff : Real.cos beta - Real.sin beta ≠ 0) :
    sectorMinimum (3 * Real.pi / 4 + beta) beta =
      s * (Real.cos beta + d * Real.sin beta) /
          (Real.cos beta - Real.sin beta) +
        (1 + (Real.cos beta + d * Real.sin beta) ^ 2) *
          (Real.sin beta + Real.cos beta) /
          (2 * (Real.cos beta - Real.sin beta)) := by
  dsimp [sectorMinimum, wedge]
  rw [third_angle_sin, third_angle_cos]
  have hsne : s ≠ 0 := s_pos.ne'
  field_simp [hdiff, hsne]
  nlinarith [s_sq]

lemma third_sector_min_ge_s_add_one
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta < Real.pi / 4) :
    s + 1 ≤ sectorMinimum (3 * Real.pi / 4 + beta) beta := by
  have hs0 := sin_beta_nonneg beta hb0 hbq
  have hdiff : 0 < Real.cos beta - Real.sin beta := sub_pos.mpr
    (sin_beta_lt_cos_beta beta hb0 hbq)
  have hsupportDiff :
      Real.cos beta - Real.sin beta ≤
        Real.cos beta + d * Real.sin beta := by
    dsimp [d]
    nlinarith [s_pos]
  have hratio1 :
      1 ≤ (Real.cos beta + d * Real.sin beta) /
        (Real.cos beta - Real.sin beta) := by
    exact (le_div_iff₀ hdiff).2 (by linarith)
  have hsquare := support_sq_ge_one beta hb0 hbq
  have hsumDiff :
      Real.cos beta - Real.sin beta ≤
        Real.sin beta + Real.cos beta := by nlinarith
  have hratio2 :
      1 ≤ (Real.sin beta + Real.cos beta) /
        (Real.cos beta - Real.sin beta) := by
    exact (le_div_iff₀ hdiff).2 (by linarith)
  have hprod2 :
      2 ≤ (1 + (Real.cos beta + d * Real.sin beta) ^ 2) *
        ((Real.sin beta + Real.cos beta) /
          (Real.cos beta - Real.sin beta)) := by
    have hleft : 2 ≤ 1 + (Real.cos beta + d * Real.sin beta) ^ 2 := by
      linarith
    have hnonneg : 0 ≤ 1 + (Real.cos beta + d * Real.sin beta) ^ 2 := by
      positivity
    nlinarith [mul_le_mul hleft hratio2 (by norm_num) hnonneg]
  rw [sectorMinimum_third_formula beta hdiff.ne']
  have hsratio := mul_le_mul_of_nonneg_left hratio1 s_nonneg
  nlinarith

lemma third_baseline_le_s_add_one
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta < Real.pi / 4) :
    phaseSlope * ((3 * Real.pi / 4 + beta) / Real.pi) - cap ≤ s + 1 := by
  have hu : (3 * Real.pi / 4 + beta) / Real.pi ≤ 1 := by
    apply (div_le_one Real.pi_pos).2
    nlinarith
  have hphase := mul_le_mul_of_nonneg_left hu phaseSlope_pos.le
  have htop : phaseSlope - cap ≤ s + 1 := by
    dsimp [phaseSlope, cap, d]
    nlinarith [s_sq, s_lower]
  nlinarith

/-- Nonnegativity of the phase defect on `[3π/4,π)`. -/
theorem third_sector_defect_nonneg
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta < Real.pi / 4) :
    0 ≤ sectorDefect (3 * Real.pi / 4 + beta) beta := by
  dsimp [sectorDefect]
  have hmin := third_sector_min_ge_s_add_one beta hb0 hbq
  have hbase := third_baseline_le_s_add_one beta hb0 hbq
  linarith

end

end ThirdSectorDefect
