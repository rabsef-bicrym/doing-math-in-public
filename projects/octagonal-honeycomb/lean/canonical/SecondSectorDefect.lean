import SectorGapWedge
import HHEdgeAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Nonnegativity of the phase defect on the second octagonal sector

For `α = π/2 + β`, `0 ≤ β ≤ π/4`, the exact boundary minimum has a simple
form.  Its excess above the value at `π/2` dominates `sqrt 2 * tan β`, while
the affine phase baseline grows more slowly.  Hence the sector defect is
nonnegative throughout the whole interval `[π/2,3π/4]`.
-/

namespace SecondSectorDefect

noncomputable section

open Real
open PairGapCore
open NoncrystallineDomainReduction
open OctagonalCornerBank
open PhaseSnappingSum
open SmallGapWedge
open SectorGapWedge

lemma sin_beta_nonneg (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) : 0 ≤ Real.sin beta := by
  exact Real.sin_nonneg_of_nonneg_of_le_pi hb0
    (by nlinarith [hbq, Real.pi_pos])

lemma cos_beta_pos (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) : 0 < Real.cos beta := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [hb0, hbq, Real.pi_pos]

lemma sin_beta_le_cos_beta (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) : Real.sin beta ≤ Real.cos beta := by
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two
    (x := beta) (y := Real.pi / 2 - beta)
    (by nlinarith [hb0, Real.pi_pos])
    (by nlinarith [hb0])
    (by nlinarith [hbq])
  simpa [Real.sin_pi_div_two_sub] using h

lemma support_sq_ge_one (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) :
    1 ≤ (Real.cos beta + d * Real.sin beta) ^ 2 := by
  have hs0 := sin_beta_nonneg beta hb0 hbq
  have hsc := sin_beta_le_cos_beta beta hb0 hbq
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

lemma second_angle_sin (beta : ℝ) :
    Real.sin (Real.pi / 2 + beta) = Real.cos beta := by
  rw [Real.sin_add]
  simp

lemma second_angle_cos (beta : ℝ) :
    Real.cos (Real.pi / 2 + beta) = -Real.sin beta := by
  rw [Real.cos_add]
  simp

lemma sectorMinimum_second_formula
    (beta : ℝ) (hcos : Real.cos beta ≠ 0) :
    sectorMinimum (Real.pi / 2 + beta) beta =
      1 + d * (Real.sin beta / Real.cos beta) +
        (1 + (Real.cos beta + d * Real.sin beta) ^ 2) *
          (Real.sin beta / Real.cos beta) / 2 := by
  dsimp [sectorMinimum, wedge]
  rw [second_angle_sin, second_angle_cos]
  field_simp [hcos]
  ring

lemma beta_le_tan_beta (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) :
    beta ≤ Real.sin beta / Real.cos beta := by
  rcases hb0.eq_or_lt with rfl | hbpos
  · simp
  · have hlt := Real.lt_tan hbpos (by nlinarith [hbq, Real.pi_pos])
    rw [Real.tan_eq_sin_div_cos] at hlt
    exact hlt.le

lemma phaseSlope_div_pi_le_s : phaseSlope / Real.pi ≤ s := by
  have hnum : phaseSlope ≤ 2 * s := by
    dsimp [phaseSlope]
    nlinarith [s_lower]
  have hpi : 2 * s ≤ s * Real.pi := by
    have := mul_le_mul_of_nonneg_left Real.two_le_pi s_nonneg
    nlinarith
  apply (div_le_iff₀ Real.pi_pos).2
  nlinarith

lemma second_baseline_identity (beta : ℝ) :
    phaseSlope * ((Real.pi / 2 + beta) / Real.pi) - cap =
      1 + phaseSlope * (beta / Real.pi) := by
  have hsplit :
      (Real.pi / 2 + beta) / Real.pi =
        (1 : ℝ) / 2 + beta / Real.pi := by
    field_simp [Real.pi_ne_zero]
    ring
  have hconst : phaseSlope / 2 - cap = 1 := by
    dsimp [phaseSlope, cap, d]
    nlinarith [s_sq]
  rw [hsplit]
  nlinarith

/-- The exact sector minimum dominates the affine phase baseline on the entire
second residual sector. -/
theorem second_sector_min_ge_baseline
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4) :
    phaseSlope * ((Real.pi / 2 + beta) / Real.pi) - cap ≤
      sectorMinimum (Real.pi / 2 + beta) beta := by
  have hcos := cos_beta_pos beta hb0 hbq
  have hsin0 := sin_beta_nonneg beta hb0 hbq
  have ht0 : 0 ≤ Real.sin beta / Real.cos beta :=
    div_nonneg hsin0 hcos.le
  have hsquare := support_sq_ge_one beta hb0 hbq
  have hmul := mul_le_mul_of_nonneg_right hsquare ht0
  have hformula := sectorMinimum_second_formula beta hcos.ne'
  have hminimum :
      1 + s * (Real.sin beta / Real.cos beta) ≤
        sectorMinimum (Real.pi / 2 + beta) beta := by
    rw [hformula]
    dsimp [d]
    nlinarith
  have htan := beta_le_tan_beta beta hb0 hbq
  have hcoeff := phaseSlope_div_pi_le_s
  have hcoeffBeta := mul_le_mul_of_nonneg_right hcoeff hb0
  have hphase :
      phaseSlope * (beta / Real.pi) ≤
        s * (Real.sin beta / Real.cos beta) := by
    have h1 : phaseSlope * (beta / Real.pi) =
        (phaseSlope / Real.pi) * beta := by ring
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left htan s_nonneg]
  rw [second_baseline_identity]
  linarith

/-- Nonnegativity of the phase defect on `[π/2,3π/4]`. -/
theorem second_sector_defect_nonneg
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4) :
    0 ≤ sectorDefect (Real.pi / 2 + beta) beta := by
  dsimp [sectorDefect]
  exact sub_nonneg.mpr (second_sector_min_ge_baseline beta hb0 hbq)

end

end SecondSectorDefect
