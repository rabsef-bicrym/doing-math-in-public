import OctagonBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Nonnegativity of the octagonal phase defect on the second large sector

For `alpha = pi/2 + beta`, `0 <= beta <= pi/4`, the exact boundary minimum
is no smaller than the affine phase baseline.
-/

namespace SecondSectorDefectStandalone

noncomputable section

open Real
open OctagonBase

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
    nlinarith [d_quadratic]
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
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) d_nonneg) hs0)
      (sub_nonneg.mpr hsc)
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
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left Real.two_le_pi s_nonneg)
  apply (div_le_iff₀ Real.pi_pos).2
  nlinarith

lemma second_baseline_identity (beta : ℝ) :
    phaseSlope * ((Real.pi / 2 + beta) / Real.pi) - cap =
      1 + phaseSlope * (beta / Real.pi) := by
  have hsplit :
      (Real.pi / 2 + beta) / Real.pi =
        (1 : ℝ) / 2 + beta / Real.pi := by
    field_simp [Real.pi_ne_zero]
  have hconst : phaseSlope / 2 - cap = 1 := by
    dsimp [phaseSlope, cap, d]
    nlinarith [s_sq]
  rw [hsplit]
  nlinarith

/-- The exact sector minimum dominates the affine phase baseline on
`[pi/2, 3pi/4]`. -/
theorem second_sector_min_ge_baseline
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4) :
    phaseSlope * ((Real.pi / 2 + beta) / Real.pi) - cap ≤
      sectorMinimum (Real.pi / 2 + beta) beta := by
  have hcos := cos_beta_pos beta hb0 hbq
  have hsin0 := sin_beta_nonneg beta hb0 hbq
  let T : ℝ := Real.sin beta / Real.cos beta
  let K : ℝ := Real.cos beta + d * Real.sin beta
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact div_nonneg hsin0 hcos.le
  have hKsq : 1 ≤ K ^ 2 := by
    dsimp [K]
    exact support_sq_ge_one beta hb0 hbq
  have hKT : T ≤ K ^ 2 * T := by
    have := mul_le_mul_of_nonneg_right hKsq hT0
    simpa using this
  have hterm : T ≤ (1 + K ^ 2) * T / 2 := by
    nlinarith
  have hformula := sectorMinimum_second_formula beta hcos.ne'
  have hminimum : 1 + s * T ≤ sectorMinimum (Real.pi / 2 + beta) beta := by
    rw [hformula]
    change 1 + s * T ≤ 1 + d * T + (1 + K ^ 2) * T / 2
    have hds : d + 1 = s := by simp [d]
    nlinarith
  have htan := beta_le_tan_beta beta hb0 hbq
  have hcoeff := phaseSlope_div_pi_le_s
  have hphase : phaseSlope * (beta / Real.pi) ≤ s * T := by
    have h1 : phaseSlope * (beta / Real.pi) =
        (phaseSlope / Real.pi) * beta := by ring
    rw [h1]
    have hcoeffBeta := mul_le_mul_of_nonneg_right hcoeff hb0
    have htanScaled : s * beta ≤ s * T := by
      dsimp [T]
      exact mul_le_mul_of_nonneg_left htan s_nonneg
    nlinarith
  rw [second_baseline_identity]
  linarith

/-- Nonnegativity of the residual phase defect on the second large sector. -/
theorem second_sector_defect_nonneg
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4) :
    0 ≤ sectorMinimum (Real.pi / 2 + beta) beta -
      (phaseSlope * ((Real.pi / 2 + beta) / Real.pi) - cap) := by
  exact sub_nonneg.mpr (second_sector_min_ge_baseline beta hb0 hbq)

end

end SecondSectorDefectStandalone
