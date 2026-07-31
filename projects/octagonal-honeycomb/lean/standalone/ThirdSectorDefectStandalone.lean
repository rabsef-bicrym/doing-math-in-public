import OctagonBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Nonnegativity of the octagonal phase defect on the third large sector

For `alpha = 3*pi/4 + beta`, `0 <= beta < pi/4`, the boundary minimum is
already at least `sqrt 2 + 1`, while the affine phase baseline never exceeds
that value before `alpha = pi`.
-/

namespace ThirdSectorDefectStandalone

noncomputable section

open Real
open OctagonBase

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
  ring_nf
  rw [s_sq]
  ring

lemma third_sector_min_ge_s_add_one
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta < Real.pi / 4) :
    s + 1 ≤ sectorMinimum (3 * Real.pi / 4 + beta) beta := by
  let K : ℝ := Real.cos beta + d * Real.sin beta
  let D : ℝ := Real.cos beta - Real.sin beta
  let N : ℝ := Real.sin beta + Real.cos beta
  have hdiff : 0 < D := by
    dsimp [D]
    exact sub_pos.mpr (sin_beta_lt_cos_beta beta hb0 hbq)
  have hsupportDiff : D ≤ K := by
    dsimp [D, K, d]
    have hs0 := sin_beta_nonneg beta hb0 hbq
    nlinarith [s_pos]
  have hratio1 : 1 ≤ K / D :=
    (le_div_iff₀ hdiff).2 (by simpa using hsupportDiff)
  have hsquare : 1 ≤ K ^ 2 := by
    dsimp [K]
    exact support_sq_ge_one beta hb0 hbq
  have hDN : D ≤ N := by
    dsimp [D, N]
    nlinarith [sin_beta_nonneg beta hb0 hbq]
  have hN0 : 0 ≤ N := le_trans hdiff.le hDN
  have hA : 2 ≤ 1 + K ^ 2 := by linarith
  have hprod : 2 * D ≤ (1 + K ^ 2) * N := by
    exact mul_le_mul hA hDN hdiff.le (by positivity)
  have hfirst : s ≤ s * K / D := by
    have hm := mul_le_mul_of_nonneg_left hratio1 s_nonneg
    simpa [mul_div_assoc] using hm
  have hsecond : 1 ≤ (1 + K ^ 2) * N / (2 * D) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hdiff)).2
    simpa [one_mul, mul_assoc] using hprod
  rw [sectorMinimum_third_formula beta hdiff.ne']
  change s + 1 ≤ s * K / D + (1 + K ^ 2) * N / (2 * D)
  linarith

lemma third_baseline_le_s_add_one
    (beta : ℝ) (hbq : beta < Real.pi / 4) :
    phaseSlope * ((3 * Real.pi / 4 + beta) / Real.pi) - cap ≤ s + 1 := by
  have hu : (3 * Real.pi / 4 + beta) / Real.pi ≤ 1 := by
    apply (div_le_one Real.pi_pos).2
    nlinarith
  have hphase := mul_le_mul_of_nonneg_left hu phaseSlope_pos.le
  have htop : phaseSlope - cap ≤ s + 1 := by
    dsimp [phaseSlope, cap, d]
    nlinarith [s_sq, s_lower]
  nlinarith

/-- Nonnegativity of the residual phase defect on the third large sector. -/
theorem third_sector_defect_nonneg
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta < Real.pi / 4) :
    0 ≤ sectorMinimum (3 * Real.pi / 4 + beta) beta -
      (phaseSlope * ((3 * Real.pi / 4 + beta) / Real.pi) - cap) := by
  have hmin := third_sector_min_ge_s_add_one beta hb0 hbq
  have hbase := third_baseline_le_s_add_one beta hbq
  linarith

end

end ThirdSectorDefectStandalone
