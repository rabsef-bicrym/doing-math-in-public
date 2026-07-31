import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A seventh-order lower bound for arctangent

The alternating polynomial through `-x^7/7` lies below `arctan x` for
nonnegative `x`.  We use it only once, to show that `tan beta >= 7/8`
forces `beta > 11*pi/50`.
-/

namespace ArctanSeventhLower

noncomputable section

open Real


def seventh (x : ℝ) : ℝ :=
  x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7


def gap (x : ℝ) : ℝ := Real.arctan x - seventh x

lemma hasDerivAt_gap (x : ℝ) :
    HasDerivAt gap (x ^ 8 / (1 + x ^ 2)) x := by
  have hpoly : HasDerivAt seventh
      (1 - x ^ 2 + x ^ 4 - x ^ 6) x := by
    dsimp [seventh]
    convert (((hasDerivAt_id x).sub
      (((hasDerivAt_id x).pow 3).div_const 3)).add
      (((hasDerivAt_id x).pow 5).div_const 5)).sub
      (((hasDerivAt_id x).pow 7).div_const 7) using 1 <;> ring
  have hraw := (Real.hasDerivAt_arctan x).sub hpoly
  change HasDerivAt (Real.arctan - seventh)
    (x ^ 8 / (1 + x ^ 2)) x
  convert hraw using 1
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

lemma differentiable_gap : Differentiable ℝ gap :=
  fun x => (hasDerivAt_gap x).differentiableAt

lemma deriv_gap_nonneg (x : ℝ) : 0 ≤ deriv gap x := by
  rw [(hasDerivAt_gap x).deriv]
  positivity

/-- Alternating seventh-order lower bound, valid on the nonnegative axis. -/
theorem seventh_le_arctan (x : ℝ) (hx : 0 ≤ x) :
    seventh x ≤ Real.arctan x := by
  have hgrow := mul_sub_le_image_sub_of_le_deriv differentiable_gap
    (C := 0) deriv_gap_nonneg (x := 0) (y := x) hx
  norm_num [gap, seventh] at hgrow ⊢
  linarith

lemma eleven_pi_over_fifty_lt_arctan_seven_eighths :
    11 * Real.pi / 50 < Real.arctan ((7 : ℝ) / 8) := by
  have hpi : 11 * Real.pi / 50 < (693 : ℝ) / 1000 := by
    have hp := Real.pi_lt_d2
    nlinarith
  have hpoly : (693 : ℝ) / 1000 < seventh ((7 : ℝ) / 8) := by
    norm_num [seventh]
  have hatan := seventh_le_arctan ((7 : ℝ) / 8) (by norm_num)
  linarith

lemma arctan_le_self_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    Real.arctan x ≤ x := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp
  · have ha : 0 < Real.arctan x := Real.arctan_pos.mpr hxpos
    have hlt := Real.lt_tan ha (Real.arctan_lt_pi_div_two x)
    rw [Real.tan_arctan] at hlt
    exact hlt.le

lemma arctan_lt_pi_over_fifteen_of_lt_one_fifth
    (x : ℝ) (hx0 : 0 ≤ x) (hx : x < (1 : ℝ) / 5) :
    Real.arctan x < Real.pi / 15 := by
  have hself := arctan_le_self_of_nonneg x hx0
  have hpi : (1 : ℝ) / 5 < Real.pi / 15 := by
    nlinarith [Real.pi_gt_three]
  linarith

lemma eleven_pi_over_fifty_lt_arctan_of_seven_eighths_lt
    (x : ℝ) (hx : (7 : ℝ) / 8 < x) :
    11 * Real.pi / 50 < Real.arctan x := by
  have hmono := Real.arctan_strictMono hx
  exact lt_trans eleven_pi_over_fifty_lt_arctan_seven_eighths hmono

end

end ArctanSeventhLower
