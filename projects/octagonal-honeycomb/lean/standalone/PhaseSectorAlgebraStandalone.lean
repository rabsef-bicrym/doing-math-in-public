import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# One-sector minimization for the regular-octagon support function

Inside one support sector the support function is a positive constant times
`cos t`, with `t` in `[-pi/8,pi/8]`.  For fixed actual normal gap and fixed
residual phase difference, the tangent-wedge numerator is minimized at a
sector boundary.
-/

namespace PhaseSectorAlgebraStandalone

noncomputable section

open Real

/-- Scale-free numerator of one tangent-wedge contribution. -/
def pairNumerator (c x y : ℝ) : ℝ :=
  2 * Real.cos x * Real.cos y -
    c * (Real.cos x ^ 2 + Real.cos y ^ 2)

lemma two_cos_mul_cos (x y : ℝ) :
    2 * Real.cos x * Real.cos y =
      Real.cos (y - x) + Real.cos (x + y) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

lemma cos_sq_add_cos_sq (x y : ℝ) :
    Real.cos x ^ 2 + Real.cos y ^ 2 =
      1 + Real.cos (y - x) * Real.cos (x + y) := by
  have hcx : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hcy : Real.cos y ^ 2 = 1 - Real.sin y ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq y]
  rw [Real.cos_sub, Real.cos_add]
  ring_nf
  rw [hcx, hcy]
  ring

lemma pairNumerator_identity (c x y : ℝ) :
    pairNumerator c x y =
      Real.cos (y - x) - c +
        (1 - c * Real.cos (y - x)) * Real.cos (x + y) := by
  dsimp [pairNumerator]
  rw [two_cos_mul_cos, cos_sq_add_cos_sq]
  ring

lemma one_sub_cos_mul_cos_nonneg (a b : ℝ) :
    0 ≤ 1 - Real.cos a * Real.cos b := by
  have ha : |Real.cos a| ≤ 1 := Real.abs_cos_le_one a
  have hb : |Real.cos b| ≤ 1 := Real.abs_cos_le_one b
  have hab : |Real.cos a * Real.cos b| ≤ 1 := by
    rw [abs_mul]
    calc
      |Real.cos a| * |Real.cos b| ≤ 1 * 1 := by
        exact mul_le_mul ha hb (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hle : Real.cos a * Real.cos b ≤ 1 :=
    le_trans (le_abs_self _) hab
  linarith

lemma cos_of_abs_le
    (a y : ℝ) (haπ : a ≤ Real.pi)
    (hy : |y| ≤ a) :
    Real.cos a ≤ Real.cos y := by
  have hy0 : 0 ≤ |y| := abs_nonneg _
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hy0 haπ hy
  simpa using hmono

/-- No-wrap reduced phases. -/
theorem noWrap_min
    (alpha beta t : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ Real.pi / 4)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + beta ≤ Real.pi / 8) :
    pairNumerator (Real.cos alpha) (-(Real.pi / 8))
        (-(Real.pi / 8) + beta) ≤
      pairNumerator (Real.cos alpha) t (t + beta) := by
  let a : ℝ := Real.pi / 4 - beta
  let y : ℝ := 2 * t + beta
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have haπ : a ≤ Real.pi := by
    dsimp [a]
    nlinarith [Real.pi_pos]
  have hyUpper : y ≤ a := by dsimp [y, a]; linarith
  have hyLower : -a ≤ y := by dsimp [y, a]; linarith
  have hyabs : |y| ≤ a := (abs_le).2 ⟨hyLower, hyUpper⟩
  have hcos : Real.cos a ≤ Real.cos y := cos_of_abs_le a y haπ hyabs
  have hcoef : 0 ≤ 1 - Real.cos alpha * Real.cos beta :=
    one_sub_cos_mul_cos_nonneg alpha beta
  rw [pairNumerator_identity, pairNumerator_identity]
  have hdiffBoundary :
      (-(Real.pi / 8) + beta) - (-(Real.pi / 8)) = beta := by ring
  have hsumBoundary :
      (-(Real.pi / 8)) + (-(Real.pi / 8) + beta) = -a := by
    dsimp [a]
    ring
  have hdiff : t + beta - t = beta := by ring
  have hsum : t + (t + beta) = y := by dsimp [y]; ring
  rw [hdiffBoundary, hsumBoundary, hdiff, hsum, Real.cos_neg]
  have hmul := mul_le_mul_of_nonneg_left hcos hcoef
  nlinarith

/-- One-boundary-wrap reduced phases. -/
theorem wrap_min
    (alpha beta t : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ Real.pi / 4)
    (htL : Real.pi / 8 - beta ≤ t)
    (htR : t ≤ Real.pi / 8) :
    pairNumerator (Real.cos alpha) (Real.pi / 8)
        (beta - Real.pi / 8) ≤
      pairNumerator (Real.cos alpha) t
        (t + beta - Real.pi / 4) := by
  let a : ℝ := beta
  let y : ℝ := 2 * t + beta - Real.pi / 4
  let gap : ℝ := beta - Real.pi / 4
  have haπ : a ≤ Real.pi := by
    dsimp [a]
    nlinarith [hbeta, Real.pi_pos]
  have hyUpper : y ≤ a := by dsimp [y, a]; linarith
  have hyLower : -a ≤ y := by dsimp [y, a]; linarith
  have hyabs : |y| ≤ a := (abs_le).2 ⟨hyLower, hyUpper⟩
  have hcos : Real.cos a ≤ Real.cos y := cos_of_abs_le a y haπ hyabs
  have hcoef : 0 ≤ 1 - Real.cos alpha * Real.cos gap :=
    one_sub_cos_mul_cos_nonneg alpha gap
  rw [pairNumerator_identity, pairNumerator_identity]
  have hdiffBoundary :
      (beta - Real.pi / 8) - Real.pi / 8 = gap := by
    dsimp [gap]
    ring
  have hsumBoundary :
      Real.pi / 8 + (beta - Real.pi / 8) = a := by
    dsimp [a]
    ring
  have hdiff :
      (t + beta - Real.pi / 4) - t = gap := by
    dsimp [gap]
    ring
  have hsum :
      t + (t + beta - Real.pi / 4) = y := by
    dsimp [y]
    ring
  rw [hdiffBoundary, hsumBoundary, hdiff, hsum]
  have hmul := mul_le_mul_of_nonneg_left hcos hcoef
  nlinarith

end

end PhaseSectorAlgebraStandalone
