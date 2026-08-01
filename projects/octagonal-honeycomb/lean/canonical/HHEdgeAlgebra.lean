import PairGapCore

/-!
# Algebraic bridge for the crystalline HH-edge surgery

The geometric surgery supplies three facts: the added area is `x^2/4`, the
perimeter increment is `d*x`, and the circumscribed-fan area changes from `f`
to `f+d^2`.  This file proves, from those data and the augmented Chakerian
inequality, the exact HH lower bound used in the pair-gap argument.
-/

namespace HHEdgeAlgebra

noncomputable section

open Real
open PairGapCore

lemma d_quadratic : d ^ 2 + 2 * d = 1 := by
  dsimp [d]
  nlinarith [s_sq]

/-- Replacing a segment of length `x` by the two equal legs of its external
45-45-90 triangle increases length by `(sqrt 2 - 1)x = d*x`. -/
lemma perimeter_increment (x : ℝ) : s * x - x = d * x := by
  dsimp [d]
  ring

/-- The two new equal legs have total Euclidean length `sqrt 2 * x`. -/
lemma new_side_total (x : ℝ) : 2 * (s * x / 2) = s * x := by ring

/-- The attached right isosceles triangle has base `x`, altitude `x/2`, and
therefore area `x^2/4`. -/
lemma added_triangle_area (x : ℝ) : x * (x / 2) / 2 = x ^ 2 / 4 := by ring

/-- The local fan replacement changes its area contribution by `d^2`. -/
lemma fan_merge (f : ℝ) : f - 2 * d + 1 = f + d ^ 2 := by
  nlinarith [d_quadratic]

/-- Expanded form of Chakerian's inequality for the augmented polygon. -/
theorem hh_quadratic_of_augmented_chakerian
    (P x f : ℝ)
    (hchak : 4 * (f + d ^ 2) * (1 + x ^ 2 / 4) ≤ (P + d * x) ^ 2) :
    4 * (f + d ^ 2) ≤ P ^ 2 + 2 * d * P * x - f * x ^ 2 := by
  nlinarith

/-- The exact square-root HH-edge perimeter bound. -/
theorem hh_perimeter_lower
    (P x f : ℝ)
    (hP : 0 ≤ P) (hx : 0 ≤ x) (hf : 0 ≤ f)
    (hchak : 4 * (f + d ^ 2) * (1 + x ^ 2 / 4) ≤ (P + d * x) ^ 2) :
    Real.sqrt (f + d ^ 2) * Real.sqrt (x ^ 2 + 4) - d * x ≤ P := by
  let U := Real.sqrt (f + d ^ 2) * Real.sqrt (x ^ 2 + 4)
  let V := P + d * x
  have hfd : 0 ≤ f + d ^ 2 := by positivity
  have hxx : 0 ≤ x ^ 2 + 4 := by positivity
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V]
    exact add_nonneg hP (mul_nonneg d_nonneg hx)
  have hU2 : U ^ 2 = (f + d ^ 2) * (x ^ 2 + 4) := by
    dsimp [U]
    rw [mul_pow, Real.sq_sqrt hfd, Real.sq_sqrt hxx]
  have hscaled : (f + d ^ 2) * (x ^ 2 + 4) ≤ V ^ 2 := by
    dsimp [V]
    nlinarith
  have hUV : U ≤ V := by nlinarith
  dsimp [U, V] at hUV ⊢
  linarith

/-- Restatement in the metric-excess normalization used by the discharging
argument. -/
theorem hh_metric_excess
    (P x f : ℝ)
    (hP : 0 ≤ P) (hx : 0 ≤ x) (hf : 0 ≤ f)
    (hchak : 4 * (f + d ^ 2) * (1 + x ^ 2 / 4) ≤ (P + d * x) ^ 2) :
    h x f ≤ P - 2 * Real.sqrt f := by
  have hp := hh_perimeter_lower P x f hP hx hf hchak
  dsimp [h]
  linarith

end

end HHEdgeAlgebra
