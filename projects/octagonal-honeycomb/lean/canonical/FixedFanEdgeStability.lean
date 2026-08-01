import Mathlib

/-!
# General fixed-fan edge stability

For a fixed normal fan, the mixed-area form has Lorentzian signature. After
splitting a polygon into the homothetic tangent polygon plus a zero-perimeter
deformation, conditioning one edge gives

  1 ≤ P²/(4f) - μ (x - e P/(2f))².

This file performs the exact algebraic endgame. The degenerate branch contains
the crystalline RR inequality; the nondegenerate branch contains the HH bound.
-/

namespace FixedFanEdgeStability

noncomputable section

open Real

lemma master_scaled
    (f μ e x P : ℝ) (hf : 0 < f)
    (hmaster : 1 ≤ P ^ 2 / (4 * f) - μ * (x - e * P / (2 * f)) ^ 2) :
    4 * f ≤ P ^ 2 - 4 * f * μ * (x - e * P / (2 * f)) ^ 2 := by
  have hm := mul_le_mul_of_nonneg_left hmaster (show 0 ≤ 4 * f by positivity)
  calc
    4 * f = (4 * f) * 1 := by ring
    _ ≤ (4 * f) * (P ^ 2 / (4 * f) - μ * (x - e * P / (2 * f)) ^ 2) := hm
    _ = P ^ 2 - 4 * f * μ * (x - e * P / (2 * f)) ^ 2 := by
      field_simp [ne_of_gt hf]

lemma master_quadratic
    (f μ e x P : ℝ) (hf : 0 < f)
    (hmaster : 1 ≤ P ^ 2 / (4 * f) - μ * (x - e * P / (2 * f)) ^ 2) :
    0 ≤ ((f - μ * e ^ 2) / f) * P ^ 2 + 4 * μ * e * x * P -
      4 * f * (μ * x ^ 2 + 1) := by
  have hs := master_scaled f μ e x P hf hmaster
  have heq :
      P ^ 2 - 4 * f * μ * (x - e * P / (2 * f)) ^ 2 - 4 * f =
        ((f - μ * e ^ 2) / f) * P ^ 2 + 4 * μ * e * x * P -
          4 * f * (μ * x ^ 2 + 1) := by
    field_simp [ne_of_gt hf]
    ring
  rw [← heq]
  linarith

theorem perimeter_lower_degenerate
    (f μ e x P : ℝ)
    (hf : 0 < f) (hμ : 0 < μ) (he : 0 < e) (hx : 0 < x)
    (hdeg : f = μ * e ^ 2)
    (hmaster : 1 ≤ P ^ 2 / (4 * f) - μ * (x - e * P / (2 * f)) ^ 2) :
    f * (μ * x ^ 2 + 1) / (μ * e * x) ≤ P := by
  have hq := master_quadratic f μ e x P hf hmaster
  have hzero : ((f - μ * e ^ 2) / f) * P ^ 2 = 0 := by
    rw [hdeg]
    ring
  rw [hzero, zero_add] at hq
  have hraw : f * (μ * x ^ 2 + 1) ≤ μ * e * x * P := by
    nlinarith
  have hden : 0 < μ * e * x := by positivity
  apply (div_le_iff₀ hden).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hraw

def lowerRoot (f μ e x : ℝ) : ℝ :=
  2 * f * (Real.sqrt (f - μ * e ^ 2 + μ * f * x ^ 2) - μ * e * x) /
    (f - μ * e ^ 2)

theorem perimeter_lower_nondegenerate
    (f μ e x P : ℝ)
    (hf : 0 < f) (hμ : 0 ≤ μ) (he : 0 ≤ e) (hx : 0 ≤ x) (hP : 0 ≤ P)
    (hD : 0 < f - μ * e ^ 2)
    (hmaster : 1 ≤ P ^ 2 / (4 * f) - μ * (x - e * P / (2 * f)) ^ 2) :
    lowerRoot f μ e x ≤ P := by
  let D : ℝ := f - μ * e ^ 2
  let S : ℝ := Real.sqrt (D + μ * f * x ^ 2)
  let R : ℝ := 2 * f * (S - μ * e * x) / D

  have hD' : 0 < D := by simpa [D] using hD
  have hrad : 0 ≤ D + μ * f * x ^ 2 := by positivity
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hS2 : S ^ 2 = D + μ * f * x ^ 2 := by
    dsimp [S]
    exact Real.sq_sqrt hrad
  have hmex0 : 0 ≤ μ * e * x := by positivity
  have hsep : 0 < S - μ * e * x := by
    have hidentity :
        S ^ 2 - (μ * e * x) ^ 2 = D * (1 + μ * x ^ 2) := by
      rw [hS2]
      dsimp [D]
      ring
    have hright : 0 < D * (1 + μ * x ^ 2) := by positivity
    nlinarith
  have hRpos : 0 < R := by
    dsimp [R]
    positivity

  have hroot :
      (D / f) * R ^ 2 + 4 * μ * e * x * R -
        4 * f * (μ * x ^ 2 + 1) = 0 := by
    dsimp [R]
    field_simp [ne_of_gt hf, ne_of_gt hD']
    nlinarith [hS2]

  have hq := master_quadratic f μ e x P hf hmaster
  have hqD :
      0 ≤ (D / f) * P ^ 2 + 4 * μ * e * x * P -
        4 * f * (μ * x ^ 2 + 1) := by
    simpa [D] using hq

  have hfactor :
      (D / f) * P ^ 2 + 4 * μ * e * x * P -
          4 * f * (μ * x ^ 2 + 1) =
        (P - R) * ((D / f) * (P + R) + 4 * μ * e * x) := by
    nlinarith [hroot]
  have hsecond : 0 < (D / f) * (P + R) + 4 * μ * e * x := by
    have hDf : 0 < D / f := div_pos hD' hf
    have hPRsum : 0 < P + R := by linarith
    positivity
  have hPR : R ≤ P := by
    by_contra hn
    have hlt : P < R := lt_of_not_ge hn
    have hneg :
        (P - R) * ((D / f) * (P + R) + 4 * μ * e * x) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hsecond
    rw [← hfactor] at hneg
    linarith
  simpa [lowerRoot, D, S, R] using hPR

end

end FixedFanEdgeStability
