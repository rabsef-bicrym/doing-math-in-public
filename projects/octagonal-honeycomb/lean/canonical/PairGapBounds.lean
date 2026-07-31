import PairGapMonotone

/-!
# Exact large-edge bounds for the pair-gap theorem

This module contains the tangent-line certificate, rational brackets, and
AM--GM estimates used in the `x ≥ 1/2` branch.
-/

namespace PairGapBounds

noncomputable section

open Real
open PairGapCore

/-- The augmented octagonal fan area. -/
def g : ℝ := 6 * s - 5

/-- Tangent coefficient `sqrt(g / 3029)`. -/
def u : ℝ := Real.sqrt (g / 3029)

/-- The AM--GM coefficient in the quadrilateral branch. -/
def C4 : ℝ := 3 - s + 23 * u

/-- The AM--GM coefficient in the pentagonal branch. -/
def C5 : ℝ := (3 : ℝ) / 2 + 23 * u

lemma g_pos : 0 < g := by
  dsimp [g]
  nlinarith [s_lower]

lemma g_nonneg : 0 ≤ g := g_pos.le

lemma u_nonneg : 0 ≤ u := by
  dsimp [u]
  positivity

lemma u_sq : u ^ 2 = g / 3029 := by
  dsimp [u]
  exact Real.sq_sqrt (div_nonneg g_nonneg (by norm_num))

lemma p5_nonneg : 0 ≤ p5 := by
  dsimp [p5]
  positivity

lemma p8_nonneg : 0 ≤ p8 := by
  dsimp [p8]
  positivity

lemma p5_sq : p5 ^ 2 = 4 * A5 := by
  dsimp [p5]
  rw [mul_pow, Real.sq_sqrt A5_pos.le]
  ring

lemma p8_sq : p8 ^ 2 = 4 * A8 := by
  dsimp [p8]
  rw [mul_pow, Real.sq_sqrt A8_pos.le]
  ring

lemma p5_upper : p5 < (3914 : ℝ) / 1000 := by
  have hr :
      4 + 8 * ((70711 : ℝ) / 50000) < ((3914 : ℝ) / 1000) ^ 2 := by
    norm_num
  have hsq : 4 * A5 < ((3914 : ℝ) / 1000) ^ 2 := by
    dsimp [A5]
    nlinarith [s_upper]
  have hb : 0 < (3914 : ℝ) / 1000 := by norm_num
  nlinarith [p5_sq, p5_nonneg]

lemma p8_upper : p8 < (3641 : ℝ) / 1000 := by
  have hr :
      32 * (((70711 : ℝ) / 50000) - 1) < ((3641 : ℝ) / 1000) ^ 2 := by
    norm_num
  have hsq : 4 * A8 < ((3641 : ℝ) / 1000) ^ 2 := by
    dsimp [A8, d]
    nlinarith [s_upper]
  have hb : 0 < (3641 : ℝ) / 1000 := by norm_num
  nlinarith [p8_sq, p8_nonneg]

lemma u_lower : (106 : ℝ) / 3125 < u := by
  have hr :
      ((106 : ℝ) / 3125) ^ 2 <
        (6 * ((7071 : ℝ) / 5000) - 5) / 3029 := by
    norm_num
  have hsq : ((106 : ℝ) / 3125) ^ 2 < g / 3029 := by
    dsimp [g]
    nlinarith [s_lower]
  have hq : 0 < (106 : ℝ) / 3125 := by norm_num
  nlinarith [u_sq, u_nonneg]

lemma C4_lower : (118297 : ℝ) / 50000 < C4 := by
  dsimp [C4]
  nlinarith [s_upper, u_lower]

lemma C5_lower : (14251 : ℝ) / 6250 < C5 := by
  dsimp [C5]
  nlinarith [u_lower]

lemma C4_pos : 0 < C4 := by nlinarith [C4_lower]

lemma C5_pos : 0 < C5 := by nlinarith [C5_lower]

lemma root4_lower :
    (87 : ℝ) / 20 < 2 * Real.sqrt C4 * s := by
  have hC : 0 ≤ C4 := C4_pos.le
  have hsC : (Real.sqrt C4) ^ 2 = C4 := Real.sq_sqrt hC
  have hprod0 : 0 ≤ Real.sqrt C4 * s :=
    mul_nonneg (Real.sqrt_nonneg _) s_nonneg
  have hprodSq : (Real.sqrt C4 * s) ^ 2 = 2 * C4 := by
    rw [mul_pow, hsC, s_sq]
    ring
  have hr :
      ((87 : ℝ) / 40) ^ 2 < 2 * ((118297 : ℝ) / 50000) := by
    norm_num
  have hsq : ((87 : ℝ) / 40) ^ 2 < 2 * C4 := by
    nlinarith [C4_lower]
  have hhalf : (87 : ℝ) / 40 < Real.sqrt C4 * s := by
    have hq : 0 < (87 : ℝ) / 40 := by norm_num
    nlinarith
  nlinarith

lemma root5_lower :
    (427 : ℝ) / 100 < 2 * Real.sqrt C5 * s := by
  have hC : 0 ≤ C5 := C5_pos.le
  have hsC : (Real.sqrt C5) ^ 2 = C5 := Real.sq_sqrt hC
  have hprod0 : 0 ≤ Real.sqrt C5 * s :=
    mul_nonneg (Real.sqrt_nonneg _) s_nonneg
  have hprodSq : (Real.sqrt C5 * s) ^ 2 = 2 * C5 := by
    rw [mul_pow, hsC, s_sq]
    ring
  have hr :
      ((427 : ℝ) / 200) ^ 2 < 2 * ((14251 : ℝ) / 6250) := by
    norm_num
  have hsq : ((427 : ℝ) / 200) ^ 2 < 2 * C5 := by
    nlinarith [C5_lower]
  have hhalf : (427 : ℝ) / 200 < Real.sqrt C5 * s := by
    have hq : 0 < (427 : ℝ) / 200 := by norm_num
    nlinarith
  nlinarith

/-- Exact tangent estimate, after multiplication by `sqrt g`. -/
theorem tangent_product_lower (x : ℝ) (hx : (1 : ℝ) / 2 ≤ x) :
    (23 * x + 100) * u ≤
      Real.sqrt g * Real.sqrt (x ^ 2 + 4) := by
  have hlin : 0 ≤ 23 * x + 100 := by nlinarith
  have hxx : 0 ≤ x ^ 2 + 4 := by positivity
  have hR0 : 0 ≤ Real.sqrt (x ^ 2 + 4) := Real.sqrt_nonneg _
  have hleft0 : 0 ≤ (23 * x + 100) * u := mul_nonneg hlin u_nonneg
  have hright0 : 0 ≤ Real.sqrt g * Real.sqrt (x ^ 2 + 4) :=
    mul_nonneg (Real.sqrt_nonneg _) hR0
  have ht := PairGapLemma.tangent2325Identity x
  have hpoly : (23 * x + 100) ^ 2 ≤ 3029 * (x ^ 2 + 4) := by
    nlinarith [sq_nonneg (25 * x - 23)]
  have hdiv : (23 * x + 100) ^ 2 / 3029 ≤ x ^ 2 + 4 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3029)).2
    nlinarith
  have hsqrtg : (Real.sqrt g) ^ 2 = g := Real.sq_sqrt g_nonneg
  have hsqrtx : (Real.sqrt (x ^ 2 + 4)) ^ 2 = x ^ 2 + 4 :=
    Real.sq_sqrt hxx
  have hsquares :
      ((23 * x + 100) * u) ^ 2 ≤
        (Real.sqrt g * Real.sqrt (x ^ 2 + 4)) ^ 2 := by
    calc
      ((23 * x + 100) * u) ^ 2 =
          g * ((23 * x + 100) ^ 2 / 3029) := by
            rw [mul_pow, u_sq]
            ring
      _ ≤ g * (x ^ 2 + 4) :=
        mul_le_mul_of_nonneg_left hdiv g_nonneg
      _ = (Real.sqrt g * Real.sqrt (x ^ 2 + 4)) ^ 2 := by
        rw [mul_pow, hsqrtg, hsqrtx]
  nlinarith

/-- AM--GM in the exact normalization used by both branches. -/
theorem amgm_two_over_x (x C : ℝ) (hx : 0 < x) (hC : 0 ≤ C) :
    2 * Real.sqrt C * s ≤ 2 / x + C * x := by
  have hsC : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
  have hsq : 0 ≤ (Real.sqrt C * x - s) ^ 2 := sq_nonneg _
  have hmul :
      (2 * Real.sqrt C * s) * x ≤ 2 + C * x ^ 2 := by
    nlinarith [hsC, s_sq]
  have hright : (2 / x + C * x) * x = 2 + C * x ^ 2 := by
    field_simp [ne_of_gt hx]
  have hmul' :
      (2 * Real.sqrt C * s) * x ≤ (2 / x + C * x) * x := by
    rw [hright]
    exact hmul
  nlinarith

end

end PairGapBounds
