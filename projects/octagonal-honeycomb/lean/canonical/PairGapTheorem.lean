import PairGapBounds

/-!
# Full crystalline pair-gap theorem

This file combines the small-edge factorization, the fan-area monotonicity, and
the exact large-edge estimates.  Its final theorem is the strengthened form of
Lemma 4 used by the crystalline discharging argument.
-/

namespace PairGapTheorem

noncomputable section

open Real
open PairGapCore
open PairGapMonotone
open PairGapBounds

/-- In the small-edge range, the quadrilateral RR excess alone is at least one. -/
lemma small_r4 (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ (1 : ℝ) / 2) :
    1 ≤ r4 x := by
  have h1 : 2 * x - 1 ≤ 0 := by linarith
  have h2 : x - 2 ≤ 0 := by linarith
  have hprod : 0 ≤ (2 * x - 1) * (x - 2) :=
    mul_nonneg_of_nonpos_of_nonpos h1 h2
  have hid := PairGapLemma.smallR4Identity x (ne_of_gt hx)
  have hxmul : 0 ≤ x * (r4 x - 1) := by
    have hform : x * (r4 x - 1) = x * (2 / x + 2 * x - 5) := by
      dsimp [r4]
      ring
    rw [hform, hid]
    exact hprod
  nlinarith

/-- In the same small-edge range, the pentagonal RR excess is even larger. -/
lemma small_r5_gt_r4 (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ (1 : ℝ) / 2) :
    r4 x < r5 x := by
  have hcoef : (2 * s - 3) / 2 < 0 := by
    nlinarith [s_upper]
  have hterm : (2 * s - 3) / 4 ≤ ((2 * s - 3) / 2) * x := by
    have hm := mul_le_mul_of_nonpos_left hxhalf hcoef.le
    nlinarith
  have hnum : 0 < (2 * s - 3) / 4 + 4 - p5 := by
    have hr :
        0 < (2 * ((7071 : ℝ) / 5000) - 3) / 4 + 4 -
          (3914 : ℝ) / 1000 := by
      norm_num
    nlinarith [s_lower, p5_upper]
  dsimp [r4, r5, A5]
  nlinarith

/-- Tangent plus the exact identities give the large-edge quadrilateral lower
comparison before inserting the numerical constants. -/
lemma large_four_comparison (x : ℝ) (hx : (1 : ℝ) / 2 ≤ x) :
    2 / x + C4 * x + 100 * u - 4 - p8 ≤ r4 x + h x A8 := by
  have ht := tangent_product_lower x hx
  dsimp [r4, h, C4, p8]
  rw [fanAugment]
  dsimp [g, d] at ht ⊢
  nlinarith

/-- The analogous large-edge pentagonal comparison. -/
lemma large_five_comparison (x : ℝ) (hx : (1 : ℝ) / 2 ≤ x) :
    2 / x + C5 * x + 100 * u - p5 - p8 ≤ r5 x + h x A8 := by
  have ht := tangent_product_lower x hx
  dsimp [r5, h, C5, p5, p8, A5]
  rw [fanAugment]
  dsimp [g, d] at ht ⊢
  nlinarith

/-- Exact numerical endgame for the quadrilateral branch. -/
lemma large_four_numeric (x : ℝ) (hx : 0 < x) :
    (101 : ℝ) / 1000 < 2 / x + C4 * x + 100 * u - 4 - p8 := by
  have hamgm := amgm_two_over_x x C4 hx C4_pos.le
  have hroot := root4_lower
  have hu := u_lower
  have hp := p8_upper
  nlinarith

/-- Exact numerical endgame for the pentagonal branch. -/
lemma large_five_numeric (x : ℝ) (hx : 0 < x) :
    (107 : ℝ) / 1000 < 2 / x + C5 * x + 100 * u - p5 - p8 := by
  have hamgm := amgm_two_over_x x C5 hx C5_pos.le
  have hroot := root5_lower
  have hu := u_lower
  have hp5 := p5_upper
  have hp8 := p8_upper
  nlinarith

/-- The strengthened quadrilateral pair gap. -/
theorem pair_gap_four (x f : ℝ) (hx : 0 < x) (hf : A8 ≤ f) :
    (101 : ℝ) / 1000 < r4 x + h x f := by
  by_cases hsmall : x ≤ (1 : ℝ) / 2
  · have hr := small_r4 x hx hsmall
    have hh := h_nonneg x f hx.le (le_trans A8_pos.le hf)
    have hq : (101 : ℝ) / 1000 < 1 := by norm_num
    linarith
  · have hxhalf : (1 : ℝ) / 2 ≤ x := le_of_not_ge hsmall
    have hm := h_mono_A8 x f hxhalf hf
    have hlower := large_four_comparison x hxhalf
    have hend := large_four_numeric x hx
    linarith

/-- The strengthened pentagonal pair gap, stated with the common `0.101`
constant used in the discharging argument. -/
theorem pair_gap_five (x f : ℝ) (hx : 0 < x) (hf : A8 ≤ f) :
    (101 : ℝ) / 1000 < r5 x + h x f := by
  by_cases hsmall : x ≤ (1 : ℝ) / 2
  · have hr4 := small_r4 x hx hsmall
    have hr5 := small_r5_gt_r4 x hx hsmall
    have hh := h_nonneg x f hx.le (le_trans A8_pos.le hf)
    have hq : (101 : ℝ) / 1000 < 1 := by norm_num
    linarith
  · have hxhalf : (1 : ℝ) / 2 ≤ x := le_of_not_ge hsmall
    have hm := h_mono_A8 x f hxhalf hf
    have hlower := large_five_comparison x hxhalf
    have hend := large_five_numeric x hx
    linarith

/-- Full strengthened Lemma 4. -/
theorem pair_gap_full (x f : ℝ) (hx : 0 < x) (hf : A8 ≤ f) :
    (101 : ℝ) / 1000 < r4 x + h x f ∧
      (101 : ℝ) / 1000 < r5 x + h x f :=
  ⟨pair_gap_four x f hx hf, pair_gap_five x f hx hf⟩

end

end PairGapTheorem
