import OctagonBase

/-!
# Affine benchmark and negative-cell thresholds

These are the exact constants used by the regular-octagon honeycomb ledger.
The rational brackets are deliberately modest but strong enough to separate
the phase-classification margins.
-/

namespace OctagonBenchmarkStandalone

noncomputable section

open Real
open OctagonBase

def A4 : ℝ := 4

def A5 : ℝ := 1 + 2 * s

def A6 : ℝ := 4 * s - 2

def A7 : ℝ := 6 * s - 5

def A8 : ℝ := 8 * d

def p5 : ℝ := 2 * Real.sqrt A5

def p6 : ℝ := 2 * Real.sqrt A6

def p8 : ℝ := 2 * Real.sqrt A8

def slope : ℝ := (p6 - p8) / 2

def line (n : ℕ) : ℝ := p6 - slope * ((n : ℝ) - 6)

def eta4 : ℝ := (line 4 / 2) ^ 2 - A4

def eta5 : ℝ := (line 5 / 2) ^ 2 - A5

lemma s_lower_tight : (14142135 : ℝ) / 10000000 < s := by
  have hrat : ((14142135 : ℝ) / 10000000) ^ 2 < 2 := by norm_num
  nlinarith [s_sq, s_nonneg]

lemma s_upper_tighter : s < (14142136 : ℝ) / 10000000 := by
  have hrat : 2 < ((14142136 : ℝ) / 10000000) ^ 2 := by norm_num
  nlinarith [s_sq, s_nonneg]

lemma A5_pos : 0 < A5 := by
  dsimp [A5]
  nlinarith [s_pos]

lemma A6_pos : 0 < A6 := by
  dsimp [A6]
  nlinarith [s_lower]

lemma A8_pos : 0 < A8 := by
  dsimp [A8]
  nlinarith [d_pos]

lemma p5_nonneg : 0 ≤ p5 := by
  dsimp [p5]
  positivity

lemma p6_nonneg : 0 ≤ p6 := by
  dsimp [p6]
  positivity

lemma p8_nonneg : 0 ≤ p8 := by
  dsimp [p8]
  positivity

lemma p5_sq : p5 ^ 2 = 4 * A5 := by
  dsimp [p5]
  rw [mul_pow, Real.sq_sqrt A5_pos.le]
  ring

lemma p6_sq : p6 ^ 2 = 4 * A6 := by
  dsimp [p6]
  rw [mul_pow, Real.sq_sqrt A6_pos.le]
  ring

lemma p8_sq : p8 ^ 2 = 4 * A8 := by
  dsimp [p8]
  rw [mul_pow, Real.sq_sqrt A8_pos.le]
  ring

lemma p6_lower_tight : (382458 : ℝ) / 100000 < p6 := by
  have hsq : ((382458 : ℝ) / 100000) ^ 2 < 4 * A6 := by
    dsimp [A6]
    nlinarith [s_lower_tight]
  have hq : 0 < (382458 : ℝ) / 100000 := by norm_num
  nlinarith [p6_sq, p6_nonneg]

lemma p6_upper_tight : p6 < (382459 : ℝ) / 100000 := by
  have hsq : 4 * A6 < ((382459 : ℝ) / 100000) ^ 2 := by
    dsimp [A6]
    nlinarith [s_upper_tighter]
  have hq : 0 < (382459 : ℝ) / 100000 := by norm_num
  nlinarith [p6_sq, p6_nonneg]

lemma p8_lower_tight : (364071 : ℝ) / 100000 < p8 := by
  have hsq : ((364071 : ℝ) / 100000) ^ 2 < 4 * A8 := by
    dsimp [A8, d]
    nlinarith [s_lower_tight]
  have hq : 0 < (364071 : ℝ) / 100000 := by norm_num
  nlinarith [p8_sq, p8_nonneg]

lemma p8_upper_tight : p8 < (364072 : ℝ) / 100000 := by
  have hsq : 4 * A8 < ((364072 : ℝ) / 100000) ^ 2 := by
    dsimp [A8, d]
    nlinarith [s_upper_tighter]
  have hq : 0 < (364072 : ℝ) / 100000 := by norm_num
  nlinarith [p8_sq, p8_nonneg]

lemma p5_upper : p5 < (3914 : ℝ) / 1000 := by
  have hsq : 4 * A5 < ((3914 : ℝ) / 1000) ^ 2 := by
    dsimp [A5]
    nlinarith [s_upper_tighter]
  have hq : 0 < (3914 : ℝ) / 1000 := by norm_num
  nlinarith [p5_sq, p5_nonneg]

lemma line_four : line 4 = 2 * p6 - p8 := by
  dsimp [line, slope]
  norm_num
  ring

lemma line_five : line 5 = (3 * p6 - p8) / 2 := by
  dsimp [line, slope]
  norm_num
  ring

lemma line4_pos : 0 < line 4 := by
  rw [line_four]
  nlinarith [p6_lower_tight, p8_upper_tight]

lemma line5_pos : 0 < line 5 := by
  rw [line_five]
  nlinarith [p6_lower_tight, p8_upper_tight]

lemma line4_gt_four : 4 < line 4 := by
  rw [line_four]
  nlinarith [p6_lower_tight, p8_upper_tight]

lemma line5_gt_p5 : p5 < line 5 := by
  rw [line_five]
  nlinarith [p5_upper, p6_lower_tight, p8_upper_tight]

lemma line4_upper : line 4 < (400847 : ℝ) / 100000 := by
  rw [line_four]
  nlinarith [p6_upper_tight, p8_lower_tight]

lemma line5_upper : line 5 < (391653 : ℝ) / 100000 := by
  rw [line_five]
  nlinarith [p6_upper_tight, p8_lower_tight]

lemma eta4_nonneg : 0 ≤ eta4 := by
  have hhalf : 2 ≤ line 4 / 2 := by nlinarith [line4_gt_four]
  have hsum : 0 ≤ line 4 / 2 + 2 := by nlinarith [line4_pos]
  have hp := mul_nonneg (sub_nonneg.mpr hhalf) hsum
  dsimp [eta4, A4]
  nlinarith

lemma eta5_nonneg : 0 ≤ eta5 := by
  have hhalf : p5 / 2 ≤ line 5 / 2 := by nlinarith [line5_gt_p5]
  have hsum : 0 ≤ line 5 / 2 + p5 / 2 := by
    nlinarith [line5_pos, p5_nonneg]
  have hp := mul_nonneg (sub_nonneg.mpr hhalf) hsum
  dsimp [eta5]
  nlinarith [p5_sq]

lemma eta4_lt_seventeen_thousandths : eta4 < (17 : ℝ) / 1000 := by
  have hhalf : line 4 / 2 < (400847 : ℝ) / 200000 := by
    nlinarith [line4_upper]
  have hsum : 0 < (400847 : ℝ) / 200000 + line 4 / 2 := by
    nlinarith [line4_pos]
  have hp := mul_pos (sub_pos.mpr hhalf) hsum
  dsimp [eta4, A4]
  nlinarith

lemma eta5_lt_four_625 : eta5 < (4 : ℝ) / 625 := by
  have hhalf : line 5 / 2 < (391653 : ℝ) / 200000 := by
    nlinarith [line5_upper]
  have hsum : 0 < (391653 : ℝ) / 200000 + line 5 / 2 := by
    nlinarith [line5_pos]
  have hp := mul_pos (sub_pos.mpr hhalf) hsum
  dsimp [eta5, A5]
  nlinarith [s_lower_tight]

lemma A4_eta4_sq : A4 + eta4 = (line 4 / 2) ^ 2 := by
  dsimp [eta4]
  ring

lemma A5_eta5_sq : A5 + eta5 = (line 5 / 2) ^ 2 := by
  dsimp [eta5]
  ring

end

end OctagonBenchmarkStandalone
