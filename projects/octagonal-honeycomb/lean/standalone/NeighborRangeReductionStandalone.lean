import OctagonBenchmarkStandalone

/-!
# Side-count reduction outside the interval certificate

Only quadrilateral and pentagonal cells can have negative net charge. A
triangular opposite cell and every opposite cell with at least ten sides have
so much affine structural reserve that the allocated `63/80` side share alone
pays the worst possible quadrilateral debt. Consequently the computer-assisted
local inequality is needed only for neighbor side counts four through nine.
-/

namespace NeighborRangeReductionStandalone

noncomputable section

open Real
open OctagonBase
open OctagonBenchmarkStandalone

def p3 : ℝ := 2 + 2 * s

def p7 : ℝ := 2 * Real.sqrt A7

def debt4 : ℝ := line 4 - A4

def isolatedLower (n : ℕ) : ℝ :=
  if n = 3 then p3
  else if n = 4 then 2 * Real.sqrt A4
  else if n = 5 then p5
  else if n = 6 then p6
  else if n = 7 then p7
  else p8

lemma A7_pos : 0 < A7 := by
  dsimp [A7]
  nlinarith [s_lower]

lemma p7_nonneg : 0 ≤ p7 := by
  dsimp [p7]
  positivity

lemma p7_sq : p7 ^ 2 = 4 * A7 := by
  dsimp [p7]
  rw [mul_pow, Real.sq_sqrt A7_pos.le]
  ring

lemma p7_lower : (37337 : ℝ) / 10000 < p7 := by
  have hsq : ((37337 : ℝ) / 10000) ^ 2 < 4 * A7 := by
    dsimp [A7]
    nlinarith [OctagonBenchmarkStandalone.s_lower_tight]
  have hq : 0 < (37337 : ℝ) / 10000 := by norm_num
  nlinarith [p7_sq, p7_nonneg]

lemma slope_lower : (9 : ℝ) / 100 < OctagonBenchmarkStandalone.slope := by
  unfold OctagonBenchmarkStandalone.slope
  nlinarith [p6_lower_tight, p8_upper_tight]

lemma slope_upper_tight : OctagonBenchmarkStandalone.slope < (23 : ℝ) / 250 := by
  unfold OctagonBenchmarkStandalone.slope
  nlinarith [p6_upper_tight, p8_lower_tight]

lemma slope_pos : 0 < OctagonBenchmarkStandalone.slope :=
  lt_trans (by norm_num) slope_lower

lemma p8_sub_line (n : ℕ) :
    p8 - line n = OctagonBenchmarkStandalone.slope * ((n : ℝ) - 8) := by
  unfold OctagonBenchmarkStandalone.line OctagonBenchmarkStandalone.slope
  ring

lemma line_three : line 3 = p6 + 3 * OctagonBenchmarkStandalone.slope := by
  unfold OctagonBenchmarkStandalone.line
  norm_num
  ring

lemma line_six : line 6 = p6 := by
  unfold OctagonBenchmarkStandalone.line
  norm_num

lemma line_seven : line 7 = (p6 + p8) / 2 := by
  unfold OctagonBenchmarkStandalone.line OctagonBenchmarkStandalone.slope
  norm_num
  ring

lemma p3_gt_line_three : line 3 < p3 := by
  rw [line_three]
  dsimp [p3]
  nlinarith [OctagonBenchmarkStandalone.s_lower_tight,
    p6_upper_tight, slope_upper_tight]

lemma p7_gt_line_seven : line 7 < p7 := by
  rw [line_seven]
  nlinarith [p7_lower, p6_upper_tight, p8_upper_tight]

lemma debt4_lt_nine_thousandths : debt4 < (9 : ℝ) / 1000 := by
  dsimp [debt4, A4]
  nlinarith [line4_upper]

/-- Under the isolated polygon lower bounds, a negative cell has four or five
sides. -/
theorem negative_cell_has_four_or_five_sides
    (n : ℕ) (P : ℝ) (hn : 3 ≤ n)
    (hiso : isolatedLower n ≤ P) (hneg : P < line n) :
    n = 4 ∨ n = 5 := by
  by_cases hn8 : 8 ≤ n
  · have hcast : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
    have hline : line n ≤ p8 := by
      rw [← sub_nonneg, p8_sub_line]
      exact mul_nonneg slope_pos.le (sub_nonneg.mpr hcast)
    have hiso8 : p8 ≤ P := by
      simpa [isolatedLower, show n ≠ 3 by omega, show n ≠ 4 by omega,
        show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega]
        using hiso
    linarith
  · have hn7 : n ≤ 7 := by omega
    have hcases : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · have hp3 : p3 ≤ P := by simpa [isolatedLower] using hiso
      linarith [p3_gt_line_three]
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have hp6 : p6 ≤ P := by simpa [isolatedLower] using hiso
      rw [line_six] at hneg
      linarith
    · have hp7 : p7 ≤ P := by simpa [isolatedLower] using hiso
      linarith [p7_gt_line_seven]

/-- A triangular neighbor's allocated side reserve alone pays the worst owner
charge. -/
theorem triangular_neighbor_reserve_pays
    (r : ℝ) (hr : p3 - line 3 ≤ r) :
    debt4 < ((63 : ℝ) / (80 * 3)) * r := by
  have hsurplus : (3519 : ℝ) / 5000 < p3 - line 3 := by
    rw [line_three]
    dsimp [p3]
    nlinarith [OctagonBenchmarkStandalone.s_lower_tight,
      p6_upper_tight, slope_upper_tight]
  have hr' : (3519 : ℝ) / 5000 < r := lt_of_lt_of_le hsurplus hr
  nlinarith [debt4_lt_nine_thousandths]

/-- Every neighbor with at least ten sides has enough affine reserve per side
without invoking the interval certificate. -/
theorem large_neighbor_reserve_pays
    (n : ℕ) (r : ℝ) (hn : 10 ≤ n)
    (hr : p8 - line n ≤ r) :
    debt4 < ((63 : ℝ) / (80 * (n : ℝ))) * r := by
  have hnR : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hratio : (1 : ℝ) / 5 ≤ ((n : ℝ) - 8) / (n : ℝ) := by
    apply (le_div_iff₀ hnpos).2
    nlinarith
  have hratioPos : 0 < ((n : ℝ) - 8) / (n : ℝ) := by nlinarith
  have hprod :
      ((1 : ℝ) / 5) * ((9 : ℝ) / 100) <
        (((n : ℝ) - 8) / (n : ℝ)) * OctagonBenchmarkStandalone.slope := by
    calc
      ((1 : ℝ) / 5) * ((9 : ℝ) / 100) ≤
          (((n : ℝ) - 8) / (n : ℝ)) * ((9 : ℝ) / 100) :=
        mul_le_mul_of_nonneg_right hratio (by norm_num)
      _ < (((n : ℝ) - 8) / (n : ℝ)) * OctagonBenchmarkStandalone.slope :=
        mul_lt_mul_of_pos_left slope_lower hratioPos
  have hidentity :
      ((63 : ℝ) / (80 * (n : ℝ))) * (p8 - line n) =
        ((63 : ℝ) / 80) *
          ((((n : ℝ) - 8) / (n : ℝ)) * OctagonBenchmarkStandalone.slope) := by
    rw [p8_sub_line]
    field_simp [ne_of_gt hnpos]
  have hsurplus :
      (567 : ℝ) / 40000 <
        ((63 : ℝ) / (80 * (n : ℝ))) * (p8 - line n) := by
    rw [hidentity]
    have hm := mul_lt_mul_of_pos_left hprod
      (by norm_num : (0 : ℝ) < 63 / 80)
    norm_num at hm ⊢
    exact hm
  have hcoef : 0 < (63 : ℝ) / (80 * (n : ℝ)) := by positivity
  have hreplace :
      ((63 : ℝ) / (80 * (n : ℝ))) * (p8 - line n) ≤
        ((63 : ℝ) / (80 * (n : ℝ))) * r :=
    mul_le_mul_of_nonneg_left hr hcoef.le
  nlinarith [debt4_lt_nine_thousandths]

end

end NeighborRangeReductionStandalone
