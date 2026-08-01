import PairGapBounds
import DangerousPatterns

/-!
# Exhaustion of the noncrystalline interval-certificate domains

This module proves the elementary interface between the geometric stability
classification and the root boxes used by the noncrystalline interval verifier.
Angles are normalized by `π`, so one full turn is `2`.

The analytic phase-snapping theorem supplies the broad dangerous-cell windows:

* a negative quadrilateral has all four turns in `(79/180, 92/180)`;
* a negative pentagon has exactly three high turns in `(87/180, 91/180)`.

The theorems below show that one may select an owner edge whose two turns lie
in the tighter verifier boxes, that the two opposite-cell turns then lie in
`[0, 0.54]`, and that the common edge length lies below `4.10`. They also
remove triangular and `10+`-sided neighbors from the interval calculation.
-/

namespace NoncrystallineDomainReduction

noncomputable section

open Real
open PairGapCore
open PairGapBounds

def A6 : ℝ := 4 * s - 2

def A7 : ℝ := 6 * s - 5

def p6 : ℝ := 2 * Real.sqrt A6

def p7 : ℝ := 2 * Real.sqrt A7

def p3 : ℝ := 2 + 2 * s

def slope : ℝ := (p6 - p8) / 2

def line (n : ℕ) : ℝ := p6 - slope * ((n : ℝ) - 6)

def debt4 : ℝ := line 4 - 4

def isolatedLower (n : ℕ) : ℝ :=
  if n = 3 then p3
  else if n = 4 then 4
  else if n = 5 then p5
  else if n = 6 then p6
  else if n = 7 then p7
  else p8

lemma A6_pos : 0 < A6 := by
  dsimp [A6]
  nlinarith [s_lower]

lemma A7_pos : 0 < A7 := by
  dsimp [A7]
  nlinarith [s_lower]

lemma p6_nonneg : 0 ≤ p6 := by
  dsimp [p6]
  positivity

lemma p7_nonneg : 0 ≤ p7 := by
  dsimp [p7]
  positivity

lemma p6_sq : p6 ^ 2 = 4 * A6 := by
  dsimp [p6]
  rw [mul_pow, Real.sq_sqrt A6_pos.le]
  ring

lemma p7_sq : p7 ^ 2 = 4 * A7 := by
  dsimp [p7]
  rw [mul_pow, Real.sq_sqrt A7_pos.le]
  ring

lemma p6_lower : (478 : ℝ) / 125 < p6 := by
  have hsq : ((478 : ℝ) / 125) ^ 2 < 4 * A6 := by
    dsimp [A6]
    nlinarith [s_lower]
  have hq : 0 < (478 : ℝ) / 125 := by norm_num
  nlinarith [p6_sq, p6_nonneg]

lemma p6_upper : p6 < (19123 : ℝ) / 5000 := by
  have hsq : 4 * A6 < ((19123 : ℝ) / 5000) ^ 2 := by
    dsimp [A6]
    nlinarith [s_upper]
  have hq : 0 < (19123 : ℝ) / 5000 := by norm_num
  nlinarith [p6_sq, p6_nonneg]

lemma s_lower_tight : (141421 : ℝ) / 100000 < s := by
  have hs := s_sq
  have hs0 := s_nonneg
  have hrat : ((141421 : ℝ) / 100000) ^ 2 < 2 := by norm_num
  have hq : 0 < (141421 : ℝ) / 100000 := by norm_num
  nlinarith

lemma p8_lower : (36407 : ℝ) / 10000 < p8 := by
  have hsq : ((36407 : ℝ) / 10000) ^ 2 < 4 * A8 := by
    dsimp [A8, d]
    nlinarith [s_lower_tight]
  have hq : 0 < (36407 : ℝ) / 10000 := by norm_num
  nlinarith [p8_sq, p8_nonneg]

lemma p7_lower : (37337 : ℝ) / 10000 < p7 := by
  have hsq : ((37337 : ℝ) / 10000) ^ 2 < 4 * A7 := by
    dsimp [A7]
    nlinarith [s_lower]
  have hq : 0 < (37337 : ℝ) / 10000 := by norm_num
  nlinarith [p7_sq, p7_nonneg]

lemma slope_lower : (9 : ℝ) / 100 < slope := by
  dsimp [slope]
  nlinarith [p6_lower, p8_upper]

lemma slope_upper : slope < (1 : ℝ) / 10 := by
  dsimp [slope]
  nlinarith [p6_upper, p8_lower]

lemma slope_pos : 0 < slope := by nlinarith [slope_lower]

lemma p8_sub_line (n : ℕ) : p8 - line n = slope * ((n : ℝ) - 8) := by
  dsimp [line, slope]
  ring

lemma line_four : line 4 = 2 * p6 - p8 := by
  dsimp [line, slope]
  norm_num
  ring

lemma line_five : line 5 = (3 * p6 - p8) / 2 := by
  dsimp [line, slope]
  norm_num
  ring

lemma line_six : line 6 = p6 := by simp [line]

lemma line_seven : line 7 = (p6 + p8) / 2 := by
  dsimp [line, slope]
  norm_num
  ring

lemma line_three : line 3 = p6 + 3 * slope := by
  dsimp [line]
  norm_num
  ring

lemma debt4_lt_nine_thousandths : debt4 < (9 : ℝ) / 1000 := by
  rw [debt4, line_four]
  nlinarith [p6_upper, p8_lower]

lemma line_four_lt_root_cutoff : line 4 < (41 : ℝ) / 5 := by
  rw [line_four]
  nlinarith [p6_upper, p8_lower]

lemma line_five_lt_root_cutoff : line 5 < (41 : ℝ) / 5 := by
  rw [line_five]
  nlinarith [p6_upper, p8_lower]

lemma p3_gt_line_three : line 3 < p3 := by
  rw [line_three]
  dsimp [p3]
  nlinarith [s_lower, p6_upper, slope_upper]

lemma p7_gt_line_seven : line 7 < p7 := by
  rw [line_seven]
  nlinarith [p7_lower, p6_upper, p8_upper]

theorem negative_cell_has_four_or_five_sides
    (n : ℕ) (P : ℝ) (hn : 3 ≤ n)
    (hiso : isolatedLower n ≤ P) (hneg : P < line n) :
    n = 4 ∨ n = 5 := by
  by_cases hn8 : 8 ≤ n
  · have hline : line n ≤ p8 := by
      have hcast : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
      have hnonneg : 0 ≤ slope * ((n : ℝ) - 8) :=
        mul_nonneg slope_pos.le (sub_nonneg.mpr hcast)
      rw [← sub_nonneg, p8_sub_line]
      exact hnonneg
    have hiso8 : p8 ≤ P := by
      simp [isolatedLower, show n ≠ 3 by omega, show n ≠ 4 by omega,
        show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega] at hiso
      exact hiso
    linarith
  · have hn7 : n ≤ 7 := by omega
    have hcases : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hcases with h3 | h4 | h5 | h6 | h7
    · subst n
      have hp3 : p3 ≤ P := by simpa [isolatedLower] using hiso
      linarith [p3_gt_line_three]
    · subst n
      exact Or.inl rfl
    · subst n
      exact Or.inr rfl
    · subst n
      have hp6 : p6 ≤ P := by simpa [isolatedLower] using hiso
      rw [line_six] at hneg
      linarith
    · subst n
      have hp7 : p7 ≤ P := by simpa [isolatedLower] using hiso
      linarith [p7_gt_line_seven]

def quadRootLo : ℝ := 23 / 50

def quadRootHi : ℝ := 53 / 100

def pentRootLo : ℝ := 47 / 100

def pentRootHi : ℝ := 13 / 25

def neighborRootHi : ℝ := 27 / 50

theorem quadrilateral_has_root_edge
    (a0 a1 a2 a3 : ℝ)
    (hsum : a0 + a1 + a2 + a3 = 2)
    (hu0 : a0 < (23 : ℝ) / 45) (hu1 : a1 < (23 : ℝ) / 45)
    (hu2 : a2 < (23 : ℝ) / 45) (hu3 : a3 < (23 : ℝ) / 45) :
    ((quadRootLo ≤ a0 ∧ a0 ≤ quadRootHi) ∧
      (quadRootLo ≤ a1 ∧ a1 ≤ quadRootHi)) ∨
    ((quadRootLo ≤ a1 ∧ a1 ≤ quadRootHi) ∧
      (quadRootLo ≤ a2 ∧ a2 ≤ quadRootHi)) ∨
    ((quadRootLo ≤ a2 ∧ a2 ≤ quadRootHi) ∧
      (quadRootLo ≤ a3 ∧ a3 ≤ quadRootHi)) ∨
    ((quadRootLo ≤ a3 ∧ a3 ≤ quadRootHi) ∧
      (quadRootLo ≤ a0 ∧ a0 ≤ quadRootHi)) := by
  have hupper0 : a0 ≤ quadRootHi := by dsimp [quadRootHi]; nlinarith
  have hupper1 : a1 ≤ quadRootHi := by dsimp [quadRootHi]; nlinarith
  have hupper2 : a2 ≤ quadRootHi := by dsimp [quadRootHi]; nlinarith
  have hupper3 : a3 ≤ quadRootHi := by dsimp [quadRootHi]; nlinarith
  by_cases h0 : quadRootLo ≤ a0
  · by_cases h1 : quadRootLo ≤ a1
    · exact Or.inl ⟨⟨h0, hupper0⟩, ⟨h1, hupper1⟩⟩
    · by_cases h3 : quadRootLo ≤ a3
      · exact Or.inr (Or.inr (Or.inr ⟨⟨h3, hupper3⟩, ⟨h0, hupper0⟩⟩))
      · have h1' : a1 < quadRootLo := lt_of_not_ge h1
        have h3' : a3 < quadRootLo := lt_of_not_ge h3
        dsimp [quadRootLo] at h1' h3'
        nlinarith
  · have h0' : a0 < quadRootLo := lt_of_not_ge h0
    by_cases h2 : quadRootLo ≤ a2
    · by_cases h1 : quadRootLo ≤ a1
      · exact Or.inr (Or.inl ⟨⟨h1, hupper1⟩, ⟨h2, hupper2⟩⟩)
      · by_cases h3 : quadRootLo ≤ a3
        · exact Or.inr (Or.inr (Or.inl ⟨⟨h2, hupper2⟩, ⟨h3, hupper3⟩⟩))
        · have h0'' : a0 < (23 : ℝ) / 50 := by simpa [quadRootLo] using h0'
          have h1' : a1 < (23 : ℝ) / 50 := by
            simpa [quadRootLo] using lt_of_not_ge h1
          have h3' : a3 < (23 : ℝ) / 50 := by
            simpa [quadRootLo] using lt_of_not_ge h3
          nlinarith
    · have h0'' : a0 < (23 : ℝ) / 50 := by simpa [quadRootLo] using h0'
      have h2' : a2 < (23 : ℝ) / 50 := by
        simpa [quadRootLo] using lt_of_not_ge h2
      nlinarith

theorem pentagon_has_root_edge
    (turn : Fin 5 → ℝ) (high : Fin 5 → Bool)
    (hcount : ((Finset.univ.filter fun i => high i = true).card = 3))
    (hwindow : ∀ i, high i = true →
      (87 : ℝ) / 180 < turn i ∧ turn i < (91 : ℝ) / 180) :
    ∃ i,
      (pentRootLo ≤ turn i ∧ turn i ≤ pentRootHi) ∧
      (pentRootLo ≤ turn (DangerousPatterns.next5 i) ∧
        turn (DangerousPatterns.next5 i) ≤ pentRootHi) := by
  obtain ⟨i, hi, hnext⟩ :=
    DangerousPatterns.three_marks_have_adjacent high hcount
  refine ⟨i, ?_, ?_⟩
  · have hw := hwindow i hi
    constructor <;> dsimp [pentRootLo, pentRootHi] <;> nlinarith
  · have hw := hwindow (DangerousPatterns.next5 i) hnext
    constructor <;> dsimp [pentRootLo, pentRootHi] <;> nlinarith

theorem opposite_turn_in_root
    (owner opposite third : ℝ)
    (howner : quadRootLo ≤ owner)
    (hopposite : 0 ≤ opposite) (hthird : 0 ≤ third)
    (hsum : owner + opposite + third = 1) :
    0 ≤ opposite ∧ opposite ≤ neighborRootHi := by
  refine ⟨hopposite, ?_⟩
  dsimp [quadRootLo, neighborRootHi] at howner ⊢
  linarith

theorem negative_owner_edge_length_in_root
    (n : ℕ) (P x : ℝ) (hn : n = 4 ∨ n = 5)
    (htwox : 2 * x ≤ P) (hneg : P < line n) :
    x < (41 : ℝ) / 10 := by
  rcases hn with rfl | rfl
  · nlinarith [line_four_lt_root_cutoff]
  · nlinarith [line_five_lt_root_cutoff]

theorem triangular_neighbor_reserve_pays
    (r : ℝ) (hr : p3 - line 3 ≤ r) :
    debt4 < ((63 : ℝ) / (80 * 3)) * r := by
  have hsurplus : (3519 : ℝ) / 5000 < p3 - line 3 := by
    rw [line_three]
    dsimp [p3]
    nlinarith [s_lower, p6_upper, slope_upper]
  have hr' : (3519 : ℝ) / 5000 < r := lt_of_lt_of_le hsurplus hr
  have hdebt := debt4_lt_nine_thousandths
  nlinarith

theorem large_neighbor_reserve_pays
    (n : ℕ) (r : ℝ) (hn : 10 ≤ n)
    (hr : p8 - line n ≤ r) :
    debt4 < ((63 : ℝ) / (80 * (n : ℝ))) * r := by
  have hnR : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hratio : (1 : ℝ) / 5 ≤ ((n : ℝ) - 8) / (n : ℝ) := by
    apply (le_div_iff₀ hnpos).2
    nlinarith
  have hratioPos : 0 < ((n : ℝ) - 8) / (n : ℝ) := by
    nlinarith
  have hprod1 :
      ((1 : ℝ) / 5) * ((9 : ℝ) / 100) <
        (((n : ℝ) - 8) / (n : ℝ)) * slope := by
    calc
      ((1 : ℝ) / 5) * ((9 : ℝ) / 100) ≤
          (((n : ℝ) - 8) / (n : ℝ)) * ((9 : ℝ) / 100) :=
        mul_le_mul_of_nonneg_right hratio (by norm_num)
      _ < (((n : ℝ) - 8) / (n : ℝ)) * slope :=
        mul_lt_mul_of_pos_left slope_lower hratioPos
  have hsurplus :
      (567 : ℝ) / 40000 <
        ((63 : ℝ) / (80 * (n : ℝ))) * (p8 - line n) := by
    rw [p8_sub_line]
    have hid :
        ((63 : ℝ) / (80 * (n : ℝ))) *
            (slope * ((n : ℝ) - 8)) =
          ((63 : ℝ) / 80) *
            ((((n : ℝ) - 8) / (n : ℝ)) * slope) := by
      field_simp [ne_of_gt hnpos]
    rw [hid]
    have hm := mul_lt_mul_of_pos_left hprod1 (by norm_num : (0 : ℝ) < 63 / 80)
    norm_num at hm ⊢
    exact hm
  have hcoef : 0 < (63 : ℝ) / (80 * (n : ℝ)) := by positivity
  have hreplace :
      ((63 : ℝ) / (80 * (n : ℝ))) * (p8 - line n) ≤
        ((63 : ℝ) / (80 * (n : ℝ))) * r :=
    mul_le_mul_of_nonneg_left hr hcoef.le
  have hdebt := debt4_lt_nine_thousandths
  nlinarith

end

end NoncrystallineDomainReduction
