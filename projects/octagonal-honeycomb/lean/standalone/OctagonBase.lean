import Mathlib

/-!
# Shared exact constants for the octagonal phase calculation
-/

namespace OctagonBase

noncomputable section

open Real

def s : ℝ := Real.sqrt 2

def d : ℝ := s - 1

def c : ℝ := 2 - s

def cap : ℝ := d ^ 2

def phaseSlope : ℝ := 4 * (2 - s)

def wedge (alpha h k : ℝ) : ℝ :=
  h * k / Real.sin alpha -
    (h ^ 2 + k ^ 2) * Real.cos alpha / (2 * Real.sin alpha)

def sectorMinimum (alpha beta : ℝ) : ℝ :=
  wedge alpha 1 (Real.cos beta + d * Real.sin beta)

lemma s_sq : s ^ 2 = 2 := by
  dsimp [s]
  norm_num

lemma s_nonneg : 0 ≤ s := by
  dsimp [s]
  positivity

lemma s_pos : 0 < s := by
  dsimp [s]
  positivity

lemma s_lower : (7 : ℝ) / 5 < s := by
  have hrat : ((7 : ℝ) / 5) ^ 2 < 2 := by norm_num
  nlinarith [s_sq, s_nonneg]

lemma s_lower_tight : (141421 : ℝ) / 100000 < s := by
  have hrat : ((141421 : ℝ) / 100000) ^ 2 < 2 := by norm_num
  nlinarith [s_sq, s_nonneg]

lemma s_upper : s < (3 : ℝ) / 2 := by
  have hrat : 2 < ((3 : ℝ) / 2) ^ 2 := by norm_num
  nlinarith [s_sq, s_nonneg]

lemma s_upper_tight : s < (70711 : ℝ) / 50000 := by
  have hrat : 2 < ((70711 : ℝ) / 50000) ^ 2 := by norm_num
  nlinarith [s_sq, s_nonneg]

lemma d_pos : 0 < d := by
  dsimp [d]
  nlinarith [s_lower]

lemma d_nonneg : 0 ≤ d := d_pos.le

lemma c_pos : 0 < c := by
  dsimp [c]
  nlinarith [s_upper]

lemma c_nonneg : 0 ≤ c := c_pos.le

lemma c_eq_one_sub_d : c = 1 - d := by
  dsimp [c, d]
  ring

lemma d_quadratic : d ^ 2 + 2 * d = 1 := by
  dsimp [d]
  nlinarith [s_sq]

lemma cap_nonneg : 0 ≤ cap := by
  dsimp [cap]
  positivity

lemma phaseSlope_pos : 0 < phaseSlope := by
  dsimp [phaseSlope]
  nlinarith [s_upper]

end

end OctagonBase
