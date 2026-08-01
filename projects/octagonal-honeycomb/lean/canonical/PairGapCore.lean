import Mathlib
import PairGapLemma

/-! Core constants and the first square-root inequality for the pair-gap proof. -/

namespace PairGapCore

noncomputable section

open Real

def s : ℝ := Real.sqrt 2

def d : ℝ := s - 1

def A5 : ℝ := 1 + 2 * s

def A8 : ℝ := 8 * d

def p5 : ℝ := 2 * Real.sqrt A5

def p8 : ℝ := 2 * Real.sqrt A8

def r4 (x : ℝ) : ℝ := 2 / x + 2 * x - 4

def r5 (x : ℝ) : ℝ := 2 / x + (A5 / 2) * x - p5

def h (x f : ℝ) : ℝ :=
  Real.sqrt (f + d ^ 2) * Real.sqrt (x ^ 2 + 4) - d * x - 2 * Real.sqrt f

lemma s_sq : s ^ 2 = 2 := by
  dsimp [s]
  norm_num

lemma s_nonneg : 0 ≤ s := by
  dsimp [s]
  positivity

lemma s_pos : 0 < s := by
  dsimp [s]
  positivity

lemma s_lower : (7071 : ℝ) / 5000 < s := by
  have hs := s_sq
  have hs0 := s_nonneg
  norm_num at hs0 ⊢
  nlinarith [show ((7071 : ℝ) / 5000) ^ 2 < 2 by norm_num]

lemma s_upper : s < (70711 : ℝ) / 50000 := by
  have hs := s_sq
  have hs0 := s_nonneg
  norm_num at hs0 ⊢
  nlinarith [show 2 < ((70711 : ℝ) / 50000) ^ 2 by norm_num]

lemma d_pos : 0 < d := by
  dsimp [d]
  nlinarith [s_lower]

lemma d_nonneg : 0 ≤ d := d_pos.le

lemma d_lt_half : d < (1 : ℝ) / 2 := by
  dsimp [d]
  nlinarith [s_upper]

lemma A5_pos : 0 < A5 := by
  dsimp [A5]
  nlinarith [s_pos]

lemma A8_pos : 0 < A8 := by
  dsimp [A8]
  nlinarith [d_pos]

lemma fanAugment : A8 + d ^ 2 = 6 * s - 5 := by
  dsimp [A8, d]
  nlinarith [s_sq]

/-- Exact nonnegativity of the HH excess term. -/
theorem h_nonneg (x f : ℝ) (hx : 0 ≤ x) (hf : 0 ≤ f) : 0 ≤ h x f := by
  let U := Real.sqrt (f + d ^ 2) * Real.sqrt (x ^ 2 + 4)
  let V := d * x + 2 * Real.sqrt f
  have hfd : 0 ≤ f + d ^ 2 := by positivity
  have hxx : 0 ≤ x ^ 2 + 4 := by positivity
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V]
    exact add_nonneg (mul_nonneg d_nonneg hx)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg f))
  have hU2 : U ^ 2 = (f + d ^ 2) * (x ^ 2 + 4) := by
    dsimp [U]
    rw [mul_pow, Real.sq_sqrt hfd, Real.sq_sqrt hxx]
  have hV2 : V ^ 2 = (d * x + 2 * Real.sqrt f) ^ 2 := rfl
  have hsqrtf : (Real.sqrt f) ^ 2 = f := Real.sq_sqrt hf
  have hid := PairGapLemma.hSquareIdentity x (Real.sqrt f) d
  rw [hsqrtf] at hid
  have hgap : 0 ≤ U ^ 2 - V ^ 2 := by
    rw [hU2, hV2]
    have hsquare : 0 ≤ (x * Real.sqrt f - 2 * d) ^ 2 := sq_nonneg _
    nlinarith [hid]
  have hUV : V ≤ U := by nlinarith
  dsimp [h, U, V] at hUV ⊢
  linarith

end

end PairGapCore
