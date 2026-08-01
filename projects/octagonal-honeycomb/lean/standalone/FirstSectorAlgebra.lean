import OctagonBase

/-!
# Exact algebraic certificates for the first large octagonal sector

The transcendental estimate is separated from two rational inequalities. Each
polynomial is written in Bernstein form on its interval, so positivity follows
from positive exact coefficients and nonnegative Bernstein basis functions.
-/

namespace FirstSectorAlgebra

noncomputable section

open OctagonBase

def firstLhs (t : ℝ) : ℝ :=
  d * t * (1 + t) / (1 + t ^ 2) + c ^ 2 * t / (1 + t)

def quintic (t : ℝ) : ℝ := t - t ^ 3 / 3 + t ^ 5 / 5

def cubic (t : ℝ) : ℝ := t - t ^ 3 / 3

def lowK : ℝ := 200 * c / 157

def highK : ℝ := 80 * c / 63

def lowPoly (t : ℝ) : ℝ :=
  (-240 + 120 * s) * t ^ 7 +
  (-240 + 120 * s) * t ^ 6 +
  (160 - 80 * s) * t ^ 5 +
  (160 - 80 * s) * t ^ 4 +
  (-800 + 400 * s) * t ^ 3 +
  (1555 - 1013 * s) * t ^ 2 +
  (-2142 + 1542 * s) * t +
  (1155 - 813 * s)

def highPoly (t : ℝ) : ℝ :=
  (-247 + 218 * s) * t ^ 4 +
  (335 - 73 * s) * t ^ 3 +
  (73 - 131 * s) * t ^ 2 +
  (713 - 451 * s) * t +
  (-58 + 29 * s)

def lowX (t : ℝ) : ℝ := 5 * t / 3

def highX (t : ℝ) : ℝ := (5 * t - 3) / 2

def u (t : ℝ) : ℝ := (1 - t) / (1 + t)

def lb0 : ℝ := 1155 - 813 * s
def lb1 : ℝ := 4857 / 5 - 23829 * s / 35
def lb2 : ℝ := 28506 / 35 - 99054 * s / 175
def lb3 : ℝ := 118866 / 175 - 16314 * s / 35
def lb4 : ℝ := 2456067 / 4375 - 1657821 * s / 4375
def lb5 : ℝ := 2002677 / 4375 - 1325151 * s / 4375
def lb6 : ℝ := 7992168 / 21875 - 5173584 * s / 21875
def lb7 : ℝ := 4250964 / 15625 - 2714232 * s / 15625

lemma lb0_pos : 0 < lb0 := by dsimp [lb0]; nlinarith [s_upper_tight]
lemma lb1_pos : 0 < lb1 := by dsimp [lb1]; nlinarith [s_upper_tight]
lemma lb2_pos : 0 < lb2 := by dsimp [lb2]; nlinarith [s_upper_tight]
lemma lb3_pos : 0 < lb3 := by dsimp [lb3]; nlinarith [s_upper_tight]
lemma lb4_pos : 0 < lb4 := by dsimp [lb4]; nlinarith [s_upper_tight]
lemma lb5_pos : 0 < lb5 := by dsimp [lb5]; nlinarith [s_upper_tight]
lemma lb6_pos : 0 < lb6 := by dsimp [lb6]; nlinarith [s_upper_tight]
lemma lb7_pos : 0 < lb7 := by dsimp [lb7]; nlinarith [s_upper_tight]

lemma low_bernstein_identity (t : ℝ) :
    lowPoly t =
      lb0 * (1 - lowX t) ^ 7 +
      7 * lb1 * lowX t * (1 - lowX t) ^ 6 +
      21 * lb2 * (lowX t) ^ 2 * (1 - lowX t) ^ 5 +
      35 * lb3 * (lowX t) ^ 3 * (1 - lowX t) ^ 4 +
      35 * lb4 * (lowX t) ^ 4 * (1 - lowX t) ^ 3 +
      21 * lb5 * (lowX t) ^ 5 * (1 - lowX t) ^ 2 +
      7 * lb6 * (lowX t) ^ 6 * (1 - lowX t) +
      lb7 * (lowX t) ^ 7 := by
  dsimp [lowPoly, lowX, lb0, lb1, lb2, lb3, lb4, lb5, lb6, lb7]
  ring

lemma lowPoly_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ (3 : ℝ) / 5) :
    0 ≤ lowPoly t := by
  have hx0 : 0 ≤ lowX t := by dsimp [lowX]; positivity
  have hx1 : lowX t ≤ 1 := by dsimp [lowX]; nlinarith
  have hy0 : 0 ≤ 1 - lowX t := sub_nonneg.mpr hx1
  have hb0 : 0 ≤ lb0 := lb0_pos.le
  have hb1 : 0 ≤ lb1 := lb1_pos.le
  have hb2 : 0 ≤ lb2 := lb2_pos.le
  have hb3 : 0 ≤ lb3 := lb3_pos.le
  have hb4 : 0 ≤ lb4 := lb4_pos.le
  have hb5 : 0 ≤ lb5 := lb5_pos.le
  have hb6 : 0 ≤ lb6 := lb6_pos.le
  have hb7 : 0 ≤ lb7 := lb7_pos.le
  rw [low_bernstein_identity]
  have h0 : 0 ≤ lb0 * (1 - lowX t) ^ 7 := by positivity
  have h1 : 0 ≤ 7 * lb1 * lowX t * (1 - lowX t) ^ 6 := by positivity
  have h2 : 0 ≤ 21 * lb2 * (lowX t) ^ 2 * (1 - lowX t) ^ 5 := by positivity
  have h3 : 0 ≤ 35 * lb3 * (lowX t) ^ 3 * (1 - lowX t) ^ 4 := by positivity
  have h4 : 0 ≤ 35 * lb4 * (lowX t) ^ 4 * (1 - lowX t) ^ 3 := by positivity
  have h5 : 0 ≤ 21 * lb5 * (lowX t) ^ 5 * (1 - lowX t) ^ 2 := by positivity
  have h6 : 0 ≤ 7 * lb6 * (lowX t) ^ 6 * (1 - lowX t) := by positivity
  have h7 : 0 ≤ lb7 * (lowX t) ^ 7 := by positivity
  nlinarith

lemma low_gap_identity (t : ℝ) (h1 : t + 1 ≠ 0) (h2 : t ^ 2 + 1 ≠ 0) :
    firstLhs t - lowK * quintic t =
      t * lowPoly t / (471 * (t + 1) * (t ^ 2 + 1)) := by
  have h1' : 1 + t ≠ 0 := by simpa [add_comm] using h1
  have h2' : 1 + t ^ 2 ≠ 0 := by simpa [add_comm] using h2
  dsimp [firstLhs, lowK, quintic, lowPoly, c, d]
  field_simp [h1, h1', h2, h2']
  ring_nf
  rw [s_sq]
  ring

theorem low_gap_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ (3 : ℝ) / 5) :
    lowK * quintic t ≤ firstLhs t := by
  have h1 : t + 1 ≠ 0 := by positivity
  have h2 : t ^ 2 + 1 ≠ 0 := by positivity
  have hden : 0 < 471 * (t + 1) * (t ^ 2 + 1) := by positivity
  have hp := lowPoly_nonneg t ht0 ht1
  rw [← sub_nonneg, low_gap_identity t h1 h2]
  exact div_nonneg (mul_nonneg ht0 hp) hden.le

def hb0 : ℝ := 272768 / 625 - 172672 * s / 625
def hb1 : ℝ := 66416 / 125 - 40768 * s / 125
def hb2 : ℝ := 47252 / 75 - 27784 * s / 75
def hb3 : ℝ := 3642 / 5 - 402 * s
def hb4 : ℝ := 816 - 408 * s

lemma hb0_pos : 0 < hb0 := by dsimp [hb0]; nlinarith [s_upper_tight]
lemma hb1_pos : 0 < hb1 := by dsimp [hb1]; nlinarith [s_upper_tight]
lemma hb2_pos : 0 < hb2 := by dsimp [hb2]; nlinarith [s_upper_tight]
lemma hb3_pos : 0 < hb3 := by dsimp [hb3]; nlinarith [s_upper_tight]
lemma hb4_pos : 0 < hb4 := by dsimp [hb4]; nlinarith [s_upper_tight]

lemma high_bernstein_identity (t : ℝ) :
    highPoly t =
      hb0 * (1 - highX t) ^ 4 +
      4 * hb1 * highX t * (1 - highX t) ^ 3 +
      6 * hb2 * (highX t) ^ 2 * (1 - highX t) ^ 2 +
      4 * hb3 * (highX t) ^ 3 * (1 - highX t) +
      hb4 * (highX t) ^ 4 := by
  dsimp [highPoly, highX, hb0, hb1, hb2, hb3, hb4]
  ring

lemma highPoly_nonneg (t : ℝ) (ht0 : (3 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ highPoly t := by
  have hx0 : 0 ≤ highX t := by dsimp [highX]; nlinarith
  have hx1 : highX t ≤ 1 := by dsimp [highX]; nlinarith
  have hy0 : 0 ≤ 1 - highX t := sub_nonneg.mpr hx1
  have hb0n : 0 ≤ hb0 := hb0_pos.le
  have hb1n : 0 ≤ hb1 := hb1_pos.le
  have hb2n : 0 ≤ hb2 := hb2_pos.le
  have hb3n : 0 ≤ hb3 := hb3_pos.le
  have hb4n : 0 ≤ hb4 := hb4_pos.le
  rw [high_bernstein_identity]
  have h0 : 0 ≤ hb0 * (1 - highX t) ^ 4 := by positivity
  have h1 : 0 ≤ 4 * hb1 * highX t * (1 - highX t) ^ 3 := by positivity
  have h2 : 0 ≤ 6 * hb2 * (highX t) ^ 2 * (1 - highX t) ^ 2 := by positivity
  have h3 : 0 ≤ 4 * hb3 * (highX t) ^ 3 * (1 - highX t) := by positivity
  have h4 : 0 ≤ hb4 * (highX t) ^ 4 := by positivity
  nlinarith

lemma high_gap_identity (t : ℝ) (h1 : t + 1 ≠ 0) (h2 : t ^ 2 + 1 ≠ 0) :
    firstLhs t - c + highK * cubic (u t) =
      (1 - t) * highPoly t / (189 * (t + 1) ^ 3 * (t ^ 2 + 1)) := by
  have h1' : 1 + t ≠ 0 := by simpa [add_comm] using h1
  have h2' : 1 + t ^ 2 ≠ 0 := by simpa [add_comm] using h2
  dsimp [firstLhs, highK, cubic, u, highPoly, c, d]
  field_simp [h1, h1', h2, h2']
  ring_nf
  rw [s_sq]
  ring

theorem high_gap_nonneg (t : ℝ) (ht0 : (3 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    c - highK * cubic (u t) ≤ firstLhs t := by
  have h1 : t + 1 ≠ 0 := by positivity
  have h2 : t ^ 2 + 1 ≠ 0 := by positivity
  have hden : 0 < 189 * (t + 1) ^ 3 * (t ^ 2 + 1) := by positivity
  have hp := highPoly_nonneg t ht0 ht1
  have hrearrange :
      firstLhs t - (c - highK * cubic (u t)) =
        firstLhs t - c + highK * cubic (u t) := by ring
  rw [← sub_nonneg, hrearrange, high_gap_identity t h1 h2]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hp) hden.le

end

end FirstSectorAlgebra
