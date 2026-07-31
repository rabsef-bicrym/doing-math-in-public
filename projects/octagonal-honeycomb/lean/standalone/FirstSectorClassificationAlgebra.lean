import FirstSectorAlgebra
import OctagonBenchmarkStandalone

/-!
# Quantitative first-sector classification certificate

The negative-pentagon threshold is below `4/625`.  On the middle part of the
first large sector, `13° ≤ beta ≤ 42°`, the phase defect is larger than this
threshold.  The transcendental arctangent step is separated from two exact
Bernstein polynomial certificates.
-/

namespace FirstSectorClassificationAlgebra

noncomputable section

open OctagonBase
open OctagonBenchmarkStandalone
open FirstSectorAlgebra

/-- Safe rational upper bound for the pentagonal defect budget. -/
def q5 : ℝ := (4 : ℝ) / 625

def lowClassPoly (t : ℝ) : ℝ :=
  120 * s * t ^ 8 + 120 * s * t ^ 7 - 80 * s * t ^ 6 -
    80 * s * t ^ 5 + 400 * s * t ^ 4 - 1013 * s * t ^ 3 +
    1542 * s * t ^ 2 - 813 * s * t - 240 * t ^ 8 -
    240 * t ^ 7 + 160 * t ^ 6 + 160 * t ^ 5 - 800 * t ^ 4 +
    ((969991 : ℝ) / 625) * t ^ 3 - ((1340634 : ℝ) / 625) * t ^ 2 +
    ((719991 : ℝ) / 625) * t - (1884 : ℝ) / 625

def highClassPoly (t : ℝ) : ℝ :=
  -218 * s * t ^ 5 + 291 * s * t ^ 4 + 58 * s * t ^ 3 +
    320 * s * t ^ 2 - 480 * s * t + 29 * s +
    ((153619 : ℝ) / 625) * t ^ 5 - ((366018 : ℝ) / 625) * t ^ 4 +
    ((160726 : ℝ) / 625) * t ^ 3 - ((403024 : ℝ) / 625) * t ^ 2 +
    ((479607 : ℝ) / 625) * t - (37006 : ℝ) / 625

def lowZ (t : ℝ) : ℝ := (40 * t - 9) / 15

def highZ (t : ℝ) : ℝ := (105 * t - 63) / 32

def bern8
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 z : ℝ) : ℝ :=
  b0 * (1 - z) ^ 8 +
    8 * b1 * z * (1 - z) ^ 7 +
    28 * b2 * z ^ 2 * (1 - z) ^ 6 +
    56 * b3 * z ^ 3 * (1 - z) ^ 5 +
    70 * b4 * z ^ 4 * (1 - z) ^ 4 +
    56 * b5 * z ^ 5 * (1 - z) ^ 3 +
    28 * b6 * z ^ 6 * (1 - z) ^ 2 +
    8 * b7 * z ^ 7 * (1 - z) + b8 * z ^ 8

def bern5 (b0 b1 b2 b3 b4 b5 z : ℝ) : ℝ :=
  b0 * (1 - z) ^ 5 +
    5 * b1 * z * (1 - z) ^ 4 +
    10 * b2 * z ^ 2 * (1 - z) ^ 3 +
    10 * b3 * z ^ 3 * (1 - z) ^ 2 +
    5 * b4 * z ^ 4 * (1 - z) + b5 * z ^ 5

lemma bern8_nonneg
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 z : ℝ)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4) (hb5 : 0 ≤ b5)
    (hb6 : 0 ≤ b6) (hb7 : 0 ≤ b7) (hb8 : 0 ≤ b8)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ bern8 b0 b1 b2 b3 b4 b5 b6 b7 b8 z := by
  have h1z : 0 ≤ 1 - z := sub_nonneg.mpr hz1
  dsimp [bern8]
  positivity

lemma bern5_nonneg
    (b0 b1 b2 b3 b4 b5 z : ℝ)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4) (hb5 : 0 ≤ b5)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ bern5 b0 b1 b2 b3 b4 b5 z := by
  have h1z : 0 ≤ 1 - z := sub_nonneg.mpr hz1
  dsimp [bern5]
  positivity

-- Exact Bernstein coefficients on `[9/40,3/5]`.
def lb0 : ℝ := 3 * (8919625467566 - 6303854168919 * s) / 163840000000
def lb1 : ℝ := 3 * (9913716489926 - 6958930805859 * s) / 163840000000
def lb2 : ℝ := 3 * (4613786619122 - 3214797119673 * s) / 71680000000
def lb3 : ℝ := 3 * (1188161660498 - 821103826257 * s) / 17920000000
def lb4 : ℝ := 3 * (37267446979 - 25522816686 * s) / 560000000
def lb5 : ℝ := 3 * (146204535901 - 99176402559 * s) / 2240000000
def lb6 : ℝ := 3 * (8757326671 - 5884776189 * s) / 140000000
def lb7 : ℝ := 3 * (18229222 - 12155073 * s) / 312500
def lb8 : ℝ := 12 * (1020037 - 678558 * s) / 78125

-- Exact Bernstein coefficients on `[3/5,19/21]`.
def hb0 : ℝ := 4864 * (67393 - 44375 * s) / 1953125
def hb1 : ℝ := 256 * (8717789 - 5651875 * s) / 13671875
def hb2 : ℝ := 256 * (101026103 - 64425625 * s) / 172265625
def hb3 : ℝ := 256 * (72224179 - 45405125 * s) / 144703125
def hb4 : ℝ := 256 * (15143021 - 9542875 * s) / 40516875
def hb5 : ℝ := 256 * (4328951 - 2995225 * s) / 20420505

lemma low_coefficients_pos :
    0 < lb0 ∧ 0 < lb1 ∧ 0 < lb2 ∧ 0 < lb3 ∧ 0 < lb4 ∧
      0 < lb5 ∧ 0 < lb6 ∧ 0 < lb7 ∧ 0 < lb8 := by
  constructor
  · dsimp [lb0]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [lb1]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [lb2]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [lb3]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [lb4]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [lb5]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [lb6]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [lb7]; nlinarith [s_upper_tighter]
  · dsimp [lb8]; nlinarith [s_upper_tighter]

lemma high_coefficients_pos :
    0 < hb0 ∧ 0 < hb1 ∧ 0 < hb2 ∧ 0 < hb3 ∧ 0 < hb4 ∧ 0 < hb5 := by
  constructor
  · dsimp [hb0]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [hb1]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [hb2]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [hb3]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [hb4]; nlinarith [s_upper_tighter]
  · dsimp [hb5]; nlinarith [s_upper_tighter]

lemma low_bernstein_identity (t : ℝ) :
    lowClassPoly t =
      bern8 lb0 lb1 lb2 lb3 lb4 lb5 lb6 lb7 lb8 (lowZ t) := by
  dsimp [lowClassPoly, bern8, lowZ,
    lb0, lb1, lb2, lb3, lb4, lb5, lb6, lb7, lb8]
  ring

lemma high_bernstein_identity (t : ℝ) :
    highClassPoly t = bern5 hb0 hb1 hb2 hb3 hb4 hb5 (highZ t) := by
  dsimp [highClassPoly, bern5, highZ, hb0, hb1, hb2, hb3, hb4, hb5]
  ring

lemma lowClassPoly_nonneg
    (t : ℝ) (ht0 : (9 : ℝ) / 40 ≤ t) (ht1 : t ≤ (3 : ℝ) / 5) :
    0 ≤ lowClassPoly t := by
  have hz0 : 0 ≤ lowZ t := by dsimp [lowZ]; nlinarith
  have hz1 : lowZ t ≤ 1 := by dsimp [lowZ]; nlinarith
  rcases low_coefficients_pos with
    ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  rw [low_bernstein_identity]
  exact bern8_nonneg lb0 lb1 lb2 lb3 lb4 lb5 lb6 lb7 lb8 (lowZ t)
    h0.le h1.le h2.le h3.le h4.le h5.le h6.le h7.le h8.le hz0 hz1

lemma highClassPoly_nonneg
    (t : ℝ) (ht0 : (3 : ℝ) / 5 ≤ t) (ht1 : t ≤ (19 : ℝ) / 21) :
    0 ≤ highClassPoly t := by
  have hz0 : 0 ≤ highZ t := by dsimp [highZ]; nlinarith
  have hz1 : highZ t ≤ 1 := by dsimp [highZ]; nlinarith
  rcases high_coefficients_pos with ⟨h0,h1,h2,h3,h4,h5⟩
  rw [high_bernstein_identity]
  exact bern5_nonneg hb0 hb1 hb2 hb3 hb4 hb5 (highZ t)
    h0.le h1.le h2.le h3.le h4.le h5.le hz0 hz1

lemma low_class_identity
    (t : ℝ) (h1 : t + 1 ≠ 0) (h2 : t ^ 2 + 1 ≠ 0) :
    firstLhs t - lowK * quintic t - q5 =
      lowClassPoly t / (471 * (t + 1) * (t ^ 2 + 1)) := by
  rw [low_gap_identity t h1 h2]
  dsimp [q5, lowClassPoly, lowPoly]
  field_simp [h1, h2]
  ring

lemma high_class_identity
    (t : ℝ) (h1 : t + 1 ≠ 0) (h2 : t ^ 2 + 1 ≠ 0) :
    firstLhs t - c + highK * cubic (u t) - q5 =
      highClassPoly t / (189 * (t + 1) ^ 3 * (t ^ 2 + 1)) := by
  rw [high_gap_identity t h1 h2]
  dsimp [q5, highClassPoly, highPoly]
  field_simp [h1, h2]
  ring

/-- Strengthened lower certificate on the low half. -/
theorem low_class_gap
    (t : ℝ) (ht0 : (9 : ℝ) / 40 ≤ t) (ht1 : t ≤ (3 : ℝ) / 5) :
    q5 + lowK * quintic t ≤ firstLhs t := by
  have ht : 0 ≤ t := by nlinarith
  have h1 : t + 1 ≠ 0 := by positivity
  have h2 : t ^ 2 + 1 ≠ 0 := by positivity
  have hden : 0 < 471 * (t + 1) * (t ^ 2 + 1) := by positivity
  have hp := lowClassPoly_nonneg t ht0 ht1
  have hquot : 0 ≤ lowClassPoly t / (471 * (t + 1) * (t ^ 2 + 1)) :=
    div_nonneg hp hden.le
  have hraw : 0 ≤ firstLhs t - lowK * quintic t - q5 := by
    rw [low_class_identity t h1 h2]
    exact hquot
  linarith

/-- Strengthened lower certificate on the high half. -/
theorem high_class_gap
    (t : ℝ) (ht0 : (3 : ℝ) / 5 ≤ t) (ht1 : t ≤ (19 : ℝ) / 21) :
    q5 + c - highK * cubic (u t) ≤ firstLhs t := by
  have ht : 0 ≤ t := by nlinarith
  have h1 : t + 1 ≠ 0 := by positivity
  have h2 : t ^ 2 + 1 ≠ 0 := by positivity
  have hden : 0 < 189 * (t + 1) ^ 3 * (t ^ 2 + 1) := by positivity
  have hp := highClassPoly_nonneg t ht0 ht1
  have hquot :
      0 ≤ highClassPoly t / (189 * (t + 1) ^ 3 * (t ^ 2 + 1)) :=
    div_nonneg hp hden.le
  have hraw : 0 ≤ firstLhs t - c + highK * cubic (u t) - q5 := by
    rw [high_class_identity t h1 h2]
    exact hquot
  linarith

end

end FirstSectorClassificationAlgebra
