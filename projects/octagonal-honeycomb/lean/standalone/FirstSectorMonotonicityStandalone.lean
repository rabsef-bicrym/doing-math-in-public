import FirstSectorScalar
import FirstSectorClassificationAlgebra
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Endpoint soundness on the first large octagonal sector

For the scalar phase defect

  `firstLhs t - exactK * arctan t`,

the derivative is nonnegative on `0 ≤ t ≤ 1/4` and nonpositive on
`4/5 ≤ t ≤ 1`.  Together with the independently certified middle-sector
bound, this justifies taking endpoint minima in the interval verifier.
-/

namespace FirstSectorMonotonicityStandalone

noncomputable section

open Real Set
open OctagonBase
open FirstSectorAlgebra
open FirstSectorScalar
open FirstSectorClassificationAlgebra
open OctagonBenchmarkStandalone

def scalarDefect (t : ℝ) : ℝ :=
  firstLhs t - exactK * Real.arctan t

def firstDeriv (t : ℝ) : ℝ :=
  d * (1 + 2 * t - t ^ 2) / (1 + t ^ 2) ^ 2 +
    c ^ 2 / (1 + t) ^ 2

def scalarDeriv (t : ℝ) : ℝ :=
  firstDeriv t - exactK / (1 + t ^ 2)

def lowDerivNum (t : ℝ) : ℝ :=
  (-585 * s + 699) * t ^ 4 +
    (400 * s - 800) * t ^ 3 +
    (-228 * s + 456) * t ^ 2 +
    (1028 * s - 1428) * t + (385 - 271 * s)

def highDerivNum (t : ℝ) : ℝ :=
  (-235 * s + 281) * t ^ 4 +
    (160 * s - 320) * t ^ 3 +
    (-92 * s + 184) * t ^ 2 +
    (412 * s - 572) * t + (155 - 109 * s)

lemma hasDerivAt_firstLhs
    (t : ℝ) (h1 : 1 + t ≠ 0) (h2 : 1 + t ^ 2 ≠ 0) :
    HasDerivAt firstLhs (firstDeriv t) t := by
  have ht := hasDerivAt_id t
  have h1t := (hasDerivAt_const t 1).add ht
  have h1t2 := (hasDerivAt_const t 1).add (ht.pow 2)
  have hnum := ht.mul h1t
  have ha := (hnum.const_mul d).div h1t2 h2
  have hb := (ht.const_mul (c ^ 2)).div h1t h1
  have h := ha.add hb
  convert h using 1
  · funext x
    dsimp [firstLhs]
    ring
  · dsimp [firstDeriv]
    field_simp [h1, h2]
    ring

lemma hasDerivAt_scalarDefect
    (t : ℝ) (h1 : 1 + t ≠ 0) (h2 : 1 + t ^ 2 ≠ 0) :
    HasDerivAt scalarDefect (scalarDeriv t) t := by
  have hf := hasDerivAt_firstLhs t h1 h2
  have ha := (Real.hasDerivAt_arctan t).const_mul exactK
  simpa [scalarDefect, scalarDeriv, div_eq_mul_inv] using hf.sub ha

lemma low_deriv_identity
    (t : ℝ) (h1 : 1 + t ≠ 0) (h2 : 1 + t ^ 2 ≠ 0) :
    firstDeriv t - lowK / (1 + t ^ 2) =
      lowDerivNum t / (157 * (1 + t) ^ 2 * (1 + t ^ 2) ^ 2) := by
  dsimp [firstDeriv, lowK, lowDerivNum, c, d]
  field_simp [h1, h2]
  ring_nf
  rw [s_sq]
  ring

lemma high_deriv_identity
    (t : ℝ) (h1 : 1 + t ≠ 0) (h2 : 1 + t ^ 2 ≠ 0) :
    firstDeriv t - highK / (1 + t ^ 2) =
      highDerivNum t / (63 * (1 + t) ^ 2 * (1 + t ^ 2) ^ 2) := by
  dsimp [firstDeriv, highK, highDerivNum, c, d]
  field_simp [h1, h2]
  ring_nf
  rw [s_sq]
  ring

def bern4 (b0 b1 b2 b3 b4 z : ℝ) : ℝ :=
  b0 * (1 - z) ^ 4 + 4 * b1 * z * (1 - z) ^ 3 +
    6 * b2 * z ^ 2 * (1 - z) ^ 2 +
    4 * b3 * z ^ 3 * (1 - z) + b4 * z ^ 4

lemma bern4_nonneg
    (b0 b1 b2 b3 b4 z : ℝ)
    (h0 : 0 ≤ b0) (h1 : 0 ≤ b1) (h2 : 0 ≤ b2)
    (h3 : 0 ≤ b3) (h4 : 0 ≤ b4)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ bern4 b0 b1 b2 b3 b4 z := by
  have h1z : 0 ≤ 1 - z := sub_nonneg.mpr hz1
  dsimp [bern4]
  positivity

def l0 : ℝ := 385 - 271 * s
def l1 : ℝ := (1183 - 827 * s) / 4
def l2 : ℝ := (1690 - 1159 * s) / 8
def l3 : ℝ := (2054 - 1341 * s) / 16
def l4 : ℝ := (11963 - 6217 * s) / 256

def r0 : ℝ := 9 * (16221 - 10235 * s) / 625
def r1 : ℝ := 18 * (1732 - 1055 * s) / 125
def r2 : ℝ := (19645 - 11429 * s) / 75
def r3 : ℝ := 18 * (75 - 41 * s) / 5
def r4 : ℝ := 136 * (2 - s)

lemma low_coefficients_pos :
    0 < l0 ∧ 0 < l1 ∧ 0 < l2 ∧ 0 < l3 ∧ 0 < l4 := by
  constructor
  · dsimp [l0]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [l1]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [l2]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [l3]; nlinarith [s_upper_tighter]
  · dsimp [l4]; nlinarith [s_upper_tighter]

lemma high_coefficients_pos :
    0 < r0 ∧ 0 < r1 ∧ 0 < r2 ∧ 0 < r3 ∧ 0 < r4 := by
  constructor
  · dsimp [r0]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [r1]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [r2]; nlinarith [s_upper_tighter]
  constructor
  · dsimp [r3]; nlinarith [s_upper_tighter]
  · dsimp [r4]; nlinarith [s_upper_tighter]

lemma low_bernstein_identity (t : ℝ) :
    lowDerivNum t = bern4 l0 l1 l2 l3 l4 (4 * t) := by
  dsimp [lowDerivNum, bern4, l0, l1, l2, l3, l4]
  ring

lemma high_bernstein_identity (t : ℝ) :
    -highDerivNum t = bern4 r0 r1 r2 r3 r4 (5 * t - 4) := by
  dsimp [highDerivNum, bern4, r0, r1, r2, r3, r4]
  ring

lemma lowDerivNum_nonneg
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ (1 : ℝ) / 4) :
    0 ≤ lowDerivNum t := by
  have hz0 : 0 ≤ 4 * t := by nlinarith
  have hz1 : 4 * t ≤ 1 := by nlinarith
  rcases low_coefficients_pos with ⟨h0,h1,h2,h3,h4⟩
  rw [low_bernstein_identity]
  exact bern4_nonneg l0 l1 l2 l3 l4 (4 * t)
    h0.le h1.le h2.le h3.le h4.le hz0 hz1

lemma highDerivNum_nonpos
    (t : ℝ) (ht0 : (4 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    highDerivNum t ≤ 0 := by
  have hz0 : 0 ≤ 5 * t - 4 := by nlinarith
  have hz1 : 5 * t - 4 ≤ 1 := by nlinarith
  rcases high_coefficients_pos with ⟨h0,h1,h2,h3,h4⟩
  have h := bern4_nonneg r0 r1 r2 r3 r4 (5 * t - 4)
    h0.le h1.le h2.le h3.le h4.le hz0 hz1
  rw [← high_bernstein_identity] at h
  linarith

lemma scalarDeriv_nonneg_low
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ (1 : ℝ) / 4) :
    0 ≤ scalarDeriv t := by
  have h1 : 1 + t ≠ 0 := by positivity
  have h2 : 1 + t ^ 2 ≠ 0 := by positivity
  have hden : 0 < 157 * (1 + t) ^ 2 * (1 + t ^ 2) ^ 2 := by positivity
  have hnum := lowDerivNum_nonneg t ht0 ht1
  have hlow : 0 ≤ firstDeriv t - lowK / (1 + t ^ 2) := by
    rw [low_deriv_identity t h1 h2]
    exact div_nonneg hnum hden.le
  have hk : exactK / (1 + t ^ 2) ≤ lowK / (1 + t ^ 2) := by
    exact (div_le_div_iff_of_pos_right (by positivity : 0 < 1 + t ^ 2)).2 exactK_le_lowK
  dsimp [scalarDeriv]
  linarith

lemma scalarDeriv_nonpos_high
    (t : ℝ) (ht0 : (4 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    scalarDeriv t ≤ 0 := by
  have h1 : 1 + t ≠ 0 := by positivity
  have h2 : 1 + t ^ 2 ≠ 0 := by positivity
  have hden : 0 < 63 * (1 + t) ^ 2 * (1 + t ^ 2) ^ 2 := by positivity
  have hnum := highDerivNum_nonpos t ht0 ht1
  have hhigh : firstDeriv t - highK / (1 + t ^ 2) ≤ 0 := by
    rw [high_deriv_identity t h1 h2]
    exact div_nonpos_of_nonpos_of_nonneg hnum hden.le
  have hk : highK / (1 + t ^ 2) ≤ exactK / (1 + t ^ 2) := by
    exact (div_le_div_iff_of_pos_right (by positivity : 0 < 1 + t ^ 2)).2 highK_le_exactK
  dsimp [scalarDeriv]
  linarith

lemma deriv_scalarDefect_nonneg_low
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ (1 : ℝ) / 4) :
    0 ≤ deriv scalarDefect t := by
  have h1 : 1 + t ≠ 0 := by positivity
  have h2 : 1 + t ^ 2 ≠ 0 := by positivity
  rw [(hasDerivAt_scalarDefect t h1 h2).deriv]
  exact scalarDeriv_nonneg_low t ht0 ht1

lemma deriv_scalarDefect_nonpos_high
    (t : ℝ) (ht0 : (4 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    deriv scalarDefect t ≤ 0 := by
  have h1 : 1 + t ≠ 0 := by positivity
  have h2 : 1 + t ^ 2 ≠ 0 := by positivity
  rw [(hasDerivAt_scalarDefect t h1 h2).deriv]
  exact scalarDeriv_nonpos_high t ht0 ht1

/-- Endpoint soundness near the left crystalline minimum. -/
theorem scalarDefect_monotone_low :
    MonotoneOn scalarDefect (Set.Icc 0 ((1 : ℝ) / 4)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 ((1 : ℝ) / 4))
  · intro t ht
    have h1 : 1 + t ≠ 0 := by nlinarith [ht.1]
    have h2 : 1 + t ^ 2 ≠ 0 := by positivity
    exact (hasDerivAt_scalarDefect t h1 h2).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have h1 : 1 + t ≠ 0 := by nlinarith [ht.1]
    have h2 : 1 + t ^ 2 ≠ 0 := by positivity
    exact (hasDerivAt_scalarDefect t h1 h2).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact deriv_scalarDefect_nonneg_low t ht.1.le ht.2.le

/-- Endpoint soundness near the right crystalline minimum. -/
theorem scalarDefect_antitone_high :
    AntitoneOn scalarDefect (Set.Icc ((4 : ℝ) / 5) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc ((4 : ℝ) / 5) 1)
  · intro t ht
    have h1 : 1 + t ≠ 0 := by nlinarith [ht.1]
    have h2 : 1 + t ^ 2 ≠ 0 := by positivity
    exact (hasDerivAt_scalarDefect t h1 h2).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have h1 : 1 + t ≠ 0 := by nlinarith [ht.1]
    have h2 : 1 + t ^ 2 ≠ 0 := by positivity
    exact (hasDerivAt_scalarDefect t h1 h2).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact deriv_scalarDefect_nonpos_high t ht.1.le ht.2.le

end

end FirstSectorMonotonicityStandalone
