import Mathlib

/-!
# Exact Bernstein certificate for the small-gap reserve

The transcendental comparison is reduced to an explicit degree-eight rational
polynomial `rationalGap`.  This module proves its nonnegativity on
`[0, 1/8]` by two exact Bernstein-basis expansions, on `[0,1/16]` and
`[1/16,1/8]`.  Every Bernstein coefficient is a strictly positive rational
number.
-/

namespace SmallGapBernstein

noncomputable section

/-- Rational lower approximation to `sin (π u)` used on `0 ≤ u ≤ 1/8`. -/
def lowerSin (u : ℝ) : ℝ :=
  ((31415 : ℝ) / 10000) * u -
    (((31416 : ℝ) / 10000) ^ 3) * u ^ 3 / 6 -
    (((31416 : ℝ) / 10000) ^ 4) * u ^ 4 * ((5 : ℝ) / 96)

/-- Rational lower approximation to `cos (π u)` used on `0 ≤ u ≤ 1/8`. -/
def lowerCos (u : ℝ) : ℝ :=
  1 - (((31416 : ℝ) / 10000) ^ 2) * u ^ 2 / 2 -
    (((31416 : ℝ) / 10000) ^ 4) * u ^ 4 * ((5 : ℝ) / 96)

/-- Fully rational lower bound for
`smallPhaseDefect u - (4/25) * (1 - 4u)`. -/
def rationalGap (u : ℝ) : ℝ :=
  (3 - 2 * ((70711 : ℝ) / 50000)) - ((4 : ℝ) / 25) +
    (-4 * (2 - ((141421 : ℝ) / 100000)) + ((16 : ℝ) / 25)) * u +
    (((141421 : ℝ) / 100000) - 1) * lowerSin u *
      (lowerCos u + lowerSin u)

/-- Degree-eight Bernstein polynomial. -/
def bern8
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 t : ℝ) : ℝ :=
  b0 * (1 - t) ^ 8 +
    8 * b1 * t * (1 - t) ^ 7 +
    28 * b2 * t ^ 2 * (1 - t) ^ 6 +
    56 * b3 * t ^ 3 * (1 - t) ^ 5 +
    70 * b4 * t ^ 4 * (1 - t) ^ 4 +
    56 * b5 * t ^ 5 * (1 - t) ^ 3 +
    28 * b6 * t ^ 6 * (1 - t) ^ 2 +
    8 * b7 * t ^ 7 * (1 - t) +
    b8 * t ^ 8

lemma bern8_nonneg
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 t : ℝ)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4) (hb5 : 0 ≤ b5)
    (hb6 : 0 ≤ b6) (hb7 : 0 ≤ b7) (hb8 : 0 ≤ b8)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bern8 b0 b1 b2 b3 b4 b5 b6 b7 b8 t := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  dsimp [bern8]
  positivity

abbrev l0 : ℝ := 289 / 25000
abbrev l1 : ℝ := 215552143 / 25600000000
abbrev l2 : ℝ := 16773987114469 / 2867200000000000
abbrev l3 : ℝ := 2733562296030513517 / 716800000000000000000
abbrev l4 : ℝ := 16264707722486048712421 / 7168000000000000000000000
abbrev l5 : ℝ := 5379160627882463629138037161 / 4587520000000000000000000000000
abbrev l6 : ℝ := 5460487569297999894575993279971 / 11468800000000000000000000000000000
abbrev l7 : ℝ := 1679000988056240241688902512839721 / 13107200000000000000000000000000000000
abbrev l8 : ℝ := 3837475819103876832120238000973954789 / 52428800000000000000000000000000000000000

abbrev r0 : ℝ := 3837475819103876832120238000973954789 / 52428800000000000000000000000000000000000
abbrev r1 : ℝ := 479473842991396348742432975294512789 / 26214400000000000000000000000000000000000
abbrev r2 : ℝ := 23534203622536410214160341887073495523 / 91750400000000000000000000000000000000000
abbrev r3 : ℝ := 33604384619692408852351227576853401523 / 45875200000000000000000000000000000000000
abbrev r4 : ℝ := 31822318325538489944136516286401307523 / 22937600000000000000000000000000000000000
abbrev r5 : ℝ := 24753531148672512685630236405717213523 / 11468800000000000000000000000000000000000
abbrev r6 : ℝ := 17084594965609259608693616324801119523 / 5734400000000000000000000000000000000000
abbrev r7 : ℝ := 1548605546595460044133583490521860789 / 409600000000000000000000000000000000000
abbrev r8 : ℝ := 919595836542767881958609874610418789 / 204800000000000000000000000000000000000

lemma left_coefficients_nonneg :
    0 ≤ l0 ∧ 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ 0 ≤ l4 ∧
      0 ≤ l5 ∧ 0 ≤ l6 ∧ 0 ≤ l7 ∧ 0 ≤ l8 := by
  norm_num [l0, l1, l2, l3, l4, l5, l6, l7, l8]

lemma right_coefficients_nonneg :
    0 ≤ r0 ∧ 0 ≤ r1 ∧ 0 ≤ r2 ∧ 0 ≤ r3 ∧ 0 ≤ r4 ∧
      0 ≤ r5 ∧ 0 ≤ r6 ∧ 0 ≤ r7 ∧ 0 ≤ r8 := by
  norm_num [r0, r1, r2, r3, r4, r5, r6, r7, r8]

lemma rationalGap_left_identity (u : ℝ) :
    rationalGap u = bern8 l0 l1 l2 l3 l4 l5 l6 l7 l8 (16 * u) := by
  dsimp [rationalGap, lowerSin, lowerCos, bern8,
    l0, l1, l2, l3, l4, l5, l6, l7, l8]
  ring

lemma rationalGap_right_identity (u : ℝ) :
    rationalGap u = bern8 r0 r1 r2 r3 r4 r5 r6 r7 r8 (16 * u - 1) := by
  dsimp [rationalGap, lowerSin, lowerCos, bern8,
    r0, r1, r2, r3, r4, r5, r6, r7, r8]
  ring

/-- Exact positivity of the rational lower polynomial on the complete low-gap
interval. -/
theorem rationalGap_nonneg
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ (1 : ℝ) / 8) :
    0 ≤ rationalGap u := by
  rcases left_coefficients_nonneg with
    ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8⟩
  rcases right_coefficients_nonneg with
    ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩
  by_cases hhalf : u ≤ (1 : ℝ) / 16
  · rw [rationalGap_left_identity]
    apply bern8_nonneg l0 l1 l2 l3 l4 l5 l6 l7 l8 (16 * u)
      hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8
    · nlinarith
    · nlinarith
  · have hhalf' : (1 : ℝ) / 16 ≤ u := le_of_not_ge hhalf
    rw [rationalGap_right_identity]
    apply bern8_nonneg r0 r1 r2 r3 r4 r5 r6 r7 r8 (16 * u - 1)
      hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
    · nlinarith
    · nlinarith

end

end SmallGapBernstein
