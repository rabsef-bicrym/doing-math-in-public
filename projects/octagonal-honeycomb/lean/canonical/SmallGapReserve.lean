import SmallGapBernstein
import CollisionCornerCredit
import PhaseSnappingSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Analytic small-gap reserve

For a normalized turn `u = α/π` with `0 ≤ u ≤ 1/4`, the exact octagonal
phase defect dominates

  `(4/25) * (1 - 4u)`.

On `[0,1/8]` we compare `sin (πu)` and `cos (πu)` with rigorous rational
Taylor lower bounds and finish with the exact Bernstein certificate in
`SmallGapBernstein`.  On `[1/8,1/4]` concavity of sine gives the sharper
chord estimate needed to compare with the octagonal cap line.
-/

namespace SmallGapReserve

noncomputable section

open Real
open PairGapCore
open NoncrystallineDomainReduction
open ContinuousCornerBank
open OctagonalCornerBank
open CollisionCornerCredit
open PhaseSnappingSum
open SmallGapBernstein

lemma pi_lower : ((31415 : ℝ) / 10000) ≤ Real.pi := by
  have h := Real.pi_gt_d4.le
  convert h using 1 <;> norm_num

lemma pi_upper : Real.pi ≤ ((31416 : ℝ) / 10000) := by
  have h := Real.pi_lt_d4.le
  convert h using 1 <;> norm_num

lemma square_le_of_nonneg
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hleft : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hright : 0 ≤ y + x := add_nonneg hy hx
  have hp := mul_nonneg hleft hright
  nlinarith

lemma fourth_le_of_nonneg
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ 4 ≤ y ^ 4 := by
  have hsq := square_le_of_nonneg x y hx hxy
  have hp := mul_le_mul hsq hsq (sq_nonneg x) (sq_nonneg y)
  nlinarith

lemma lowerSin_nonneg
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ (1 : ℝ) / 8) :
    0 ≤ lowerSin u := by
  have hu2 : u ^ 2 ≤ ((1 : ℝ) / 8) ^ 2 :=
    square_le_of_nonneg u ((1 : ℝ) / 8) hu hub
  have hu3 : u ^ 3 ≤ ((1 : ℝ) / 8) ^ 3 := by
    have hp := mul_le_mul hu2 hub hu (sq_nonneg ((1 : ℝ) / 8))
    nlinarith
  have hcoef :
      0 ≤ ((31415 : ℝ) / 10000) -
        (((31416 : ℝ) / 10000) ^ 3) * u ^ 2 / 6 -
        (((31416 : ℝ) / 10000) ^ 4) * u ^ 3 * ((5 : ℝ) / 96) := by
    nlinarith
  have hid :
      lowerSin u = u *
        (((31415 : ℝ) / 10000) -
          (((31416 : ℝ) / 10000) ^ 3) * u ^ 2 / 6 -
          (((31416 : ℝ) / 10000) ^ 4) * u ^ 3 * ((5 : ℝ) / 96)) := by
    dsimp [lowerSin]
    ring
  rw [hid]
  exact mul_nonneg hu hcoef

lemma lowerCos_nonneg
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ (1 : ℝ) / 8) :
    0 ≤ lowerCos u := by
  have hu2 : u ^ 2 ≤ ((1 : ℝ) / 8) ^ 2 :=
    square_le_of_nonneg u ((1 : ℝ) / 8) hu hub
  have hu4 : u ^ 4 ≤ ((1 : ℝ) / 8) ^ 4 :=
    fourth_le_of_nonneg u ((1 : ℝ) / 8) hu hub
  dsimp [lowerCos]
  nlinarith

lemma lowerSin_le_sin
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ (1 : ℝ) / 8) :
    lowerSin u ≤ Real.sin (Real.pi * u) := by
  let x : ℝ := Real.pi * u
  let B : ℝ := ((31416 : ℝ) / 10000) * u
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hxB : x ≤ B := by
    dsimp [x, B]
    exact mul_le_mul_of_nonneg_right pi_upper hu
  have hB1 : B ≤ 1 := by
    dsimp [B]
    nlinarith
  have hx1 : x ≤ 1 := le_trans hxB hB1
  have hxabs : |x| = x := abs_of_nonneg hx0
  have hsq := square_le_of_nonneg x B hx0 hxB
  have hcube : x ^ 3 ≤ B ^ 3 := by
    have hp := mul_le_mul hsq hxB hx0 (sq_nonneg B)
    nlinarith
  have hfour := fourth_le_of_nonneg x B hx0 hxB
  have hbound := Real.sin_bound (x := x) (by simpa [hxabs] using hx1)
  have hraw :
      x - x ^ 3 / 6 - x ^ 4 * ((5 : ℝ) / 96) ≤ Real.sin x := by
    have h := sub_le_comm.1 (abs_sub_le_iff.1 hbound).2
    simpa [hxabs] using h
  calc
    lowerSin u =
        ((31415 : ℝ) / 10000) * u - B ^ 3 / 6 -
          B ^ 4 * ((5 : ℝ) / 96) := by
      dsimp [lowerSin, B]
      ring
    _ ≤ x - x ^ 3 / 6 - x ^ 4 * ((5 : ℝ) / 96) := by
      have hxlower : ((31415 : ℝ) / 10000) * u ≤ x := by
        dsimp [x]
        exact mul_le_mul_of_nonneg_right pi_lower hu
      nlinarith
    _ ≤ Real.sin x := hraw
    _ = Real.sin (Real.pi * u) := rfl

lemma lowerCos_le_cos
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ (1 : ℝ) / 8) :
    lowerCos u ≤ Real.cos (Real.pi * u) := by
  let x : ℝ := Real.pi * u
  let B : ℝ := ((31416 : ℝ) / 10000) * u
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hxB : x ≤ B := by
    dsimp [x, B]
    exact mul_le_mul_of_nonneg_right pi_upper hu
  have hB1 : B ≤ 1 := by
    dsimp [B]
    nlinarith
  have hx1 : x ≤ 1 := le_trans hxB hB1
  have hxabs : |x| = x := abs_of_nonneg hx0
  have hsq := square_le_of_nonneg x B hx0 hxB
  have hfour := fourth_le_of_nonneg x B hx0 hxB
  have hbound := Real.cos_bound (x := x) (by simpa [hxabs] using hx1)
  have hraw :
      1 - x ^ 2 / 2 - x ^ 4 * ((5 : ℝ) / 96) ≤ Real.cos x := by
    have h := sub_le_comm.1 (abs_sub_le_iff.1 hbound).2
    simpa [hxabs] using h
  calc
    lowerCos u =
        1 - B ^ 2 / 2 - B ^ 4 * ((5 : ℝ) / 96) := by
      dsimp [lowerCos, B]
      ring
    _ ≤ 1 - x ^ 2 / 2 - x ^ 4 * ((5 : ℝ) / 96) := by
      nlinarith
    _ ≤ Real.cos x := hraw
    _ = Real.cos (Real.pi * u) := rfl

lemma surrogate_product_le_true
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ (1 : ℝ) / 8) :
    lowerSin u * (lowerCos u + lowerSin u) ≤
      Real.sin (Real.pi * u) *
        (Real.cos (Real.pi * u) + Real.sin (Real.pi * u)) := by
  have hs := lowerSin_le_sin u hu hub
  have hc := lowerCos_le_cos u hu hub
  have hs0 := lowerSin_nonneg u hu hub
  have hc0 := lowerCos_nonneg u hu hub
  have hsum0 : 0 ≤ lowerCos u + lowerSin u := add_nonneg hc0 hs0
  have hsin0 : 0 ≤ Real.sin (Real.pi * u) := le_trans hs0 hs
  have hsum := add_le_add hc hs
  have hfirst := mul_le_mul_of_nonneg_right hs hsum0
  have hsecond := mul_le_mul_of_nonneg_left hsum hsin0
  exact le_trans hfirst hsecond

lemma rationalGap_le_actual
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ (1 : ℝ) / 8) :
    rationalGap u ≤
      smallPhaseDefect u - smallGapReserve * (1 - 4 * u) := by
  have hprod := surrogate_product_le_true u hu hub
  have hprod0 : 0 ≤ lowerSin u * (lowerCos u + lowerSin u) := by
    exact mul_nonneg (lowerSin_nonneg u hu hub)
      (add_nonneg (lowerCos_nonneg u hu hub) (lowerSin_nonneg u hu hub))
  have hdLower : ((141421 : ℝ) / 100000) - 1 ≤ d := by
    dsimp [d]
    nlinarith [s_lower_tight]
  have hmul1 := mul_le_mul_of_nonneg_right hdLower hprod0
  have hmul2 := mul_le_mul_of_nonneg_left hprod d_nonneg
  have hmul := le_trans hmul1 hmul2
  have hcap : 3 - 2 * ((70711 : ℝ) / 50000) ≤ cap := by
    rw [cap_eq]
    nlinarith [s_upper]
  have hslope :
      phaseSlope ≤ 4 * (2 - ((141421 : ℝ) / 100000)) := by
    dsimp [phaseSlope]
    nlinarith [s_lower_tight]
  dsimp [rationalGap, smallPhaseDefect, smallGapReserve]
  nlinarith

/-- Small-gap reserve on the lower half, certified by the exact Bernstein
polynomial. -/
theorem reserve_low
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ (1 : ℝ) / 8) :
    smallGapReserve * pos (1 - 4 * u) ≤ smallPhaseDefect u := by
  have harg : 0 ≤ 1 - 4 * u := by nlinarith
  have hrat := rationalGap_nonneg u hu hub
  have hcompare := rationalGap_le_actual u hu hub
  rw [pos_eq_self_of_nonneg harg]
  nlinarith

/-- Sine lies above the chord joining `0` and `π/4`. -/
lemma sine_quarter_chord
    (z : ℝ) (hz0 : 0 ≤ z) (hzq : z ≤ Real.pi / 4) :
    (2 * s / Real.pi) * z ≤ Real.sin z := by
  let r : ℝ := 4 * z / Real.pi
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one Real.pi_pos).2
    nlinarith
  have hconc :=
    (Real.strictConcaveOn_sin_Icc).concaveOn.2
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
      (show Real.pi / 4 ∈ Set.Icc 0 Real.pi by
        constructor <;> nlinarith [Real.pi_pos])
      (sub_nonneg.mpr hr1) hr0
  have hchord : r * Real.sin (Real.pi / 4) ≤
      Real.sin (r * (Real.pi / 4)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hconc
  have hrz : r * (Real.pi / 4) = z := by
    dsimp [r]
    field_simp [Real.pi_ne_zero]
  have hleft : r * Real.sin (Real.pi / 4) = (2 * s / Real.pi) * z := by
    rw [Real.sin_pi_div_four]
    dsimp [r, s]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hleft, hrz] at hchord
  exact hchord

lemma product_identity (x z : ℝ) (hz : z = 2 * x - Real.pi / 4) :
    Real.sin x * (Real.cos x + Real.sin x) =
      (1 : ℝ) / 2 + (s / 2) * Real.sin z := by
  rw [hz, Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four,
    Real.sin_two_mul, Real.cos_two_mul]
  have htrig := Real.sin_sq_add_cos_sq x
  dsimp [s]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring_nf
  nlinarith [htrig]

lemma product_ge_four_u
    (u : ℝ) (hul : (1 : ℝ) / 8 ≤ u) (huu : u ≤ (1 : ℝ) / 4) :
    4 * u ≤ Real.sin (Real.pi * u) *
      (Real.cos (Real.pi * u) + Real.sin (Real.pi * u)) := by
  let x : ℝ := Real.pi * u
  let z : ℝ := 2 * x - Real.pi / 4
  have hz0 : 0 ≤ z := by
    dsimp [z, x]
    nlinarith [Real.pi_pos]
  have hzq : z ≤ Real.pi / 4 := by
    dsimp [z, x]
    nlinarith [Real.pi_pos]
  have hchord := sine_quarter_chord z hz0 hzq
  have hs0 : 0 ≤ s / 2 := div_nonneg s_nonneg (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hchord hs0
  have hscaled' : 2 * z / Real.pi ≤ (s / 2) * Real.sin z := by
    have hs2 := s_sq
    field_simp [Real.pi_ne_zero] at hscaled ⊢
    nlinarith
  have hid := product_identity x z rfl
  have hzrel : (1 : ℝ) / 2 + 2 * z / Real.pi = 4 * u := by
    dsimp [z, x]
    field_simp [Real.pi_ne_zero]
    ring
  dsimp [x] at hid ⊢
  nlinarith

lemma defect_minus_cap_line (u : ℝ) :
    smallPhaseDefect u - cap * (1 - 4 * u) =
      d * (Real.sin (Real.pi * u) *
        (Real.cos (Real.pi * u) + Real.sin (Real.pi * u)) - 4 * u) := by
  have hrel : 4 * (2 - s) = 4 * cap + 4 * d := by
    rw [cap_eq]
    dsimp [d]
    nlinarith [s_sq]
  dsimp [smallPhaseDefect]
  rw [hrel]
  ring

/-- Small-gap reserve on the upper half. -/
theorem reserve_high
    (u : ℝ) (hul : (1 : ℝ) / 8 ≤ u) (huu : u ≤ (1 : ℝ) / 4) :
    smallGapReserve * pos (1 - 4 * u) ≤ smallPhaseDefect u := by
  have harg : 0 ≤ 1 - 4 * u := by nlinarith
  have hprod := product_ge_four_u u hul huu
  have hcapReserve : smallGapReserve ≤ cap := by
    dsimp [smallGapReserve]
    nlinarith [cap_lower]
  have hline : smallGapReserve * (1 - 4 * u) ≤ cap * (1 - 4 * u) :=
    mul_le_mul_of_nonneg_right hcapReserve harg
  have hid := defect_minus_cap_line u
  have hnonneg : 0 ≤ smallPhaseDefect u - cap * (1 - 4 * u) := by
    have hdprod := mul_nonneg d_nonneg (sub_nonneg.mpr hprod)
    rw [hid]
    exact hdprod
  rw [pos_eq_self_of_nonneg harg]
  linarith

/-- Complete reserve theorem for every gap shorter than one octagonal sector. -/
theorem small_gap_reserve
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ (1 : ℝ) / 4) :
    smallGapReserve * pos (1 - 4 * u) ≤ smallPhaseDefect u := by
  by_cases hhalf : u ≤ (1 : ℝ) / 8
  · exact reserve_low u hu hhalf
  · exact reserve_high u (le_of_not_ge hhalf) hub

end

end SmallGapReserve
