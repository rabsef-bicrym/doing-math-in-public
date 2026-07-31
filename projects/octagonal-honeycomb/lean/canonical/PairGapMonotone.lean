import PairGapCore

/-!
# Monotonicity in the circumscribed-fan area

For edges of length at least `1/2`, this proves that the HH excess is minimized
at the regular-octagon fan area `A8`.
-/

namespace PairGapMonotone

noncomputable section

open Real
open PairGapCore

/-- Rationalized monotonicity of `h x f` in `f`, under the single base
inequality needed by the pair-gap proof. -/
theorem h_mono_from_base
    (x f f0 : ℝ)
    (hf0 : 0 < f0)
    (hff0 : f0 ≤ f)
    (hbase : 4 * d ^ 2 ≤ x ^ 2 * f0) :
    h x f0 ≤ h x f := by
  have hf : 0 ≤ f := le_trans hf0.le hff0
  let R := Real.sqrt (x ^ 2 + 4)
  let y := Real.sqrt f
  let y0 := Real.sqrt f0
  let A := Real.sqrt (f + d ^ 2)
  let B := Real.sqrt (f0 + d ^ 2)
  have hxx : 0 ≤ x ^ 2 + 4 := by positivity
  have hfd : 0 ≤ f + d ^ 2 := by positivity
  have hf0d : 0 ≤ f0 + d ^ 2 := by positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy00 : 0 ≤ y0 := by dsimp [y0]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hR2 : R ^ 2 = x ^ 2 + 4 := by
    dsimp [R]
    exact Real.sq_sqrt hxx
  have hy2 : y ^ 2 = f := by
    dsimp [y]
    exact Real.sq_sqrt hf
  have hy02 : y0 ^ 2 = f0 := by
    dsimp [y0]
    exact Real.sq_sqrt hf0.le
  have hA2 : A ^ 2 = f + d ^ 2 := by
    dsimp [A]
    exact Real.sq_sqrt hfd
  have hB2 : B ^ 2 = f0 + d ^ 2 := by
    dsimp [B]
    exact Real.sq_sqrt hf0d
  have hyorder : y0 ≤ y := by
    dsimp [y, y0]
    exact Real.sqrt_le_sqrt hff0
  have hxf : 4 * d ^ 2 ≤ x ^ 2 * f := by
    have hmul : x ^ 2 * f0 ≤ x ^ 2 * f :=
      mul_le_mul_of_nonneg_left hff0 (sq_nonneg x)
    linarith
  have hRy : 2 * A ≤ R * y := by
    have hleftsq : (2 * A) ^ 2 = 4 * (f + d ^ 2) := by
      nlinarith [hA2]
    have hrightsq : (R * y) ^ 2 = (x ^ 2 + 4) * f := by
      calc
        (R * y) ^ 2 = R ^ 2 * y ^ 2 := by ring
        _ = (x ^ 2 + 4) * f := by rw [hR2, hy2]
    have hsquares : (2 * A) ^ 2 ≤ (R * y) ^ 2 := by
      rw [hleftsq, hrightsq]
      nlinarith [hxf]
    have hleft0 : 0 ≤ 2 * A := by positivity
    have hright0 : 0 ≤ R * y := mul_nonneg hR0 hy0
    nlinarith
  have hRy0 : 2 * B ≤ R * y0 := by
    have hleftsq : (2 * B) ^ 2 = 4 * (f0 + d ^ 2) := by
      nlinarith [hB2]
    have hrightsq : (R * y0) ^ 2 = (x ^ 2 + 4) * f0 := by
      calc
        (R * y0) ^ 2 = R ^ 2 * y0 ^ 2 := by ring
        _ = (x ^ 2 + 4) * f0 := by rw [hR2, hy02]
    have hsquares : (2 * B) ^ 2 ≤ (R * y0) ^ 2 := by
      rw [hleftsq, hrightsq]
      nlinarith [hbase]
    have hleft0 : 0 ≤ 2 * B := by positivity
    have hright0 : 0 ≤ R * y0 := mul_nonneg hR0 hy00
    nlinarith
  have hsum : 2 * (A + B) ≤ R * (y + y0) := by nlinarith
  have hAB : A ^ 2 - B ^ 2 = y ^ 2 - y0 ^ 2 := by
    rw [hA2, hB2, hy2, hy02]
    ring
  have hcross := PairGapLemma.monotonicityCrossIdentity R y y0 A B hAB
  have hright :
      0 ≤ (y - y0) * (R * (y + y0) - 2 * (A + B)) := by
    apply mul_nonneg
    · linarith
    · linarith
  have hleftprod :
      0 ≤ (R * (A - B) - 2 * (y - y0)) * (A + B) := by
    rw [hcross]
    exact hright
  have hleft : 0 ≤ R * (A - B) - 2 * (y - y0) := by
    by_contra hn
    have hneg : R * (A - B) - 2 * (y - y0) < 0 := lt_of_not_ge hn
    have hsumpos : 0 < A + B := by linarith
    have hprodneg := mul_neg_of_neg_of_pos hneg hsumpos
    linarith
  dsimp [h, R, y, y0, A, B]
  linarith

lemma base_condition (x : ℝ) (hx : (1 : ℝ) / 2 ≤ x) :
    4 * d ^ 2 ≤ x ^ 2 * A8 := by
  have hx2 : (1 : ℝ) / 4 ≤ x ^ 2 := by nlinarith
  have hscale : 8 * d * ((1 : ℝ) / 4) ≤ 8 * d * x ^ 2 :=
    mul_le_mul_of_nonneg_left hx2 (mul_nonneg (by norm_num) d_nonneg)
  have h2d : 2 * d ≤ 8 * d * x ^ 2 := by nlinarith
  have hd2 : 4 * d ^ 2 ≤ 2 * d := by
    have hd0 := d_nonneg
    have hdhalf := d_lt_half
    nlinarith
  dsimp [A8]
  nlinarith

/-- For `x ≥ 1/2`, the regular-octagon fan area is the worst case. -/
theorem h_mono_A8 (x f : ℝ) (hx : (1 : ℝ) / 2 ≤ x) (hf : A8 ≤ f) :
    h x A8 ≤ h x f := by
  apply h_mono_from_base x f A8
  · exact A8_pos
  · exact hf
  · exact base_condition x hx

end

end PairGapMonotone
