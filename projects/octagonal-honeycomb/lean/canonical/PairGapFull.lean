import PairGapLemma
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity

/-!
# Full square-root proof of the crystalline pair-gap lemma

This file upgrades `PairGapLemma.lean` from an exact certificate layer to the
actual analytic statement used in the crystalline honeycomb argument.
-/

namespace PairGapFull

noncomputable section

open Real

/-- The octagonal constants, kept as definitions so the final theorem has the
same statement as the paper proof. -/
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

/-- The `HH` excess term is nonnegative for every nonnegative fan area. -/
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
    positivity
  have hU2 : U ^ 2 = (f + d ^ 2) * (x ^ 2 + 4) := by
    dsimp [U]
    rw [mul_pow, Real.sq_sqrt hfd, Real.sq_sqrt hxx]
  have hV2 : V ^ 2 = (d * x + 2 * Real.sqrt f) ^ 2 := rfl
  have hsqrtf : (Real.sqrt f) ^ 2 = f := Real.sq_sqrt hf
  have hgap : 0 ≤ U ^ 2 - V ^ 2 := by
    rw [hU2, hV2]
    calc
      0 ≤ (x * Real.sqrt f - 2 * d) ^ 2 := sq_nonneg _
      _ = (f + d ^ 2) * (x ^ 2 + 4) - (d * x + 2 * Real.sqrt f) ^ 2 := by
        rw [hsqrtf]
        ring
  have hUV : V ≤ U := by nlinarith
  dsimp [h, U, V] at hUV ⊢
  linarith

/-- Algebraic monotonicity of `h` in the fan area, under the one inequality
needed in the large-edge branch. -/
theorem h_mono_from_base
    (x f f0 : ℝ)
    (hx : 0 ≤ x)
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
    have hsquares : (2 * A) ^ 2 ≤ (R * y) ^ 2 := by
      rw [mul_pow, hR2, hy2]
      nlinarith [hA2]
    have hRy0 : 0 ≤ R * y := mul_nonneg hR0 hy0
    nlinarith
  have hRy0 : 2 * B ≤ R * y0 := by
    have hsquares : (2 * B) ^ 2 ≤ (R * y0) ^ 2 := by
      rw [mul_pow, hR2, hy02]
      nlinarith [hB2]
    have hprod0 : 0 ≤ R * y0 := mul_nonneg hR0 hy00
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
    have := mul_neg_of_neg_of_pos hneg hsumpos
    linarith
  dsimp [h, R, y, y0, A, B]
  linarith

lemma base_condition (x : ℝ) (hx : (1 : ℝ) / 2 ≤ x) :
    4 * d ^ 2 ≤ x ^ 2 * A8 := by
  have hx2 : (1 : ℝ) / 4 ≤ x ^ 2 := by nlinarith
  have hA : 2 * d ≤ x ^ 2 * A8 := by
    dsimp [A8]
    have hd0 := d_nonneg
    nlinarith
  have hdhalf := d_lt_half
  nlinarith

/-- For `x ≥ 1/2`, the worst fan area is the octagonal one. -/
theorem h_mono_A8 (x f : ℝ) (hx : (1 : ℝ) / 2 ≤ x) (hf : A8 ≤ f) :
    h x A8 ≤ h x f := by
  apply h_mono_from_base x f A8
  · linarith
  · exact A8_pos
  · exact hf
  · exact base_condition x hx

lemma p5_upper : p5 < (3914 : ℝ) / 1000 := by
  have hA5 : 0 ≤ A5 := A5_pos.le
  have hp5nonneg : 0 ≤ p5 := by dsimp [p5]; positivity
  have hp5sq : p5 ^ 2 = 4 * A5 := by
    dsimp [p5]
    rw [mul_pow, Real.sq_sqrt hA5]
    ring
  have hAupper : 4 * A5 < ((3914 : ℝ) / 1000) ^ 2 := by
    dsimp [A5]
    nlinarith [s_upper,
      show 4 + 8 * ((70711 : ℝ) / 50000) < ((3914 : ℝ) / 1000) ^ 2 by norm_num]
  norm_num at hp5nonneg ⊢
  nlinarith

lemma p8_upper : p8 < (3641 : ℝ) / 1000 := by
  have hA8 : 0 ≤ A8 := A8_pos.le
  have hp8nonneg : 0 ≤ p8 := by dsimp [p8]; positivity
  have hp8sq : p8 ^ 2 = 4 * A8 := by
    dsimp [p8]
    rw [mul_pow, Real.sq_sqrt hA8]
    ring
  have hAupper : 4 * A8 < ((3641 : ℝ) / 1000) ^ 2 := by
    dsimp [A8, d]
    nlinarith [s_upper,
      show 32 * (((70711 : ℝ) / 50000) - 1) < ((3641 : ℝ) / 1000) ^ 2 by norm_num]
  norm_num at hp8nonneg ⊢
  nlinarith

/-- The tangent estimate after multiplying by the octagonal coefficient.  This
form avoids any appeal to a square-root multiplication theorem. -/
lemma tangent_product_lower (x : ℝ) (hx : (1 : ℝ) / 2 ≤ x) :
    (23 * x + 100) * Real.sqrt ((6 * s - 5) / 3029) ≤
      Real.sqrt (6 * s - 5) * Real.sqrt (x ^ 2 + 4) := by
  let g : ℝ := 6 * s - 5
  let u : ℝ := Real.sqrt (g / 3029)
  let a : ℝ := Real.sqrt g
  let R : ℝ := Real.sqrt (x ^ 2 + 4)
  have hg : 0 < g := by
    dsimp [g]
    nlinarith [s_lower]
  have hgu : 0 ≤ g / 3029 := by positivity
  have hxx : 0 ≤ x ^ 2 + 4 := by positivity
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hlin : 0 ≤ 23 * x + 100 := by nlinarith
  have hu2 : u ^ 2 = g / 3029 := by
    dsimp [u]
    exact Real.sq_sqrt hgu
  have ha2 : a ^ 2 = g := by
    dsimp [a]
    exact Real.sq_sqrt hg.le
  have hR2 : R ^ 2 = x ^ 2 + 4 := by
    dsimp [R]
    exact Real.sq_sqrt hxx
  have hid :
      3029 * ((a * R) ^ 2 - ((23 * x + 100) * u) ^ 2) =
        g * (4 * (25 * x - 23) ^ 2) := by
    rw [mul_pow, ha2, hR2, mul_pow, hu2]
    field_simp
    ring
  have hsq : ((23 * x + 100) * u) ^ 2 ≤ (a * R) ^ 2 := by
    have hnon : 0 ≤ g * (4 * (25 * x - 23) ^ 2) := by positivity
    nlinarith
  have hleft0 : 0 ≤ (23 * x + 100) * u := mul_nonneg hlin hu0
  have hright0 : 0 ≤ a * R := mul_nonneg ha0 hR0
  have hle : (23 * x + 100) * u ≤ a * R := by nlinarith
  simpa [g, u, a, R] using hle

lemma u_lower :
    (106 : ℝ) / 3125 < Real.sqrt ((6 * s - 5) / 3029) := by
  let u : ℝ := Real.sqrt ((6 * s - 5) / 3029)
  have hg : 0 < 6 * s - 5 := by nlinarith [s_lower]
  have harg : 0 ≤ (6 * s - 5) / 3029 := by positivity
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu2 : u ^ 2 = (6 * s - 5) / 3029 := by
    dsimp [u]
    exact Real.sq_sqrt harg
  have hq : ((106 : ℝ) / 3125) ^ 2 < (6 * s - 5) / 3029 := by
    nlinarith [s_lower,
      show ((106 : ℝ) / 3125) ^ 2 < (6 * ((7071 : ℝ) / 5000) - 5) / 3029 by norm_num]
  norm_num at hu0 ⊢
  nlinarith

lemma amgm_two_over_x (x C : ℝ) (hx : 0 < x) (hC : 0 ≤ C) :
    2 * Real.sqrt C * s ≤ 2 / x + C * x := by
  have hsC : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
  have hsq : 0 ≤ (Real.sqrt C * x - s) ^ 2 := sq_nonneg _
  have hmul : (2 * Real.sqrt C * s) * x ≤ (2 / x + C * x) * x := by
    have hxne : x ≠ 0 := ne_of_gt hx
    rw [add_mul, div_mul_cancel₀ 2 hxne]
    nlinarith [s_sq]
  exact (mul_le_mul_right hx).mp hmul

lemma root4_lower (u : ℝ) (hu : (106 : ℝ) / 3125 < u) :
    (87 : ℝ) / 20 < 2 * Real.sqrt (3 - s + 23 * u) * s := by
  let C : ℝ := 3 - s + 23 * u
  have hCbound : (118297 : ℝ) / 50000 < C := by
    dsimp [C]
    nlinarith [s_upper, hu]
  have hC : 0 < C := by nlinarith
  have hsC : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC.le
  have hprod0 : 0 ≤ Real.sqrt C * s := mul_nonneg (Real.sqrt_nonneg _) s_nonneg
  have hsqprod : (Real.sqrt C * s) ^ 2 = 2 * C := by
    rw [mul_pow, hsC, s_sq]
    ring
  have hq : ((87 : ℝ) / 40) ^ 2 < 2 * C := by
    nlinarith [hCbound,
      show ((87 : ℝ) / 40) ^ 2 < 2 * ((118297 : ℝ) / 50000) by norm_num]
  have hroot : (87 : ℝ) / 40 < Real.sqrt C * s := by
    norm_num at hprod0 ⊢
    nlinarith
  nlinarith

lemma root5_lower (u : ℝ) (hu : (106 : ℝ) / 3125 < u) :
    (427 : ℝ) / 100 < 2 * Real.sqrt ((3 : ℝ) / 2 + 23 * u) * s := by
  let C : ℝ := (3 : ℝ) / 2 + 23 * u
  have hCbound : (14251 : ℝ) / 6250 < C := by
    dsimp [C]
    nlinarith [hu]
  have hC : 0 < C := by nlinarith
  have hsC : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC.le
  have hprod0 : 0 ≤ Real.sqrt C * s := mul_nonneg (Real.sqrt_nonneg _) s_nonneg
  have hsqprod : (Real.sqrt C * s) ^ 2 = 2 * C := by
    rw [mul_pow, hsC, s_sq]
    ring
  have hq : ((427 : ℝ) / 200) ^ 2 < 2 * C := by
    nlinarith [hCbound,
      show ((427 : ℝ) / 200) ^ 2 < 2 * ((14251 : ℝ) / 6250) by norm_num]
  have hroot : (427 : ℝ) / 200 < Real.sqrt C * s := by
    norm_num at hprod0 ⊢
    nlinarith
  nlinarith

lemma small_r4 (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ (1 : ℝ) / 2) :
    1 ≤ r4 x := by
  have h1 : 2 * x - 1 ≤ 0 := by linarith
  have h2 : x - 2 ≤ 0 := by linarith
  have hprod : 0 ≤ (2 * x - 1) * (x - 2) := mul_nonneg_of_nonpos_of_nonpos h1 h2
  have hid := PairGapLemma.smallR4Identity x (ne_of_gt hx)
  have hxmul : 0 ≤ x * (r4 x - 1) := by
    dsimp [r4]
    rw [hid]
    exact hprod
  nlinarith

lemma small_r5_gt_r4 (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ (1 : ℝ) / 2) :
    r4 x < r5 x := by
  have hcoef : 2 * s - 3 < 0 := by nlinarith [s_upper]
  have hterm : ((2 * s - 3) / 2) * x ≥ (2 * s - 3) / 4 := by
    have := mul_le_mul_of_nonpos_left hxhalf hcoef.le
    nlinarith
  have hp := p5_upper
  dsimp [r4, r5, A5]
  have hnum : 0 < (2 * s - 3) / 4 + 4 - p5 := by
    nlinarith [s_lower, hp,
      show 0 < (2 * ((7071 : ℝ) / 5000) - 3) / 4 + 4 - (3914 : ℝ) / 1000 by norm_num]
  nlinarith

/-- The strengthened quadrilateral pair gap. -/
theorem pair_gap_four (x f : ℝ) (hx : 0 < x) (hf : A8 ≤ f) :
    (101 : ℝ) / 1000 < r4 x + h x f := by
  by_cases hsmall : x ≤ (1 : ℝ) / 2
  · have hr := small_r4 x hx hsmall
    have hh := h_nonneg x f hx.le (le_trans A8_pos.le hf)
    norm_num
    linarith
  · have hxhalf : (1 : ℝ) / 2 ≤ x := le_of_not_ge hsmall
    have hm := h_mono_A8 x f hxhalf hf
    let u : ℝ := Real.sqrt ((6 * s - 5) / 3029)
    let C : ℝ := 3 - s + 23 * u
    have hu : (106 : ℝ) / 3125 < u := by simpa [u] using u_lower
    have hC0 : 0 ≤ C := by
      dsimp [C]
      nlinarith [s_upper, hu]
    have ht := tangent_product_lower x hxhalf
    have hamgm := amgm_two_over_x x C hx hC0
    have hroot := root4_lower u hu
    have hp := p8_upper
    have hlower :
        2 / x + C * x + 100 * u - 4 - p8 ≤ r4 x + h x A8 := by
      dsimp [r4, h, C, u]
      rw [fanAugment]
      nlinarith
    have hend :
        (101 : ℝ) / 1000 < 2 / x + C * x + 100 * u - 4 - p8 := by
      nlinarith [hamgm, hroot, hp]
    linarith

/-- The strengthened pentagonal pair gap (with the common 0.101 target). -/
theorem pair_gap_five (x f : ℝ) (hx : 0 < x) (hf : A8 ≤ f) :
    (101 : ℝ) / 1000 < r5 x + h x f := by
  by_cases hsmall : x ≤ (1 : ℝ) / 2
  · have hr4 := small_r4 x hx hsmall
    have hr5 := small_r5_gt_r4 x hx hsmall
    have hh := h_nonneg x f hx.le (le_trans A8_pos.le hf)
    norm_num
    linarith
  · have hxhalf : (1 : ℝ) / 2 ≤ x := le_of_not_ge hsmall
    have hm := h_mono_A8 x f hxhalf hf
    let u : ℝ := Real.sqrt ((6 * s - 5) / 3029)
    let C : ℝ := (3 : ℝ) / 2 + 23 * u
    have hu : (106 : ℝ) / 3125 < u := by simpa [u] using u_lower
    have hC0 : 0 ≤ C := by
      dsimp [C]
      nlinarith [hu]
    have ht := tangent_product_lower x hxhalf
    have hamgm := amgm_two_over_x x C hx hC0
    have hroot := root5_lower u hu
    have hp5 := p5_upper
    have hp8 := p8_upper
    have hlower :
        2 / x + C * x + 100 * u - p5 - p8 ≤ r5 x + h x A8 := by
      dsimp [r5, h, C, u, A5]
      rw [fanAugment]
      nlinarith
    have hend :
        (107 : ℝ) / 1000 < 2 / x + C * x + 100 * u - p5 - p8 := by
      nlinarith [hamgm, hroot, hp5, hp8]
    linarith

/-- The actual pair-gap lemma used by the discharging argument. -/
theorem pair_gap_full (x f : ℝ) (hx : 0 < x) (hf : A8 ≤ f) :
    (101 : ℝ) / 1000 < r4 x + h x f ∧
      (101 : ℝ) / 1000 < r5 x + h x f :=
  ⟨pair_gap_four x f hx hf, pair_gap_five x f hx hf⟩

end

end PairGapFull
