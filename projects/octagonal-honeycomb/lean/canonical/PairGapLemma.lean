import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact certificate layer for the crystalline pair-gap lemma

This file formalizes the polynomial identities and final rational arithmetic
used in the strengthened proof

  r_m(x) + h_f(x) > 101/1000.

It deliberately separates the exact certificate layer from the order lemmas
about `Real.sqrt`.  The accompanying proof note supplies those order lemmas;
the two Python verifiers check the full chain independently.

There are no `sorry`s in this file.
-/

namespace PairGapLemma

noncomputable section

/-- The perfect-square identity behind `h_f(x) >= 0`, with `y = sqrt f`. -/
lemma hSquareIdentity (x y d : ℝ) :
    (y ^ 2 + d ^ 2) * (x ^ 2 + 4) - (d * x + 2 * y) ^ 2 =
      (x * y - 2 * d) ^ 2 := by
  ring

/-- Cross-multiplied form of the algebraic monotonicity difference quotient.
Here `A` and `B` stand for `sqrt (y^2+d^2)` and
`sqrt (y0^2+d^2)`. -/
lemma monotonicityCrossIdentity
    (R y y0 A B : ℝ) (hAB : A ^ 2 - B ^ 2 = y ^ 2 - y0 ^ 2) :
    (R * (A - B) - 2 * (y - y0)) * (A + B) =
      (y - y0) * (R * (y + y0) - 2 * (A + B)) := by
  calc
    (R * (A - B) - 2 * (y - y0)) * (A + B) =
        (y - y0) * (R * (y + y0) - 2 * (A + B)) +
          R * ((A ^ 2 - B ^ 2) - (y ^ 2 - y0 ^ 2)) := by ring
    _ = (y - y0) * (R * (y + y0) - 2 * (A + B)) := by rw [hAB]; ring

/-- Exact tangent certificate at `x = 23/25`. -/
lemma tangent2325Identity (x : ℝ) :
    3029 * (x ^ 2 + 4) - (23 * x + 100) ^ 2 =
      4 * (25 * x - 23) ^ 2 := by
  ring

/-- Exact factorization used in the small-edge quadrilateral branch. -/
lemma smallR4Identity (x : ℝ) (hx : x ≠ 0) :
    x * (2 / x + 2 * x - 5) = (2 * x - 1) * (x - 2) := by
  field_simp [hx]
  ring

/-- Rational square margins used to bracket `sqrt 2`. -/
lemma sqrtTwoLowerSquareMargin :
    (2 : ℚ) - (7071 / 5000 : ℚ) ^ 2 = 959 / 25000000 := by
  norm_num

lemma sqrtTwoUpperSquareMargin :
    (70711 / 50000 : ℚ) ^ 2 - 2 = 45521 / 2500000000 := by
  norm_num

/-- Rational square margin proving `u > 106/3125` after inserting the lower
bracket for `sqrt 2`. -/
lemma uLowerSquareMargin :
    ((6 * (7071 / 5000 : ℚ) - 5) / 3029) -
        (106 / 3125 : ℚ) ^ 2 = 5249 / 118320312500 := by
  norm_num

/-- Rational square margins for the perimeter constants. -/
lemma p8UpperSquareMargin :
    (3641 / 1000 : ℚ) ^ 2 -
        32 * ((70711 / 50000 : ℚ) - 1) = 1841 / 1000000 := by
  norm_num

lemma p5UpperSquareMargin :
    (3914 / 1000 : ℚ) ^ 2 -
        (4 + 8 * (70711 / 50000 : ℚ)) = 1409 / 250000 := by
  norm_num

/-- The exact lower bounds for the AM-GM coefficients. -/
lemma c4LowerArithmetic :
    3 - (70711 / 50000 : ℚ) + 23 * (106 / 3125 : ℚ) =
      118297 / 50000 := by
  norm_num

lemma c5LowerArithmetic :
    (3 / 2 : ℚ) + 23 * (106 / 3125 : ℚ) = 14251 / 6250 := by
  norm_num

/-- Square margins for the two AM-GM root terms. -/
lemma root4SquareMargin :
    2 * (118297 / 50000 : ℚ) - (87 / 40 : ℚ) ^ 2 =
      251 / 200000 := by
  norm_num

lemma root5SquareMargin :
    2 * (14251 / 6250 : ℚ) - (427 / 200 : ℚ) ^ 2 =
      419 / 200000 := by
  norm_num

/-- The exact final arithmetic for the quadrilateral branch. -/
lemma finalGap4Arithmetic :
    (87 / 20 : ℚ) + 100 * (106 / 3125 : ℚ) - 4 - 3641 / 1000 =
      101 / 1000 := by
  norm_num

/-- The exact final arithmetic for the pentagonal branch. -/
lemma finalGap5Arithmetic :
    (427 / 100 : ℚ) + 100 * (106 / 3125 : ℚ) -
        3914 / 1000 - 3641 / 1000 = 107 / 1000 := by
  norm_num

/-- Formal glue for the strict quadrilateral endgame. -/
theorem finishM4
    (rootTerm u p8 : ℝ)
    (hroot : (87 : ℝ) / 20 < rootTerm)
    (hu : (106 : ℝ) / 3125 < u)
    (hp8 : p8 < (3641 : ℝ) / 1000) :
    (101 : ℝ) / 1000 < rootTerm + 100 * u - 4 - p8 := by
  norm_num at *
  linarith

/-- Formal glue for the strict pentagonal endgame. -/
theorem finishM5
    (rootTerm u p5 p8 : ℝ)
    (hroot : (427 : ℝ) / 100 < rootTerm)
    (hu : (106 : ℝ) / 3125 < u)
    (hp5 : p5 < (3914 : ℝ) / 1000)
    (hp8 : p8 < (3641 : ℝ) / 1000) :
    (107 : ℝ) / 1000 < rootTerm + 100 * u - p5 - p8 := by
  norm_num at *
  linarith

end

end PairGapLemma
