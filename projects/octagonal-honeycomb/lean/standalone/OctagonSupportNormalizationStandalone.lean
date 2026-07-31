import OctagonBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact support normalization for the regular octagon

The isoperimetrix has apothem one.  Its circumradius is
`sqrt (4 - 2 sqrt 2)`, and the two boundary support identities are proved
from double-angle formulas.
-/

namespace OctagonSupportNormalizationStandalone

noncomputable section

open Real
open OctagonBase

/-- Circumradius of the regular octagon with apothem one. -/
def R : ℝ := Real.sqrt (4 - 2 * s)

lemma radicand_pos : 0 < 4 - 2 * s := by
  nlinarith [s_upper]

lemma R_nonneg : 0 ≤ R := by
  dsimp [R]
  positivity

lemma R_pos : 0 < R := by
  dsimp [R]
  exact Real.sqrt_pos.2 radicand_pos

lemma R_sq : R ^ 2 = 4 - 2 * s := by
  dsimp [R]
  exact Real.sq_sqrt radicand_pos.le

lemma eighth_nonneg : 0 ≤ Real.pi / 8 := by positivity

lemma eighth_le_pi : Real.pi / 8 ≤ Real.pi := by
  nlinarith [Real.pi_pos]

lemma sin_eighth_nonneg : 0 ≤ Real.sin (Real.pi / 8) :=
  Real.sin_nonneg_of_nonneg_of_le_pi eighth_nonneg eighth_le_pi

lemma cos_eighth_pos : 0 < Real.cos (Real.pi / 8) := by
  have hmem : Real.pi / 8 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  exact Real.cos_pos_of_mem_Ioo hmem

lemma cos_eighth_nonneg : 0 ≤ Real.cos (Real.pi / 8) := cos_eighth_pos.le

lemma cos_eighth_sq :
    Real.cos (Real.pi / 8) ^ 2 = (2 + s) / 4 := by
  have hdouble := Real.cos_two_mul (Real.pi / 8)
  have hangle : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
  rw [hangle, Real.cos_pi_div_four] at hdouble
  dsimp [s] at hdouble ⊢
  nlinarith

lemma sin_eighth_sq :
    Real.sin (Real.pi / 8) ^ 2 = (2 - s) / 4 := by
  have htrig := Real.sin_sq_add_cos_sq (Real.pi / 8)
  rw [cos_eighth_sq] at htrig
  nlinarith

lemma R_mul_cos_sq :
    (R * Real.cos (Real.pi / 8)) ^ 2 = 1 := by
  rw [mul_pow, R_sq, cos_eighth_sq]
  nlinarith [s_sq]

lemma R_mul_sin_sq :
    (R * Real.sin (Real.pi / 8)) ^ 2 = d ^ 2 := by
  rw [mul_pow, R_sq, sin_eighth_sq]
  dsimp [d]
  nlinarith [s_sq]

/-- Apothem-one normalization. -/
theorem R_mul_cos_eighth :
    R * Real.cos (Real.pi / 8) = 1 := by
  have hnonneg : 0 ≤ R * Real.cos (Real.pi / 8) :=
    mul_nonneg R_nonneg cos_eighth_nonneg
  nlinarith [R_mul_cos_sq]

/-- Tangential boundary support ratio. -/
theorem R_mul_sin_eighth :
    R * Real.sin (Real.pi / 8) = d := by
  have hnonneg : 0 ≤ R * Real.sin (Real.pi / 8) :=
    mul_nonneg R_nonneg sin_eighth_nonneg
  nlinarith [R_mul_sin_sq, d_nonneg]

end

end OctagonSupportNormalizationStandalone
