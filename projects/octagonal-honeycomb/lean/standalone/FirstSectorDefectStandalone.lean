import FirstSectorScalar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Nonnegativity of the phase defect on `[pi/4, pi/2]`

Substituting `t = tan beta` identifies the exact tangent-wedge excess with the
scalar expression certified in `FirstSectorScalar`.
-/

namespace FirstSectorDefectStandalone

noncomputable section

open Real
open OctagonBase
open FirstSectorAlgebra
open FirstSectorScalar

lemma sin_beta_nonneg (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) : 0 ≤ Real.sin beta := by
  exact Real.sin_nonneg_of_nonneg_of_le_pi hb0
    (by nlinarith [hbq, Real.pi_pos])

lemma cos_beta_pos (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) : 0 < Real.cos beta := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [hb0, hbq, Real.pi_pos]

lemma sin_beta_le_cos_beta (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) : Real.sin beta ≤ Real.cos beta := by
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two
    (x := beta) (y := Real.pi / 2 - beta)
    (by nlinarith [hb0, Real.pi_pos])
    (by nlinarith [hb0])
    (by nlinarith [hbq])
  simpa [Real.sin_pi_div_two_sub] using h

lemma first_angle_sin (beta : ℝ) :
    Real.sin (Real.pi / 4 + beta) =
      (s / 2) * (Real.cos beta + Real.sin beta) := by
  rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
  dsimp [s]
  ring

lemma first_angle_cos (beta : ℝ) :
    Real.cos (Real.pi / 4 + beta) =
      (s / 2) * (Real.cos beta - Real.sin beta) := by
  rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
  dsimp [s]
  ring

lemma first_wedge_algebra
    (S C : ℝ) (hCS : C + S ≠ 0)
    (htrig : S ^ 2 + C ^ 2 = 1) :
    2 * (C + d * S) / (s * (C + S)) -
        (1 + (C + d * S) ^ 2) * (C - S) / (2 * (C + S)) =
      d + d * S * (C + S) + c ^ 2 * S / (C + S) := by
  dsimp [c, d]
  field_simp [hCS, s_pos.ne']
  linear_combination
    (-4 * C ^ 2 * S - C * S ^ 2 * s - 2 * C + S ^ 3 * s -
      4 * S ^ 3 - 2 * S * s + 6 * S) * s_sq +
    (-C * s + 5 * S * s - 8 * S) * htrig

lemma firstLhs_ratio
    (S C : ℝ) (hC : C ≠ 0) (hCS : C + S ≠ 0)
    (htrig : S ^ 2 + C ^ 2 = 1) :
    firstLhs (S / C) =
      d * S * (C + S) + c ^ 2 * S / (C + S) := by
  have hunit : C ^ 2 + S ^ 2 ≠ 0 := by
    have : C ^ 2 + S ^ 2 = 1 := by nlinarith [htrig]
    nlinarith
  dsimp [firstLhs, c, d]
  field_simp [hC, hCS, hunit]
  linear_combination
    (-S * (C + S) ^ 2 * (s - 1)) * htrig

lemma first_wedge_rewrite
    (S C : ℝ) (hCS : C + S ≠ 0) :
    (C + d * S) / ((s / 2) * (C + S)) -
        (1 + (C + d * S) ^ 2) * ((s / 2) * (C - S)) /
          (2 * ((s / 2) * (C + S))) =
      2 * (C + d * S) / (s * (C + S)) -
        (1 + (C + d * S) ^ 2) * (C - S) / (2 * (C + S)) := by
  field_simp [hCS, s_pos.ne']

lemma first_sector_formula
    (beta : ℝ)
    (hcos : Real.cos beta ≠ 0)
    (hsum : Real.cos beta + Real.sin beta ≠ 0) :
    sectorMinimum (Real.pi / 4 + beta) beta =
      d + firstLhs (Real.tan beta) := by
  let S : ℝ := Real.sin beta
  let C : ℝ := Real.cos beta
  have htrig : S ^ 2 + C ^ 2 = 1 := by
    dsimp [S, C]
    exact Real.sin_sq_add_cos_sq beta
  have hCS : C + S ≠ 0 := by simpa [S, C] using hsum
  have hC : C ≠ 0 := by simpa [C] using hcos
  have hw := first_wedge_algebra S C hCS htrig
  have hl := firstLhs_ratio S C hC hCS htrig
  have hr := first_wedge_rewrite S C hCS
  have hraw :
      sectorMinimum (Real.pi / 4 + beta) beta =
        d + firstLhs (S / C) := by
    dsimp [sectorMinimum, wedge]
    rw [first_angle_sin, first_angle_cos]
    simp only [one_mul, one_pow]
    calc
      (C + d * S) / ((s / 2) * (C + S)) -
          (1 + (C + d * S) ^ 2) * ((s / 2) * (C - S)) /
            (2 * ((s / 2) * (C + S))) =
        2 * (C + d * S) / (s * (C + S)) -
          (1 + (C + d * S) ^ 2) * (C - S) / (2 * (C + S)) := hr
      _ = d + d * S * (C + S) + c ^ 2 * S / (C + S) := hw
      _ = d + firstLhs (S / C) := by rw [hl]; ring
  simpa [S, C, Real.tan_eq_sin_div_cos] using hraw

lemma phaseSlope_eq_four_c : phaseSlope = 4 * c := by
  rfl

lemma phase_beta_identity (beta : ℝ) :
    phaseSlope * (beta / Real.pi) = exactK * beta := by
  rw [phaseSlope_eq_four_c]
  dsimp [exactK]
  field_simp [Real.pi_ne_zero]

lemma first_baseline_identity (beta : ℝ) :
    phaseSlope * ((Real.pi / 4 + beta) / Real.pi) - cap =
      d + exactK * beta := by
  have hsplit :
      (Real.pi / 4 + beta) / Real.pi =
        (1 : ℝ) / 4 + beta / Real.pi := by
    field_simp [Real.pi_ne_zero]
  have hconst : phaseSlope / 4 - cap = d := by
    dsimp [phaseSlope, cap, d]
    nlinarith [s_sq]
  calc
    phaseSlope * ((Real.pi / 4 + beta) / Real.pi) - cap =
        phaseSlope * ((1 : ℝ) / 4 + beta / Real.pi) - cap := by rw [hsplit]
    _ = (phaseSlope / 4 - cap) + phaseSlope * (beta / Real.pi) := by ring
    _ = d + exactK * beta := by rw [hconst, phase_beta_identity]

theorem first_sector_defect_nonneg
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4) :
    0 ≤ sectorMinimum (Real.pi / 4 + beta) beta -
      (phaseSlope * ((Real.pi / 4 + beta) / Real.pi) - cap) := by
  have hcos := cos_beta_pos beta hb0 hbq
  have hsin := sin_beta_nonneg beta hb0 hbq
  have hsum : 0 < Real.cos beta + Real.sin beta :=
    add_pos_of_pos_of_nonneg hcos hsin
  have ht0 : 0 ≤ Real.tan beta := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg hsin hcos.le
  have ht1 : Real.tan beta ≤ 1 := by
    rw [Real.tan_eq_sin_div_cos]
    exact (div_le_one hcos).2 (sin_beta_le_cos_beta beta hb0 hbq)
  have hscalar := first_sector_scalar (Real.tan beta) ht0 ht1
  have hatan : Real.arctan (Real.tan beta) = beta := by
    apply Real.arctan_tan
    · nlinarith [hb0, Real.pi_pos]
    · nlinarith [hbq, Real.pi_pos]
  rw [hatan] at hscalar
  rw [first_sector_formula beta hcos.ne' hsum.ne', first_baseline_identity]
  nlinarith

end

end FirstSectorDefectStandalone
