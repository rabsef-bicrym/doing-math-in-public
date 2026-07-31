import ArctanPolynomialBounds
import FirstSectorAlgebra
import Mathlib.Analysis.Real.Pi.Bounds

namespace FirstSectorScalar

noncomputable section

open Real
open OctagonBase
open ArctanPolynomialBounds
open FirstSectorAlgebra

def exactK : ℝ := 4 * c / Real.pi

lemma exactK_nonneg : 0 ≤ exactK := by
  dsimp [exactK]
  exact div_nonneg (mul_nonneg (by norm_num) c_nonneg) Real.pi_pos.le

lemma lowK_nonneg : 0 ≤ lowK := by
  dsimp [lowK]
  exact div_nonneg (mul_nonneg (by norm_num) c_nonneg) (by norm_num)

lemma highK_nonneg : 0 ≤ highK := by
  dsimp [highK]
  exact div_nonneg (mul_nonneg (by norm_num) c_nonneg) (by norm_num)

lemma exactK_le_lowK : exactK ≤ lowK := by
  have hpi : (157 : ℝ) / 50 ≤ Real.pi := by
    have h := Real.pi_gt_d2.le
    convert h using 1
    all_goals norm_num
  have hcoef : 0 ≤ 200 * c / 157 := by
    exact div_nonneg (mul_nonneg (by norm_num) c_nonneg) (by norm_num)
  apply (div_le_iff₀ Real.pi_pos).2
  dsimp [exactK, lowK]
  calc
    4 * c = (200 * c / 157) * ((157 : ℝ) / 50) := by ring
    _ ≤ (200 * c / 157) * Real.pi :=
      mul_le_mul_of_nonneg_left hpi hcoef

lemma highK_le_exactK : highK ≤ exactK := by
  have hpi : Real.pi ≤ (63 : ℝ) / 20 := by
    have h := Real.pi_lt_d2.le
    convert h using 1
    all_goals norm_num
  have hcoef : 0 ≤ 80 * c / 63 := by
    exact div_nonneg (mul_nonneg (by norm_num) c_nonneg) (by norm_num)
  apply (le_div_iff₀ Real.pi_pos).2
  dsimp [exactK, highK]
  calc
    (80 * c / 63) * Real.pi ≤
        (80 * c / 63) * ((63 : ℝ) / 20) :=
      mul_le_mul_of_nonneg_left hpi hcoef
    _ = 4 * c := by ring

lemma exactK_mul_pi_div_four : exactK * (Real.pi / 4) = c := by
  dsimp [exactK]
  field_simp [Real.pi_ne_zero]

lemma u_nonneg (t : ℝ) (ht1 : t ≤ 1) (htm : -1 < t) : 0 ≤ u t := by
  dsimp [u]
  exact div_nonneg (sub_nonneg.mpr ht1) (by linarith)

lemma u_le_quarter (t : ℝ) (ht : (3 : ℝ) / 5 ≤ t) : u t ≤ (1 : ℝ) / 4 := by
  have hden : 0 < 1 + t := by nlinarith
  dsimp [u]
  apply (div_le_iff₀ hden).2
  nlinarith

lemma cubic_u_nonneg (t : ℝ) (ht : (3 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ cubic (u t) := by
  have htm : -1 < t := by nlinarith
  have hu0 := u_nonneg t ht1 htm
  have huq := u_le_quarter t ht
  have hu2raw : u t * u t ≤ ((1 : ℝ) / 4) * ((1 : ℝ) / 4) :=
    mul_le_mul huq huq hu0 (by norm_num)
  have hfactor : 0 ≤ 1 - (u t) ^ 2 / 3 := by
    nlinarith
  have hid : cubic (u t) = u t * (1 - (u t) ^ 2 / 3) := by
    dsimp [cubic]
    ring
  rw [hid]
  exact mul_nonneg hu0 hfactor

lemma arctan_complement
    (t : ℝ) (ht : (3 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    Real.arctan t = Real.pi / 4 - Real.arctan (u t) := by
  have ht0 : 0 ≤ t := by nlinarith
  have htm : -1 < t := by nlinarith
  have hu0 := u_nonneg t ht1 htm
  have huq := u_le_quarter t ht
  have htu : t * u t < 1 := by
    have hmul : t * u t ≤ 1 * ((1 : ℝ) / 4) :=
      mul_le_mul ht1 huq hu0 (by norm_num)
    nlinarith
  have hadd := Real.arctan_add htu
  have hbase : 0 < 1 + t := by linarith
  have hnum : t + u t = (1 + t ^ 2) / (1 + t) := by
    dsimp [u]
    field_simp [hbase.ne']
    ring
  have hden : 1 - t * u t = (1 + t ^ 2) / (1 + t) := by
    dsimp [u]
    field_simp [hbase.ne']
    ring
  have hquot : 0 < (1 + t ^ 2) / (1 + t) := by positivity
  have hfrac : (t + u t) / (1 - t * u t) = 1 := by
    rw [hnum, hden]
    exact div_self hquot.ne'
  rw [hfrac, Real.arctan_one] at hadd
  linarith

lemma low_scalar
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ (3 : ℝ) / 5) :
    exactK * Real.arctan t ≤ firstLhs t := by
  have hatan0 : 0 ≤ Real.arctan t := Real.arctan_nonneg.mpr ht0
  have hquint := arctan_le_quintic t ht0
  calc
    exactK * Real.arctan t ≤ lowK * Real.arctan t :=
      mul_le_mul_of_nonneg_right exactK_le_lowK hatan0
    _ ≤ lowK * quintic t :=
      mul_le_mul_of_nonneg_left hquint lowK_nonneg
    _ ≤ firstLhs t := low_gap_nonneg t ht0 ht1

lemma high_scalar
    (t : ℝ) (ht : (3 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    exactK * Real.arctan t ≤ firstLhs t := by
  have ht0 : 0 ≤ t := by nlinarith
  have htm : -1 < t := by nlinarith
  have hu0 := u_nonneg t ht1 htm
  have hcubic := cubic_le_arctan (u t) hu0
  have hcomp := arctan_complement t ht ht1
  have hR0 := cubic_u_nonneg t ht ht1
  have hkR := mul_le_mul_of_nonneg_right highK_le_exactK hR0
  have hm : exactK * cubic (u t) ≤ exactK * Real.arctan (u t) := by
    apply mul_le_mul_of_nonneg_left
    · simpa [cubic] using hcubic
    · exact exactK_nonneg
  have hupper :
      exactK * Real.arctan t ≤ c - exactK * cubic (u t) := by
    rw [hcomp]
    rw [mul_sub, exactK_mul_pi_div_four]
    linarith
  calc
    exactK * Real.arctan t ≤ c - exactK * cubic (u t) := hupper
    _ ≤ c - highK * cubic (u t) := by linarith
    _ ≤ firstLhs t := high_gap_nonneg t ht ht1

theorem first_sector_scalar
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    exactK * Real.arctan t ≤ firstLhs t := by
  by_cases h : t ≤ (3 : ℝ) / 5
  · exact low_scalar t ht0 h
  · exact high_scalar t (le_of_not_ge h) ht1

end

end FirstSectorScalar
