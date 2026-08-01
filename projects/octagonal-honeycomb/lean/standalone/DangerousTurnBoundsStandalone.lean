import PentagonMiddleDefectGenerated
import FirstSectorDefectStandalone
import SecondSectorDefectStandalone
import ThirdSectorDefectStandalone
import SmallGapReserveStandalone
import ArctanSeventhLower
import OctagonBenchmarkStandalone

/-!
# Quantitative angular windows for potentially negative cells

This module turns the sector-defect estimates into the rational angular
windows used by the interval certificate.  Angles here are in radians.
-/

namespace DangerousTurnBoundsStandalone

noncomputable section

open Real
open OctagonBase
open OctagonBenchmarkStandalone
open FirstSectorAlgebra
open FirstSectorScalar
open FirstSectorDefectStandalone
open SecondSectorDefectStandalone
open ThirdSectorDefectStandalone
open SmallGapReserveStandalone
open PentagonMiddleDefectGenerated
open ArctanSeventhLower


def affineBaseline (alpha : ℝ) : ℝ :=
  phaseSlope * (alpha / Real.pi) - cap


def phaseDefect (alpha beta : ℝ) : ℝ :=
  sectorMinimum alpha beta - affineBaseline alpha

lemma phaseSlope_div_pi_le_four_fifths :
    phaseSlope / Real.pi ≤ (4 : ℝ) / 5 := by
  have hslope : phaseSlope < (12 : ℝ) / 5 := by
    dsimp [phaseSlope]
    nlinarith [s_lower]
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  apply (div_le_iff₀ Real.pi_pos).2
  nlinarith

lemma three_fifths_le_s_sub_phase_coefficient :
    (3 : ℝ) / 5 ≤ s - phaseSlope / Real.pi := by
  nlinarith [s_lower, phaseSlope_div_pi_le_four_fifths]

/-- Quantitative lower bound throughout the second large sector. -/
theorem second_defect_lower
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4) :
    ((3 : ℝ) / 5) * beta ≤ phaseDefect (Real.pi / 2 + beta) beta := by
  have hcos := SecondSectorDefectStandalone.cos_beta_pos beta hb0 hbq
  have hsin0 := SecondSectorDefectStandalone.sin_beta_nonneg beta hb0 hbq
  have ht0 : 0 ≤ Real.sin beta / Real.cos beta :=
    div_nonneg hsin0 hcos.le
  have hsquare := SecondSectorDefectStandalone.support_sq_ge_one beta hb0 hbq
  have hmul := mul_le_mul_of_nonneg_right hsquare ht0
  have hformula := SecondSectorDefectStandalone.sectorMinimum_second_formula beta hcos.ne'
  have hminimum :
      1 + s * (Real.sin beta / Real.cos beta) ≤
        sectorMinimum (Real.pi / 2 + beta) beta := by
    rw [hformula]
    dsimp [d]
    nlinarith
  have htan := SecondSectorDefectStandalone.beta_le_tan_beta beta hb0 hbq
  have htanScaled := mul_le_mul_of_nonneg_left htan s_nonneg
  have hcoef := three_fifths_le_s_sub_phase_coefficient
  have hcoefScaled := mul_le_mul_of_nonneg_right hcoef hb0
  have hphase :
      phaseSlope * (beta / Real.pi) =
        (phaseSlope / Real.pi) * beta := by ring
  change ((3 : ℝ) / 5) * beta ≤
    sectorMinimum (Real.pi / 2 + beta) beta -
      (phaseSlope * ((Real.pi / 2 + beta) / Real.pi) - cap)
  rw [SecondSectorDefectStandalone.second_baseline_identity]
  rw [hphase]
  nlinarith

lemma nine_over_two_fifty_lt_second_defect_of_pi_fifty_le
    (beta : ℝ) (hb : Real.pi / 50 ≤ beta) (hbq : beta ≤ Real.pi / 4) :
    (9 : ℝ) / 250 < phaseDefect (Real.pi / 2 + beta) beta := by
  have hb0 : 0 ≤ beta := le_trans (by positivity) hb
  have hdef := second_defect_lower beta hb0 hbq
  have hpi : (9 : ℝ) / 250 < ((3 : ℝ) / 5) * beta := by
    nlinarith [Real.pi_gt_three]
  linarith

lemma eta4_lt_second_defect_of_pi_fifty_le
    (beta : ℝ) (hb : Real.pi / 50 ≤ beta) (hbq : beta ≤ Real.pi / 4) :
    eta4 < phaseDefect (Real.pi / 2 + beta) beta := by
  have hlarge := nine_over_two_fifty_lt_second_defect_of_pi_fifty_le beta hb hbq
  have heta := eta4_lt_seventeen_thousandths
  norm_num at heta ⊢
  linarith

lemma eta4_lt_second_defect_of_three_pi_hundred_le
    (beta : ℝ) (hb : 3 * Real.pi / 100 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) :
    eta4 < phaseDefect (Real.pi / 2 + beta) beta := by
  have hweak : Real.pi / 50 ≤ beta := by nlinarith [Real.pi_pos]
  exact eta4_lt_second_defect_of_pi_fifty_le beta hweak hbq

/-- Every turn in the third residual sector has a large phase penalty. -/
theorem one_fifth_lt_third_defect
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta < Real.pi / 4) :
    (1 : ℝ) / 5 < phaseDefect (3 * Real.pi / 4 + beta) beta := by
  have hmin := ThirdSectorDefectStandalone.third_sector_min_ge_s_add_one beta hb0 hbq
  have hu : (3 * Real.pi / 4 + beta) / Real.pi < 1 := by
    apply (div_lt_one Real.pi_pos).2
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hu phaseSlope_pos
  have hbase :
      affineBaseline (3 * Real.pi / 4 + beta) < phaseSlope - cap := by
    dsimp [affineBaseline]
    nlinarith
  have hconstant : (1 : ℝ) / 5 < s + 1 - (phaseSlope - cap) := by
    dsimp [phaseSlope, cap, d]
    nlinarith [s_sq, s_lower]
  dsimp [phaseDefect]
  nlinarith

lemma eta4_lt_third_defect
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta < Real.pi / 4) :
    eta4 < phaseDefect (3 * Real.pi / 4 + beta) beta := by
  have hthird := one_fifth_lt_third_defect beta hb0 hbq
  have heta := eta4_lt_seventeen_thousandths
  norm_num at heta ⊢
  linarith

/-- The small-gap reserve excludes turns at or below 43 degrees for a
negative pentagonal owner. -/
theorem eta5_lt_small_defect_of_le_fortythree_degrees
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ (43 : ℝ) / 180) :
    eta5 < smallPhaseDefect u := by
  have huq : u ≤ (1 : ℝ) / 4 := by nlinarith
  have hreserve := small_gap_reserve u hu0 huq
  have hline : (8 : ℝ) / 1125 ≤ smallGapReserve * (1 - 4 * u) := by
    dsimp [smallGapReserve]
    nlinarith
  have heta := eta5_lt_seven_thousandths
  have hcompare : (7 : ℝ) / 1000 < (8 : ℝ) / 1125 := by norm_num
  linarith

/-- On the middle tangent interval, the actual first-sector defect exceeds
all possible pentagonal debt. -/
theorem eta5_lt_first_middle_defect
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4)
    (ht0 : (1 : ℝ) / 5 ≤ Real.tan beta)
    (ht1 : Real.tan beta ≤ (7 : ℝ) / 8) :
    eta5 < phaseDefect (Real.pi / 4 + beta) beta := by
  have hcos := FirstSectorDefectStandalone.cos_beta_pos beta hb0 hbq
  have hsin := FirstSectorDefectStandalone.sin_beta_nonneg beta hb0 hbq
  have hsum : 0 < Real.cos beta + Real.sin beta :=
    add_pos_of_pos_of_nonneg hcos hsin
  have hmiddle := eta5_lt_middle_phase_defect (Real.tan beta) ht0 ht1
  have hatan : Real.arctan (Real.tan beta) = beta := by
    apply Real.arctan_tan
    · nlinarith [hb0, Real.pi_pos]
    · nlinarith [hbq, Real.pi_pos]
  rw [hatan] at hmiddle
  change eta5 <
    sectorMinimum (Real.pi / 4 + beta) beta -
      (phaseSlope * ((Real.pi / 4 + beta) / Real.pi) - cap)
  rw [FirstSectorDefectStandalone.first_sector_formula beta hcos.ne' hsum.ne',
    FirstSectorDefectStandalone.first_baseline_identity]
  exact hmiddle

lemma first_angle_low_of_tan_lt_one_fifth
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4)
    (ht : Real.tan beta < (1 : ℝ) / 5) :
    Real.pi / 4 + beta < 19 * Real.pi / 60 := by
  have ht0 : 0 ≤ Real.tan beta := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg
      (FirstSectorDefectStandalone.sin_beta_nonneg beta hb0 hbq)
      (FirstSectorDefectStandalone.cos_beta_pos beta hb0 hbq).le
  have hatan : Real.arctan (Real.tan beta) = beta := by
    apply Real.arctan_tan
    · nlinarith [hb0, Real.pi_pos]
    · nlinarith [hbq, Real.pi_pos]
  have hsmall := arctan_lt_pi_over_fifteen_of_lt_one_fifth
    (Real.tan beta) ht0 ht
  rw [hatan] at hsmall
  nlinarith [Real.pi_pos]

lemma first_angle_high_of_seven_eighths_lt_tan
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4)
    (ht : (7 : ℝ) / 8 < Real.tan beta) :
    47 * Real.pi / 100 < Real.pi / 4 + beta := by
  have hatan : Real.arctan (Real.tan beta) = beta := by
    apply Real.arctan_tan
    · nlinarith [hb0, Real.pi_pos]
    · nlinarith [hbq, Real.pi_pos]
  have hlarge := eleven_pi_over_fifty_lt_arctan_of_seven_eighths_lt
    (Real.tan beta) ht
  rw [hatan] at hlarge
  nlinarith [Real.pi_pos]

/-- A first-sector turn whose defect is below the pentagonal threshold is
forced into one of two separated angular windows. -/
theorem first_sector_low_or_high_of_defect_lt_eta5
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4)
    (hdef : phaseDefect (Real.pi / 4 + beta) beta < eta5) :
    Real.pi / 4 + beta < 19 * Real.pi / 60 ∨
      47 * Real.pi / 100 < Real.pi / 4 + beta := by
  by_cases hlo : Real.tan beta < (1 : ℝ) / 5
  · exact Or.inl (first_angle_low_of_tan_lt_one_fifth beta hb0 hbq hlo)
  · have hlo' : (1 : ℝ) / 5 ≤ Real.tan beta := le_of_not_gt hlo
    by_cases hhi : (7 : ℝ) / 8 < Real.tan beta
    · exact Or.inr (first_angle_high_of_seven_eighths_lt_tan beta hb0 hbq hhi)
    · have hhi' : Real.tan beta ≤ (7 : ℝ) / 8 := le_of_not_gt hhi
      have hcontra := eta5_lt_first_middle_defect beta hb0 hbq hlo' hhi'
      linarith

end

end DangerousTurnBoundsStandalone
