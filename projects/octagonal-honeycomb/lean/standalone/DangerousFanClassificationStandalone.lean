import FirstSectorClassificationAlgebra
import ReducedFanBridgeStandalone
import Mathlib.Analysis.Real.Pi.Bounds

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Rigorous angular classification of potentially negative cells

A negative quadrilateral has total phase defect below `eta4 < 0.017`; a
negative pentagon has total phase defect below `eta5 < 4/625`.  This module
proves the one-gap quantitative bounds that force:

* every negative quadrilateral turn to be below `92°`;
* every negative pentagon turn to lie either in `(43°,58°)` or `(87°,91°)`.

The latter windows, together with the turn sum, force exactly three high turns
and hence a selectable high--high side.
-/

namespace DangerousFanClassificationStandalone

noncomputable section

open Real
open OctagonBase
open OctagonBenchmarkStandalone
open FirstSectorAlgebra
open FirstSectorScalar
open FirstSectorClassificationAlgebra
open ArctanPolynomialBounds
open AllSectorDefectStandalone
open PhaseGapBridgeStandalone
open ReducedFanBridgeStandalone
open SmallGapReserveStandalone

/-- `4c/pi` is safely below `4/5`. -/
lemma phaseSlope_div_pi_le_four_fifths :
    phaseSlope / Real.pi ≤ (4 : ℝ) / 5 := by
  have hslope : phaseSlope < (12 : ℝ) / 5 := by
    dsimp [phaseSlope]
    nlinarith [s_lower]
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  apply (div_le_iff₀ Real.pi_pos).2
  have hright : (12 : ℝ) / 5 ≤ ((4 : ℝ) / 5) * Real.pi := by
    nlinarith
  linarith

/-- Quantitative lower bound throughout the second residual sector. -/
theorem second_sector_defect_ge
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4) :
    ((3 : ℝ) / 5) * beta ≤
      phaseDefect (Real.pi / 2 + beta) beta := by
  have hcos := SecondSectorDefectStandalone.cos_beta_pos beta hb0 hbq
  have hsin0 := SecondSectorDefectStandalone.sin_beta_nonneg beta hb0 hbq
  let T : ℝ := Real.sin beta / Real.cos beta
  let K : ℝ := Real.cos beta + d * Real.sin beta
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact div_nonneg hsin0 hcos.le
  have hKsq : 1 ≤ K ^ 2 := by
    dsimp [K]
    exact SecondSectorDefectStandalone.support_sq_ge_one beta hb0 hbq
  have hKT : T ≤ K ^ 2 * T := by
    simpa using mul_le_mul_of_nonneg_right hKsq hT0
  have hterm : T ≤ (1 + K ^ 2) * T / 2 := by
    nlinarith
  have hformula :=
    SecondSectorDefectStandalone.sectorMinimum_second_formula beta hcos.ne'
  have hminimum :
      1 + s * T ≤ sectorMinimum (Real.pi / 2 + beta) beta := by
    rw [hformula]
    change 1 + s * T ≤ 1 + d * T + (1 + K ^ 2) * T / 2
    have hds : d + 1 = s := by simp [d]
    nlinarith
  have htan := SecondSectorDefectStandalone.beta_le_tan_beta beta hb0 hbq
  have hsBeta : ((7 : ℝ) / 5) * beta ≤ s * beta :=
    mul_le_mul_of_nonneg_right s_lower.le hb0
  have hsTan : s * beta ≤ s * T := by
    dsimp [T]
    exact mul_le_mul_of_nonneg_left htan s_nonneg
  have hcoeff := phaseSlope_div_pi_le_four_fifths
  have hphase :
      phaseSlope * (beta / Real.pi) ≤ ((4 : ℝ) / 5) * beta := by
    have hid : phaseSlope * (beta / Real.pi) =
        (phaseSlope / Real.pi) * beta := by ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hcoeff hb0
  have hbase := SecondSectorDefectStandalone.second_baseline_identity beta
  dsimp [phaseDefect]
  rw [hbase]
  nlinarith

/-- The third sector has a very large reserve; the octagonal cap alone is a
valid lower bound. -/
theorem third_sector_defect_ge_cap
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta < Real.pi / 4) :
    cap ≤ phaseDefect (3 * Real.pi / 4 + beta) beta := by
  have hmin := ThirdSectorDefectStandalone.third_sector_min_ge_s_add_one
    beta hb0 hbq
  have hu : (3 * Real.pi / 4 + beta) / Real.pi ≤ 1 := by
    apply (div_le_one Real.pi_pos).2
    nlinarith
  have hphase := mul_le_mul_of_nonneg_left hu phaseSlope_pos.le
  have hconst : cap ≤ s + 1 - (phaseSlope - cap) := by
    dsimp [phaseSlope]
    nlinarith [s_lower]
  dsimp [phaseDefect]
  nlinarith

lemma beta_thirteen_tan_lower
    (beta : ℝ) (hbeta : 13 * Real.pi / 180 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) :
    (9 : ℝ) / 40 ≤ Real.tan beta := by
  have hbpos : 0 < beta := by nlinarith [Real.pi_pos]
  have hlt := Real.lt_tan hbpos (by nlinarith [hbq, Real.pi_pos])
  have hpi := Real.pi_gt_d2
  nlinarith

lemma high_branch_tan_upper
    (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbeta : beta ≤ 42 * Real.pi / 180)
    (ht : (3 : ℝ) / 5 ≤ Real.tan beta)
    (ht1 : Real.tan beta ≤ 1) :
    Real.tan beta ≤ (19 : ℝ) / 21 := by
  let t : ℝ := Real.tan beta
  have hcomp := arctan_complement t ht ht1
  have hatan : Real.arctan t = beta := by
    dsimp [t]
    apply Real.arctan_tan
    · nlinarith [hb0, Real.pi_pos]
    · nlinarith [hbeta, Real.pi_pos]
  have huatan : Real.arctan (u t) = Real.pi / 4 - beta := by
    linarith
  let gamma : ℝ := Real.pi / 4 - beta
  have hgamma : gamma = Real.arctan (u t) := by
    dsimp [gamma]
    linarith
  have hgammaLower : Real.pi / 60 ≤ gamma := by
    dsimp [gamma]
    nlinarith
  have hgammaPos : 0 < gamma := by nlinarith [Real.pi_pos]
  have hgammaHalf : gamma < Real.pi / 2 := by
    dsimp [gamma]
    nlinarith [hb0, Real.pi_pos]
  have hltTan := Real.lt_tan hgammaPos hgammaHalf
  have htanGamma : Real.tan gamma = u t := by
    rw [hgamma, Real.tan_arctan]
  rw [htanGamma] at hltTan
  have hpi := Real.pi_gt_three
  have hu : (1 : ℝ) / 20 < u t := by nlinarith
  have htneg : -1 < t := by
    dsimp [t]
    nlinarith
  have hden : 0 < 1 + t := by linarith
  have hmul : ((1 : ℝ) / 20) * (1 + t) < 1 - t := by
    change (1 - t) / (1 + t) > (1 : ℝ) / 20 at hu
    exact (lt_div_iff₀ hden).1 hu
  have htfinal : t ≤ (19 : ℝ) / 21 := by nlinarith
  simpa [t] using htfinal

/-- The first large sector has defect at least `4/625` between `58°` and
`87°`. -/
theorem first_sector_defect_ge_q5
    (beta : ℝ)
    (hbl : 13 * Real.pi / 180 ≤ beta)
    (hbu : beta ≤ 42 * Real.pi / 180) :
    q5 ≤ phaseDefect (Real.pi / 4 + beta) beta := by
  have hb0 : 0 ≤ beta := by nlinarith [Real.pi_pos]
  have hbq : beta ≤ Real.pi / 4 := by nlinarith [hbu, Real.pi_pos]
  have hcos := FirstSectorDefectStandalone.cos_beta_pos beta hb0 hbq
  have hsin := FirstSectorDefectStandalone.sin_beta_nonneg beta hb0 hbq
  have hsum : 0 < Real.cos beta + Real.sin beta :=
    add_pos_of_pos_of_nonneg hcos hsin
  let t : ℝ := Real.tan beta
  have ht0 : 0 ≤ t := by
    dsimp [t]
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg hsin hcos.le
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [Real.tan_eq_sin_div_cos]
    exact (div_le_one hcos).2
      (FirstSectorDefectStandalone.sin_beta_le_cos_beta beta hb0 hbq)
  have htLower : (9 : ℝ) / 40 ≤ t := by
    dsimp [t]
    exact beta_thirteen_tan_lower beta hbl hbq
  have hatan : Real.arctan t = beta := by
    dsimp [t]
    apply Real.arctan_tan
    · nlinarith [hb0, Real.pi_pos]
    · nlinarith [hbq, Real.pi_pos]
  have hscalar : q5 + exactK * Real.arctan t ≤ firstLhs t := by
    by_cases hlow : t ≤ (3 : ℝ) / 5
    · have hgap := low_class_gap t htLower hlow
      have hatan0 : 0 ≤ Real.arctan t := Real.arctan_nonneg.mpr ht0
      have hquint := arctan_le_quintic t ht0
      have h1 : exactK * Real.arctan t ≤ lowK * Real.arctan t :=
        mul_le_mul_of_nonneg_right exactK_le_lowK hatan0
      have h2 : lowK * Real.arctan t ≤ lowK * quintic t :=
        mul_le_mul_of_nonneg_left hquint lowK_nonneg
      nlinarith
    · have hhigh : (3 : ℝ) / 5 ≤ t := le_of_not_ge hlow
      have htUpper : t ≤ (19 : ℝ) / 21 := by
        dsimp [t]
        exact high_branch_tan_upper beta hb0 hbu hhigh ht1
      have hgap := high_class_gap t hhigh htUpper
      have hcomp := arctan_complement t hhigh ht1
      have htm : -1 < t := by nlinarith
      have hu0 := u_nonneg t ht1 htm
      have hcubic := cubic_le_arctan (u t) hu0
      have hR0 := cubic_u_nonneg t hhigh ht1
      have hk := mul_le_mul_of_nonneg_right highK_le_exactK hR0
      have hka := mul_le_mul_of_nonneg_left hcubic exactK_nonneg
      have hpay : highK * cubic (u t) ≤ exactK * Real.arctan (u t) :=
        le_trans hk hka
      have hconst := exactK_mul_pi_div_four
      have hrewrite : exactK * Real.arctan t =
          c - exactK * Real.arctan (u t) := by
        rw [hcomp, mul_sub, hconst]
      rw [hrewrite]
      linarith
  rw [hatan] at hscalar
  have hformula := FirstSectorDefectStandalone.first_sector_formula
    beta hcos.ne' hsum.ne'
  have hbase := FirstSectorDefectStandalone.first_baseline_identity beta
  dsimp [phaseDefect]
  rw [hformula, hbase]
  nlinarith

/-- A turn at or beyond `92°` already exceeds the worst quadrilateral defect
budget. -/
theorem defect_ge_q4_of_ninety_two_le
    (alpha : ℝ)
    (ha : 92 * Real.pi / 180 ≤ alpha)
    (haπ : alpha < Real.pi) :
    (17 : ℝ) / 1000 ≤ actualDefect alpha := by
  have hhalf : Real.pi / 2 < alpha := by nlinarith [Real.pi_pos]
  by_cases hthird : alpha ≤ 3 * Real.pi / 4
  · let beta : ℝ := alpha - Real.pi / 2
    have hb0 : 0 ≤ beta := by dsimp [beta]; linarith
    have hbq : beta ≤ Real.pi / 4 := by dsimp [beta]; linarith
    have hbl : Real.pi / 90 ≤ beta := by dsimp [beta]; nlinarith
    have hdef := second_sector_defect_ge beta hb0 hbq
    have hnum : (17 : ℝ) / 1000 ≤ ((3 : ℝ) / 5) * beta := by
      have hpi := Real.pi_gt_three
      nlinarith
    have hres : AllSectorDefectStandalone.residual alpha = beta := by
      simp [AllSectorDefectStandalone.residual,
        show ¬ alpha ≤ Real.pi / 4 by linarith,
        show ¬ alpha ≤ Real.pi / 2 by linarith, hthird, beta]
    have hpaid := le_trans hnum hdef
    dsimp [actualDefect]
    rw [hres]
    simpa [beta] using hpaid
  · let beta : ℝ := alpha - 3 * Real.pi / 4
    have hb0 : 0 ≤ beta := by dsimp [beta]; linarith
    have hbq : beta < Real.pi / 4 := by dsimp [beta]; linarith
    have hdef := third_sector_defect_ge_cap beta hb0 hbq
    have hqcap : (17 : ℝ) / 1000 ≤ cap := by
      nlinarith [SmallGapReserveStandalone.cap_lower]
    have hres : AllSectorDefectStandalone.residual alpha = beta := by
      simp [AllSectorDefectStandalone.residual,
        show ¬ alpha ≤ Real.pi / 4 by linarith,
        show ¬ alpha ≤ Real.pi / 2 by linarith,
        show ¬ alpha ≤ 3 * Real.pi / 4 by exact hthird, beta]
    have hpaid := le_trans hqcap hdef
    dsimp [actualDefect]
    rw [hres]
    simpa [beta] using hpaid

/-- A phase defect below `4/625` lies in one of the two pentagonal windows. -/
theorem defect_lt_q5_classification
    (alpha : ℝ) (ha0 : 0 < alpha) (haπ : alpha < Real.pi)
    (hdef : actualDefect alpha < q5) :
    (43 * Real.pi / 180 < alpha ∧ alpha < 58 * Real.pi / 180) ∨
      (87 * Real.pi / 180 < alpha ∧ alpha < 91 * Real.pi / 180) := by
  by_cases h43 : alpha ≤ 43 * Real.pi / 180
  · have hreq := all_sector_reserve alpha ha0.le haπ
    have hratio : alpha / Real.pi ≤ (43 : ℝ) / 180 := by
      apply (div_le_iff₀ Real.pi_pos).2
      nlinarith
    have hfactor : (2 : ℝ) / 45 ≤ 1 - 4 * (alpha / Real.pi) := by
      nlinarith
    have hreserve : q5 ≤ requiredReserve alpha := by
      have hmul := mul_le_mul_of_nonneg_left hfactor
        (by norm_num [smallGapReserve] : 0 ≤ smallGapReserve)
      dsimp [requiredReserve]
      have hnonneg : 0 ≤ 1 - 4 * (alpha / Real.pi) := by nlinarith
      rw [max_eq_left hnonneg]
      dsimp [smallGapReserve, q5] at hmul ⊢
      nlinarith
    have hpaid := le_trans hreserve hreq
    exact (not_lt_of_ge hpaid hdef).elim
  · have h43' : 43 * Real.pi / 180 < alpha := lt_of_not_ge h43
    by_cases h58 : alpha < 58 * Real.pi / 180
    · exact Or.inl ⟨h43', h58⟩
    · have h58' : 58 * Real.pi / 180 ≤ alpha := le_of_not_gt h58
      by_cases h87 : alpha ≤ 87 * Real.pi / 180
      · let beta : ℝ := alpha - Real.pi / 4
        have hbl : 13 * Real.pi / 180 ≤ beta := by dsimp [beta]; nlinarith
        have hbu : beta ≤ 42 * Real.pi / 180 := by dsimp [beta]; nlinarith
        have hq := first_sector_defect_ge_q5 beta hbl hbu
        have hres : AllSectorDefectStandalone.residual alpha = beta := by
          have hqtr : Real.pi / 4 < alpha := by nlinarith [Real.pi_pos]
          have hhalf : alpha ≤ Real.pi / 2 := by nlinarith [h87, Real.pi_pos]
          simp [AllSectorDefectStandalone.residual,
            show ¬ alpha ≤ Real.pi / 4 by linarith, hhalf, beta]
        have hq' : q5 ≤ phaseDefect alpha beta := by
          simpa [beta] using hq
        have hactual : actualDefect alpha = phaseDefect alpha beta := by
          dsimp [actualDefect]
          rw [hres]
        rw [hactual] at hdef
        exact (not_lt_of_ge hq' hdef).elim
      · have h87' : 87 * Real.pi / 180 < alpha := lt_of_not_ge h87
        by_cases h91 : alpha < 91 * Real.pi / 180
        · exact Or.inr ⟨h87', h91⟩
        · have h91' : 91 * Real.pi / 180 ≤ alpha := le_of_not_gt h91
          by_cases hthird : alpha ≤ 3 * Real.pi / 4
          · let beta : ℝ := alpha - Real.pi / 2
            have hb0 : 0 ≤ beta := by dsimp [beta]; nlinarith [Real.pi_pos]
            have hbq : beta ≤ Real.pi / 4 := by dsimp [beta]; nlinarith
            have hbl : Real.pi / 180 ≤ beta := by dsimp [beta]; nlinarith
            have hq := second_sector_defect_ge beta hb0 hbq
            have hnum : q5 ≤ ((3 : ℝ) / 5) * beta := by
              have hpi := Real.pi_gt_three
              dsimp [q5]
              nlinarith
            have hres : AllSectorDefectStandalone.residual alpha = beta := by
              simp [AllSectorDefectStandalone.residual,
                show ¬ alpha ≤ Real.pi / 4 by nlinarith [Real.pi_pos],
                show ¬ alpha ≤ Real.pi / 2 by nlinarith [Real.pi_pos],
                hthird, beta]
            have hpaid := le_trans hnum hq
            have hpaid' : q5 ≤ phaseDefect alpha beta := by
              simpa [beta] using hpaid
            have hactual : actualDefect alpha = phaseDefect alpha beta := by
              dsimp [actualDefect]
              rw [hres]
            rw [hactual] at hdef
            exact (not_lt_of_ge hpaid' hdef).elim
          · let beta : ℝ := alpha - 3 * Real.pi / 4
            have hb0 : 0 ≤ beta := by dsimp [beta]; linarith
            have hbq : beta < Real.pi / 4 := by dsimp [beta]; linarith
            have hq := third_sector_defect_ge_cap beta hb0 hbq
            have hqcap : q5 ≤ cap := by
              dsimp [q5]
              nlinarith [SmallGapReserveStandalone.cap_lower]
            have hres : AllSectorDefectStandalone.residual alpha = beta := by
              simp [AllSectorDefectStandalone.residual,
                show ¬ alpha ≤ Real.pi / 4 by nlinarith [Real.pi_pos],
                show ¬ alpha ≤ Real.pi / 2 by nlinarith [Real.pi_pos],
                show ¬ alpha ≤ 3 * Real.pi / 4 by exact hthird, beta]
            have hpaid := le_trans hqcap hq
            have hpaid' : q5 ≤ phaseDefect alpha beta := by
              simpa [beta] using hpaid
            have hactual : actualDefect alpha = phaseDefect alpha beta := by
              dsimp [actualDefect]
              rw [hres]
            rw [hactual] at hdef
            exact (not_lt_of_ge hpaid' hdef).elim

end

end DangerousFanClassificationStandalone
