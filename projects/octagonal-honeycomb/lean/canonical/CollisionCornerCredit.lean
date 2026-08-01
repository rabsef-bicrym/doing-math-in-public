import OctagonalCornerBank
import CollisionChargeAccounting
import Mathlib.Analysis.Real.Pi.Bounds

set_option linter.unusedVariables false

/-!
# Exact credit available at a continuous collision corner

When two negative owners select the same edge, each owner turn is at least
`0.46π`; hence the third-cell turn is at most `0.08π`.  On this interval the
phase-snapping defect has an explicit trigonometric formula.  Rational Taylor
bounds prove that the resulting under-credit is strictly greater than `0.009`,
which pays the maximum possible owner debt.
-/

namespace CollisionCornerCredit

noncomputable section

open Real
open PairGapCore
open PairGapBounds
open NoncrystallineDomainReduction
open ContinuousCornerBank
open OctagonalCornerBank
open CollisionChargeAccounting

def collisionLimit : ℝ := 2 / 25

def sinSurrogate (u : ℝ) : ℝ :=
  ((157 : ℝ) / 50) * u - ((250047 : ℝ) / 32000) * u ^ 3

def cosSurrogate (u : ℝ) : ℝ :=
  1 - ((3969 : ℝ) / 800) * u ^ 2

def tangentSurrogate (u : ℝ) : ℝ :=
  4 * u + sinSurrogate u * (cosSurrogate u + sinSurrogate u)

def rationalDefect (u : ℝ) : ℝ :=
  cap - 4 * (2 - s) * u +
    d * sinSurrogate u * (cosSurrogate u + sinSurrogate u)

def smallPhaseDefect (u : ℝ) : ℝ :=
  cap - 4 * (2 - s) * u +
    d * Real.sin (Real.pi * u) *
      (Real.cos (Real.pi * u) + Real.sin (Real.pi * u))

/-- Polynomial quotient certifying that `tangentSurrogate` has slope below
nine on the collision interval. -/
def tangentGapWitness (u : ℝ) : ℝ :=
  (388837321526291 : ℝ) / 312500000000000 -
  ((192412678473709 : ℝ) / 25000000000000) * u +
  ((54077321526291 : ℝ) / 2000000000000) * u ^ 2 +
  ((7292734026291 : ℝ) / 160000000000) * u ^ 3 -
  ((558741773709 : ℝ) / 12800000000) * u ^ 4 -
  ((62523502209 : ℝ) / 1024000000) * u ^ 5

lemma collisionLimit_pos : 0 < collisionLimit := by norm_num [collisionLimit]

lemma collisionLimit_nonneg : 0 ≤ collisionLimit := collisionLimit_pos.le

lemma d_lt_five_twelfths : d < (5 : ℝ) / 12 := by
  dsimp [d]
  nlinarith [s_upper]

lemma square_le_at_limit
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    u ^ 2 ≤ collisionLimit ^ 2 := by
  have hleft : 0 ≤ collisionLimit - u := sub_nonneg.mpr hub
  have hright : 0 ≤ collisionLimit + u := add_nonneg collisionLimit_nonneg hu
  have hp := mul_nonneg hleft hright
  nlinarith

lemma fourth_le_at_limit
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    u ^ 4 ≤ collisionLimit ^ 4 := by
  have hsq := square_le_at_limit u hu hub
  have hp := mul_le_mul hsq hsq (sq_nonneg u) (sq_nonneg collisionLimit)
  nlinarith

lemma fifth_le_at_limit
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    u ^ 5 ≤ collisionLimit ^ 5 := by
  have h4 := fourth_le_at_limit u hu hub
  have hp := mul_le_mul h4 hub hu (pow_nonneg collisionLimit_nonneg 4)
  nlinarith

lemma tangentGapWitness_nonneg
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    0 ≤ tangentGapWitness u := by
  have h4 := fourth_le_at_limit u hu hub
  have h5 := fifth_le_at_limit u hu hub
  have h2 : 0 ≤ u ^ 2 := sq_nonneg u
  have h3 : 0 ≤ u ^ 3 := pow_nonneg hu 3
  dsimp [tangentGapWitness, collisionLimit] at h4 h5 ⊢
  nlinarith

lemma tangent_gap_identity (u : ℝ) :
    9 * (collisionLimit - u) -
        (tangentSurrogate collisionLimit - tangentSurrogate u) =
      (collisionLimit - u) * tangentGapWitness u := by
  dsimp [collisionLimit, tangentSurrogate, sinSurrogate, cosSurrogate,
    tangentGapWitness]
  ring

lemma tangent_gap_le_nine
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    tangentSurrogate collisionLimit - tangentSurrogate u ≤
      9 * (collisionLimit - u) := by
  have hdelta : 0 ≤ collisionLimit - u := sub_nonneg.mpr hub
  have hw := tangentGapWitness_nonneg u hu hub
  have hp := mul_nonneg hdelta hw
  have hid := tangent_gap_identity u
  nlinarith

lemma rational_defect_difference (u : ℝ) :
    rationalDefect u - rationalDefect collisionLimit =
      4 * (collisionLimit - u) -
        d * (tangentSurrogate collisionLimit - tangentSurrogate u) := by
  dsimp [rationalDefect, tangentSurrogate, d]
  ring

lemma rationalDefect_mono_to_limit
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    rationalDefect collisionLimit ≤ rationalDefect u := by
  have hdelta : 0 ≤ collisionLimit - u := sub_nonneg.mpr hub
  have ht := tangent_gap_le_nine u hu hub
  have hdt := mul_le_mul_of_nonneg_left ht d_nonneg
  have hd9 : d * 9 ≤ (15 : ℝ) / 4 := by
    nlinarith [d_lt_five_twelfths]
  have hscale := mul_le_mul_of_nonneg_right hd9 hdelta
  have hid := rational_defect_difference u
  nlinarith

lemma rationalDefect_limit_gt :
    (108 : ℝ) / 1000 < rationalDefect collisionLimit := by
  dsimp [rationalDefect, collisionLimit, sinSurrogate, cosSurrogate, cap, d]
  nlinarith [s_sq, s_upper]

lemma sinSurrogate_nonneg
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    0 ≤ sinSurrogate u := by
  have hu2 := square_le_at_limit u hu hub
  have hcoef :
      0 ≤ (157 : ℝ) / 50 - ((250047 : ℝ) / 32000) * u ^ 2 := by
    dsimp [collisionLimit] at hu2
    nlinarith
  have hid :
      sinSurrogate u = u *
        ((157 : ℝ) / 50 - ((250047 : ℝ) / 32000) * u ^ 2) := by
    dsimp [sinSurrogate]
    ring
  rw [hid]
  exact mul_nonneg hu hcoef

lemma cosSurrogate_nonneg
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    0 ≤ cosSurrogate u := by
  have hu2 := square_le_at_limit u hu hub
  dsimp [cosSurrogate, collisionLimit] at hu2 ⊢
  nlinarith

lemma surrogate_product_le_true
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    sinSurrogate u * (cosSurrogate u + sinSurrogate u) ≤
      Real.sin (Real.pi * u) *
        (Real.cos (Real.pi * u) + Real.sin (Real.pi * u)) := by
  by_cases hu0 : u = 0
  · subst u
    simp [sinSurrogate, cosSurrogate]
  · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    let x : ℝ := Real.pi * u
    let B : ℝ := ((63 : ℝ) / 20) * u
    have hxpos : 0 < x := mul_pos Real.pi_pos hupos
    have hx0 : 0 ≤ x := hxpos.le
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    have hpiLower : (157 : ℝ) / 50 ≤ Real.pi := by
      have h := Real.pi_gt_d2.le
      convert h using 1 <;> norm_num
    have hpiUpper : Real.pi ≤ (63 : ℝ) / 20 := by
      have h := Real.pi_lt_d2.le
      convert h using 1 <;> norm_num
    have hxlo : ((157 : ℝ) / 50) * u ≤ x := by
      dsimp [x]
      exact mul_le_mul_of_nonneg_right hpiLower hu
    have hxhi : x ≤ B := by
      dsimp [x, B]
      exact mul_le_mul_of_nonneg_right hpiUpper hu
    have hxle1 : x ≤ 1 := by
      calc
        x ≤ B := hxhi
        _ ≤ ((63 : ℝ) / 20) * collisionLimit :=
          mul_le_mul_of_nonneg_left hub (by norm_num)
        _ ≤ 1 := by norm_num [collisionLimit]
    have hsq : x ^ 2 ≤ B ^ 2 := by
      have hleft : 0 ≤ B - x := sub_nonneg.mpr hxhi
      have hright : 0 ≤ B + x := add_nonneg hB0 hx0
      have hp := mul_nonneg hleft hright
      nlinarith
    have hcube : x ^ 3 ≤ B ^ 3 := by
      have hp := mul_le_mul hsq hxhi hx0 (sq_nonneg B)
      nlinarith
    have hsinTaylor := (Real.sin_gt_sub_cube hxpos hxle1).le
    have hsinSur : sinSurrogate u ≤ x - x ^ 3 / 4 := by
      dsimp [sinSurrogate, B] at hcube ⊢
      nlinarith
    have hsin : sinSurrogate u ≤ Real.sin x :=
      le_trans hsinSur hsinTaylor
    have hcosTaylor : 1 - x ^ 2 / 2 ≤ Real.cos x :=
      Real.one_sub_sq_div_two_le_cos
    have hcosSur : cosSurrogate u ≤ 1 - x ^ 2 / 2 := by
      dsimp [cosSurrogate, B] at hsq ⊢
      nlinarith
    have hcos : cosSurrogate u ≤ Real.cos x :=
      le_trans hcosSur hcosTaylor
    have hSin0 := sinSurrogate_nonneg u hu hub
    have hCos0 := cosSurrogate_nonneg u hu hub
    have hsum0 : 0 ≤ cosSurrogate u + sinSurrogate u := add_nonneg hCos0 hSin0
    have hsin0 : 0 ≤ Real.sin x := le_trans hSin0 hsin
    have hsum :
        cosSurrogate u + sinSurrogate u ≤ Real.cos x + Real.sin x :=
      add_le_add hcos hsin
    have hfirst := mul_le_mul_of_nonneg_right hsin hsum0
    have hsecond := mul_le_mul_of_nonneg_left hsum hsin0
    dsimp [x] at hfirst hsecond ⊢
    exact le_trans hfirst hsecond

lemma rationalDefect_le_smallPhaseDefect
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    rationalDefect u ≤ smallPhaseDefect u := by
  have hp := surrogate_product_le_true u hu hub
  have hdp := mul_le_mul_of_nonneg_left hp d_nonneg
  dsimp [rationalDefect, smallPhaseDefect, tangentSurrogate]
  nlinarith

/-- The exact small-corner phase defect is uniformly larger than `0.108` on
the complete collision interval. -/
theorem smallPhaseDefect_gt
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    (108 : ℝ) / 1000 < smallPhaseDefect u := by
  have hrat := rationalDefect_mono_to_limit u hu hub
  have htrue := rationalDefect_le_smallPhaseDefect u hu hub
  linarith [rationalDefect_limit_gt]

lemma line4_upper_tight : line 4 < (8017 : ℝ) / 2000 := by
  rw [line_four]
  nlinarith [p6_upper, p8_lower]

lemma eta4_upper_tight : eta4 < (171 : ℝ) / 10000 := by
  have hhalf : line 4 / 2 < (8017 : ℝ) / 4000 := by
    nlinarith [line4_upper_tight]
  have hsum : 0 < (8017 : ℝ) / 4000 + line 4 / 2 := by
    nlinarith [line4_pos]
  have hp := mul_pos (sub_pos.mpr hhalf) hsum
  dsimp [eta4]
  nlinarith

/-- Every collision third corner supplies more than `0.009` of fully funded
credit. -/
theorem underCredit_gt_nine_thousandths
    (u : ℝ) (hu : 0 ≤ u) (hub : u ≤ collisionLimit) :
    (9 : ℝ) / 1000 < underCredit (smallPhaseDefect u) := by
  have hdef := smallPhaseDefect_gt u hu hub
  have hcap : (108 : ℝ) / 1000 < cap := by
    nlinarith [cap_lower]
  have hmin : (108 : ℝ) / 1000 < min (smallPhaseDefect u) cap :=
    lt_min hdef hcap
  have harg : (9 : ℝ) / 100 <
      min (smallPhaseDefect u) cap - eta4 := by
    nlinarith [eta4_upper_tight]
  have hpos := le_pos (min (smallPhaseDefect u) cap - eta4)
  dsimp [underCredit, potential]
  nlinarith

/-- At a collision endpoint the two high owner turns force the third-cell turn
into the certified small-corner interval. -/
theorem collision_third_turn_in_range
    (ownerLeft ownerRight third : ℝ)
    (hleft : (23 : ℝ) / 50 ≤ ownerLeft)
    (hright : (23 : ℝ) / 50 ≤ ownerRight)
    (hthird : 0 ≤ third)
    (hsum : ownerLeft + ownerRight + third = 1) :
    0 ≤ third ∧ third ≤ collisionLimit := by
  refine ⟨hthird, ?_⟩
  dsimp [collisionLimit]
  linarith

/-- Two collision endpoint credits strictly pay two owner debts, each bounded
by `0.009`. -/
theorem collision_pair_strictly_paid
    (uStart uEnd debtLeft debtRight : ℝ)
    (huStart : 0 ≤ uStart) (huStartMax : uStart ≤ collisionLimit)
    (huEnd : 0 ≤ uEnd) (huEndMax : uEnd ≤ collisionLimit)
    (hdebtLeft : debtLeft ≤ (9 : ℝ) / 1000)
    (hdebtRight : debtRight ≤ (9 : ℝ) / 1000) :
    debtLeft + debtRight <
      underCredit (smallPhaseDefect uStart) +
        underCredit (smallPhaseDefect uEnd) := by
  have hs := underCredit_gt_nine_thousandths uStart huStart huStartMax
  have he := underCredit_gt_nine_thousandths uEnd huEnd huEndMax
  linarith

end

end CollisionCornerCredit
