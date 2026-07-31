import AllSectorDefectStandalone
import PhaseSectorAlgebraStandalone
import OctagonSupportNormalizationStandalone

/-!
# Geometric one-gap bridge for the regular octagon

A real support direction is reduced to a phase in `[-pi/8,pi/8]`.  For two
consecutive normals, the second reduced phase is either `t + beta` or
`t + beta - pi/4`, where `beta` is the residual gap.  The scale-free sector
minimum, exact octagon normalization, and exhaustive defect theorem combine
to give both the local tangent-area estimate and the funded small-corner
reserve used by the global proof.
-/

namespace PhaseGapBridgeStandalone

noncomputable section

open Real
open OctagonBase
open AllSectorDefectStandalone
open PhaseSectorAlgebraStandalone
open OctagonSupportNormalizationStandalone

/-- Exact tangent-wedge contribution at two reduced support phases. -/
def phaseWedge (alpha x y : ℝ) : ℝ :=
  wedge alpha (R * Real.cos x) (R * Real.cos y)

lemma phaseWedge_eq_pair
    (alpha x y : ℝ) (hsin : Real.sin alpha ≠ 0) :
    phaseWedge alpha x y =
      (R ^ 2 / (2 * Real.sin alpha)) *
        pairNumerator (Real.cos alpha) x y := by
  dsimp [phaseWedge, wedge, pairNumerator]
  field_simp [hsin]

lemma boundary_support_left :
    R * Real.cos (-(Real.pi / 8)) = 1 := by
  rw [Real.cos_neg]
  exact R_mul_cos_eighth

lemma boundary_support_right (beta : ℝ) :
    R * Real.cos (-(Real.pi / 8) + beta) =
      Real.cos beta + d * Real.sin beta := by
  have hangle : -(Real.pi / 8) + beta = beta - Real.pi / 8 := by ring
  rw [hangle, Real.cos_sub]
  calc
    R * (Real.cos beta * Real.cos (Real.pi / 8) +
        Real.sin beta * Real.sin (Real.pi / 8)) =
      Real.cos beta * (R * Real.cos (Real.pi / 8)) +
        Real.sin beta * (R * Real.sin (Real.pi / 8)) := by ring
    _ = Real.cos beta + d * Real.sin beta := by
      rw [R_mul_cos_eighth, R_mul_sin_eighth]
      ring

lemma boundary_support_right_wrap (beta : ℝ) :
    R * Real.cos (beta - Real.pi / 8) =
      Real.cos beta + d * Real.sin beta := by
  rw [Real.cos_sub]
  calc
    R * (Real.cos beta * Real.cos (Real.pi / 8) +
        Real.sin beta * Real.sin (Real.pi / 8)) =
      Real.cos beta * (R * Real.cos (Real.pi / 8)) +
        Real.sin beta * (R * Real.sin (Real.pi / 8)) := by ring
    _ = Real.cos beta + d * Real.sin beta := by
      rw [R_mul_cos_eighth, R_mul_sin_eighth]
      ring

lemma noWrap_boundary_value (alpha beta : ℝ) :
    phaseWedge alpha (-(Real.pi / 8))
        (-(Real.pi / 8) + beta) = sectorMinimum alpha beta := by
  dsimp [phaseWedge, sectorMinimum]
  rw [boundary_support_left, boundary_support_right]

lemma wrap_boundary_value (alpha beta : ℝ) :
    phaseWedge alpha (Real.pi / 8)
        (beta - Real.pi / 8) = sectorMinimum alpha beta := by
  dsimp [phaseWedge, sectorMinimum]
  rw [R_mul_cos_eighth, boundary_support_right_wrap]

/-- Sector minimization in the no-wrap phase representation. -/
theorem noWrap_sector_min
    (alpha beta t : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ Real.pi / 4)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + beta ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    sectorMinimum alpha beta ≤ phaseWedge alpha t (t + beta) := by
  have hpair := noWrap_min alpha beta t hbeta0 hbeta htL htR
  have hfactor : 0 ≤ R ^ 2 / (2 * Real.sin alpha) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpair hfactor
  rw [← noWrap_boundary_value alpha beta]
  rw [phaseWedge_eq_pair alpha (-(Real.pi / 8))
      (-(Real.pi / 8) + beta) hsin.ne',
    phaseWedge_eq_pair alpha t (t + beta) hsin.ne']
  exact hmul

/-- Sector minimization in the one-boundary-wrap representation. -/
theorem wrap_sector_min
    (alpha beta t : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ Real.pi / 4)
    (htL : Real.pi / 8 - beta ≤ t)
    (htR : t ≤ Real.pi / 8)
    (hsin : 0 < Real.sin alpha) :
    sectorMinimum alpha beta ≤
      phaseWedge alpha t (t + beta - Real.pi / 4) := by
  have hpair := wrap_min alpha beta t hbeta0 hbeta htL htR
  have hfactor : 0 ≤ R ^ 2 / (2 * Real.sin alpha) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpair hfactor
  rw [← wrap_boundary_value alpha beta]
  rw [phaseWedge_eq_pair alpha (Real.pi / 8)
      (beta - Real.pi / 8) hsin.ne',
    phaseWedge_eq_pair alpha t (t + beta - Real.pi / 4) hsin.ne']
  exact hmul

/-- Actual phase defect attached to one normal gap. -/
def actualDefect (alpha : ℝ) : ℝ :=
  phaseDefect alpha (residual alpha)

lemma baseline_add_actualDefect (alpha : ℝ) :
    phaseSlope * (alpha / Real.pi) - cap + actualDefect alpha =
      sectorMinimum alpha (residual alpha) := by
  dsimp [actualDefect, phaseDefect]
  ring

/-- Complete local package in the no-wrap representation. -/
theorem noWrap_gap_package
    (alpha t : ℝ)
    (ha0 : 0 < alpha) (haπ : alpha < Real.pi)
    (htL : -(Real.pi / 8) ≤ t)
    (htR : t + residual alpha ≤ Real.pi / 8) :
    phaseSlope * (alpha / Real.pi) - cap + actualDefect alpha ≤
        phaseWedge alpha t (t + residual alpha) ∧
      requiredReserve alpha ≤ actualDefect alpha := by
  have hbeta0 := residual_nonneg alpha ha0.le haπ
  have hbeta := residual_le_quarter alpha ha0.le haπ
  have hsin : 0 < Real.sin alpha :=
    Real.sin_pos_of_pos_of_lt_pi ha0 haπ
  have hmin := noWrap_sector_min alpha (residual alpha) t
    hbeta0 hbeta htL htR hsin
  constructor
  · rw [baseline_add_actualDefect]
    exact hmin
  · exact all_sector_reserve alpha ha0.le haπ

/-- Complete local package in the one-boundary-wrap representation. -/
theorem wrap_gap_package
    (alpha t : ℝ)
    (ha0 : 0 < alpha) (haπ : alpha < Real.pi)
    (htL : Real.pi / 8 - residual alpha ≤ t)
    (htR : t ≤ Real.pi / 8) :
    phaseSlope * (alpha / Real.pi) - cap + actualDefect alpha ≤
        phaseWedge alpha t (t + residual alpha - Real.pi / 4) ∧
      requiredReserve alpha ≤ actualDefect alpha := by
  have hbeta0 := residual_nonneg alpha ha0.le haπ
  have hbeta := residual_le_quarter alpha ha0.le haπ
  have hsin : 0 < Real.sin alpha :=
    Real.sin_pos_of_pos_of_lt_pi ha0 haπ
  have hmin := wrap_sector_min alpha (residual alpha) t
    hbeta0 hbeta htL htR hsin
  constructor
  · rw [baseline_add_actualDefect]
    exact hmin
  · exact all_sector_reserve alpha ha0.le haπ

/-- Representation-independent local package. -/
theorem reduced_gap_package
    (alpha t y : ℝ)
    (ha0 : 0 < alpha) (haπ : alpha < Real.pi)
    (hcase :
      (y = t + residual alpha ∧
        -(Real.pi / 8) ≤ t ∧
        t + residual alpha ≤ Real.pi / 8) ∨
      (y = t + residual alpha - Real.pi / 4 ∧
        Real.pi / 8 - residual alpha ≤ t ∧
        t ≤ Real.pi / 8)) :
    phaseSlope * (alpha / Real.pi) - cap + actualDefect alpha ≤
        phaseWedge alpha t y ∧
      requiredReserve alpha ≤ actualDefect alpha := by
  rcases hcase with hno | hwrap
  · rcases hno with ⟨rfl, htL, htR⟩
    exact noWrap_gap_package alpha t ha0 haπ htL htR
  · rcases hwrap with ⟨rfl, htL, htR⟩
    exact wrap_gap_package alpha t ha0 haπ htL htR

end

end PhaseGapBridgeStandalone
