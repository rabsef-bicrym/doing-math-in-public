import DangerousFanClassificationStandalone
import OctagonBenchmarkStandalone

/-!
# From negative perimeter charge to a phase-defect budget

The phase bridge gives `A_n + sumDefect <= tangentArea`; Chakerian gives
`2*sqrt(tangentArea) <= perimeter`.  If the perimeter is below the affine
benchmark line, squaring yields exactly `sumDefect < eta_n`.
-/

namespace NegativeOwnerBudgetStandalone

noncomputable section

open Real
open scoped BigOperators
open OctagonBase
open OctagonBenchmarkStandalone
open DangerousFanClassificationStandalone

lemma square_strict_of_nonneg_lt
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : a ^ 2 < b ^ 2 := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hp : 0 < (b - a) * (b + a) :=
    mul_pos (sub_pos.mpr hab) (add_pos_of_pos_of_nonneg hb ha)
  nlinarith

/-- Four-sided negative owners have total phase defect below `eta4`. -/
theorem quadrilateral_defect_budget
    (D tangentArea perimeter : ℝ)
    (hbase : 0 ≤ 4 + D)
    (hphase : 4 + D ≤ tangentArea)
    (hchakerian : 2 * Real.sqrt tangentArea ≤ perimeter)
    (hnegative : perimeter < line 4) :
    D < eta4 := by
  have harea0 : 0 ≤ tangentArea := le_trans hbase hphase
  have hsqrt0 : 0 ≤ 2 * Real.sqrt tangentArea := by positivity
  have hsqrtLine : 2 * Real.sqrt tangentArea < line 4 :=
    lt_of_le_of_lt hchakerian hnegative
  have hsq := square_strict_of_nonneg_lt
    (2 * Real.sqrt tangentArea) (line 4) hsqrt0 hsqrtLine
  have hsqrtSq : (2 * Real.sqrt tangentArea) ^ 2 = 4 * tangentArea := by
    rw [mul_pow, Real.sq_sqrt harea0]
    ring
  dsimp [eta4]
  rw [hsqrtSq] at hsq
  nlinarith

/-- Five-sided negative owners have total phase defect below `eta5`. -/
theorem pentagon_defect_budget
    (D tangentArea perimeter : ℝ)
    (hbase : 0 ≤ A5 + D)
    (hphase : A5 + D ≤ tangentArea)
    (hchakerian : 2 * Real.sqrt tangentArea ≤ perimeter)
    (hnegative : perimeter < line 5) :
    D < eta5 := by
  have harea0 : 0 ≤ tangentArea := le_trans hbase hphase
  have hsqrt0 : 0 ≤ 2 * Real.sqrt tangentArea := by positivity
  have hsqrtLine : 2 * Real.sqrt tangentArea < line 5 :=
    lt_of_le_of_lt hchakerian hnegative
  have hsq := square_strict_of_nonneg_lt
    (2 * Real.sqrt tangentArea) (line 5) hsqrt0 hsqrtLine
  have hsqrtSq : (2 * Real.sqrt tangentArea) ^ 2 = 4 * tangentArea := by
    rw [mul_pow, Real.sq_sqrt harea0]
    ring
  dsimp [eta5]
  rw [hsqrtSq] at hsq
  nlinarith

/-- Complete abstract quadrilateral pipeline from phase area to a selected
certificate-root edge. -/
theorem negative_quadrilateral_has_root_edge
    (turn : Fin 4 → ℝ) (tangentArea perimeter : ℝ)
    (hpos : ∀ i, 0 ≤ turn i) (hltpi : ∀ i, turn i < Real.pi)
    (hsumAngles : (∑ i, turn i) = 2 * Real.pi)
    (hphase : 4 + (∑ i, turnDefect (turn i)) ≤ tangentArea)
    (hchakerian : 2 * Real.sqrt tangentArea ≤ perimeter)
    (hnegative : perimeter < line 4) :
    ((46 * Real.pi / 100 ≤ turn 0 ∧ turn 0 ≤ 53 * Real.pi / 100) ∧
      (46 * Real.pi / 100 ≤ turn 1 ∧ turn 1 ≤ 53 * Real.pi / 100)) ∨
    ((46 * Real.pi / 100 ≤ turn 1 ∧ turn 1 ≤ 53 * Real.pi / 100) ∧
      (46 * Real.pi / 100 ≤ turn 2 ∧ turn 2 ≤ 53 * Real.pi / 100)) ∨
    ((46 * Real.pi / 100 ≤ turn 2 ∧ turn 2 ≤ 53 * Real.pi / 100) ∧
      (46 * Real.pi / 100 ≤ turn 3 ∧ turn 3 ≤ 53 * Real.pi / 100)) ∨
    ((46 * Real.pi / 100 ≤ turn 3 ∧ turn 3 ≤ 53 * Real.pi / 100) ∧
      (46 * Real.pi / 100 ≤ turn 0 ∧ turn 0 ≤ 53 * Real.pi / 100)) := by
  have hdef0 : ∀ i, 0 ≤ turnDefect (turn i) :=
    fun i => turnDefect_nonneg (turn i) (hpos i) (hltpi i)
  have hsum0 : 0 ≤ 4 + ∑ i, turnDefect (turn i) := by
    have : 0 ≤ ∑ i, turnDefect (turn i) := Finset.sum_nonneg (fun i _ => hdef0 i)
    linarith
  have hbudget := quadrilateral_defect_budget
    (∑ i, turnDefect (turn i)) tangentArea perimeter
    hsum0 hphase hchakerian hnegative
  exact quadrilateral_owner_has_root_edge turn hpos hltpi hsumAngles hbudget

/-- Complete abstract pentagonal pipeline from phase area to a selected
certificate-root edge. -/
theorem negative_pentagon_has_root_edge
    (turn : Fin 5 → ℝ) (tangentArea perimeter : ℝ)
    (hpos : ∀ i, 0 ≤ turn i) (hltpi : ∀ i, turn i < Real.pi)
    (hsumAngles : (∑ i, turn i) = 2 * Real.pi)
    (hphase : A5 + (∑ i, turnDefect (turn i)) ≤ tangentArea)
    (hchakerian : 2 * Real.sqrt tangentArea ≤ perimeter)
    (hnegative : perimeter < line 5) :
    ((47 * Real.pi / 100 ≤ turn 0 ∧ turn 0 ≤ 13 * Real.pi / 25) ∧
      (47 * Real.pi / 100 ≤ turn 1 ∧ turn 1 ≤ 13 * Real.pi / 25)) ∨
    ((47 * Real.pi / 100 ≤ turn 1 ∧ turn 1 ≤ 13 * Real.pi / 25) ∧
      (47 * Real.pi / 100 ≤ turn 2 ∧ turn 2 ≤ 13 * Real.pi / 25)) ∨
    ((47 * Real.pi / 100 ≤ turn 2 ∧ turn 2 ≤ 13 * Real.pi / 25) ∧
      (47 * Real.pi / 100 ≤ turn 3 ∧ turn 3 ≤ 13 * Real.pi / 25)) ∨
    ((47 * Real.pi / 100 ≤ turn 3 ∧ turn 3 ≤ 13 * Real.pi / 25) ∧
      (47 * Real.pi / 100 ≤ turn 4 ∧ turn 4 ≤ 13 * Real.pi / 25)) ∨
    ((47 * Real.pi / 100 ≤ turn 4 ∧ turn 4 ≤ 13 * Real.pi / 25) ∧
      (47 * Real.pi / 100 ≤ turn 0 ∧ turn 0 ≤ 13 * Real.pi / 25)) := by
  have hdef0 : ∀ i, 0 ≤ turnDefect (turn i) :=
    fun i => turnDefect_nonneg (turn i) (hpos i) (hltpi i)
  have hsum0 : 0 ≤ A5 + ∑ i, turnDefect (turn i) := by
    have hD : 0 ≤ ∑ i, turnDefect (turn i) := Finset.sum_nonneg (fun i _ => hdef0 i)
    have hA5 : 0 < A5 := by
      dsimp [A5]
      nlinarith [s_pos]
    linarith
  have hbudget := pentagon_defect_budget
    (∑ i, turnDefect (turn i)) tangentArea perimeter
    hsum0 hphase hchakerian hnegative
  exact pentagon_owner_has_root_edge turn hpos hltpi hsumAngles hbudget

end

end NegativeOwnerBudgetStandalone
