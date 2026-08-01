import NegativeOwnerBudgetStandalone
import OctagonBenchmarkStandalone

/-!
# Cyclic root-edge selection in the exact interval coordinates

This module converts the four/five-way disjunctions of the dangerous-fan
classification into a single cyclic edge index and then normalizes all angles
by `pi`, exactly as expected by the six-variable interval certificate.
-/

namespace CyclicRootEdgeSelectionStandalone

noncomputable section

open Real
open scoped BigOperators
open OctagonBase
open OctagonBenchmarkStandalone
open DangerousFanClassificationStandalone
open NegativeOwnerBudgetStandalone


def next4 (i : Fin 4) : Fin 4 := i + 1

def next5 (i : Fin 5) : Fin 5 := i + 1

lemma quadrilateral_disjunction_to_cyclic
    (turn : Fin 4 → ℝ)
    (h :
      ((46 * Real.pi / 100 ≤ turn 0 ∧ turn 0 ≤ 53 * Real.pi / 100) ∧
        (46 * Real.pi / 100 ≤ turn 1 ∧ turn 1 ≤ 53 * Real.pi / 100)) ∨
      ((46 * Real.pi / 100 ≤ turn 1 ∧ turn 1 ≤ 53 * Real.pi / 100) ∧
        (46 * Real.pi / 100 ≤ turn 2 ∧ turn 2 ≤ 53 * Real.pi / 100)) ∨
      ((46 * Real.pi / 100 ≤ turn 2 ∧ turn 2 ≤ 53 * Real.pi / 100) ∧
        (46 * Real.pi / 100 ≤ turn 3 ∧ turn 3 ≤ 53 * Real.pi / 100)) ∨
      ((46 * Real.pi / 100 ≤ turn 3 ∧ turn 3 ≤ 53 * Real.pi / 100) ∧
        (46 * Real.pi / 100 ≤ turn 0 ∧ turn 0 ≤ 53 * Real.pi / 100))) :
    ∃ i : Fin 4,
      (46 * Real.pi / 100 ≤ turn i ∧ turn i ≤ 53 * Real.pi / 100) ∧
      (46 * Real.pi / 100 ≤ turn (next4 i) ∧
        turn (next4 i) ≤ 53 * Real.pi / 100) := by
  rcases h with h01 | h12 | h23 | h30
  · exact ⟨0, h01.1, by simpa [next4] using h01.2⟩
  · exact ⟨1, h12.1, by simpa [next4] using h12.2⟩
  · exact ⟨2, h23.1, by simpa [next4] using h23.2⟩
  · exact ⟨3, h30.1, by simpa [next4] using h30.2⟩

lemma pentagon_disjunction_to_cyclic
    (turn : Fin 5 → ℝ)
    (h :
      ((47 * Real.pi / 100 ≤ turn 0 ∧ turn 0 ≤ 13 * Real.pi / 25) ∧
        (47 * Real.pi / 100 ≤ turn 1 ∧ turn 1 ≤ 13 * Real.pi / 25)) ∨
      ((47 * Real.pi / 100 ≤ turn 1 ∧ turn 1 ≤ 13 * Real.pi / 25) ∧
        (47 * Real.pi / 100 ≤ turn 2 ∧ turn 2 ≤ 13 * Real.pi / 25)) ∨
      ((47 * Real.pi / 100 ≤ turn 2 ∧ turn 2 ≤ 13 * Real.pi / 25) ∧
        (47 * Real.pi / 100 ≤ turn 3 ∧ turn 3 ≤ 13 * Real.pi / 25)) ∨
      ((47 * Real.pi / 100 ≤ turn 3 ∧ turn 3 ≤ 13 * Real.pi / 25) ∧
        (47 * Real.pi / 100 ≤ turn 4 ∧ turn 4 ≤ 13 * Real.pi / 25)) ∨
      ((47 * Real.pi / 100 ≤ turn 4 ∧ turn 4 ≤ 13 * Real.pi / 25) ∧
        (47 * Real.pi / 100 ≤ turn 0 ∧ turn 0 ≤ 13 * Real.pi / 25))) :
    ∃ i : Fin 5,
      (47 * Real.pi / 100 ≤ turn i ∧ turn i ≤ 13 * Real.pi / 25) ∧
      (47 * Real.pi / 100 ≤ turn (next5 i) ∧
        turn (next5 i) ≤ 13 * Real.pi / 25) := by
  rcases h with h01 | h12 | h23 | h34 | h40
  · exact ⟨0, h01.1, by simpa [next5] using h01.2⟩
  · exact ⟨1, h12.1, by simpa [next5] using h12.2⟩
  · exact ⟨2, h23.1, by simpa [next5] using h23.2⟩
  · exact ⟨3, h34.1, by simpa [next5] using h34.2⟩
  · exact ⟨4, h40.1, by simpa [next5] using h40.2⟩

lemma normalize_quad_root
    (a : ℝ) (hlo : 46 * Real.pi / 100 ≤ a)
    (hhi : a ≤ 53 * Real.pi / 100) :
    (23 : ℝ) / 50 ≤ a / Real.pi ∧ a / Real.pi ≤ (53 : ℝ) / 100 := by
  constructor
  · apply (le_div_iff₀ Real.pi_pos).2
    nlinarith
  · apply (div_le_iff₀ Real.pi_pos).2
    nlinarith

lemma normalize_pent_root
    (a : ℝ) (hlo : 47 * Real.pi / 100 ≤ a)
    (hhi : a ≤ 13 * Real.pi / 25) :
    (47 : ℝ) / 100 ≤ a / Real.pi ∧ a / Real.pi ≤ (13 : ℝ) / 25 := by
  constructor
  · apply (le_div_iff₀ Real.pi_pos).2
    nlinarith
  · apply (div_le_iff₀ Real.pi_pos).2
    nlinarith

/-- Complete normalized root-edge selection for a negative quadrilateral. -/
theorem negative_quadrilateral_normalized_root_edge
    (turn : Fin 4 → ℝ) (tangentArea perimeter : ℝ)
    (hpos : ∀ i, 0 ≤ turn i) (hltpi : ∀ i, turn i < Real.pi)
    (hsumAngles : (∑ i, turn i) = 2 * Real.pi)
    (hphase : 4 + (∑ i, turnDefect (turn i)) ≤ tangentArea)
    (hchakerian : 2 * Real.sqrt tangentArea ≤ perimeter)
    (hnegative : perimeter < line 4) :
    ∃ i : Fin 4,
      ((23 : ℝ) / 50 ≤ turn i / Real.pi ∧
        turn i / Real.pi ≤ (53 : ℝ) / 100) ∧
      ((23 : ℝ) / 50 ≤ turn (next4 i) / Real.pi ∧
        turn (next4 i) / Real.pi ≤ (53 : ℝ) / 100) := by
  have hroot := negative_quadrilateral_has_root_edge turn tangentArea perimeter
    hpos hltpi hsumAngles hphase hchakerian hnegative
  obtain ⟨i, hi, hn⟩ := quadrilateral_disjunction_to_cyclic turn hroot
  exact ⟨i, normalize_quad_root (turn i) hi.1 hi.2,
    normalize_quad_root (turn (next4 i)) hn.1 hn.2⟩

/-- Complete normalized root-edge selection for a negative pentagon. -/
theorem negative_pentagon_normalized_root_edge
    (turn : Fin 5 → ℝ) (tangentArea perimeter : ℝ)
    (hpos : ∀ i, 0 ≤ turn i) (hltpi : ∀ i, turn i < Real.pi)
    (hsumAngles : (∑ i, turn i) = 2 * Real.pi)
    (hphase : A5 + (∑ i, turnDefect (turn i)) ≤ tangentArea)
    (hchakerian : 2 * Real.sqrt tangentArea ≤ perimeter)
    (hnegative : perimeter < line 5) :
    ∃ i : Fin 5,
      ((47 : ℝ) / 100 ≤ turn i / Real.pi ∧
        turn i / Real.pi ≤ (13 : ℝ) / 25) ∧
      ((47 : ℝ) / 100 ≤ turn (next5 i) / Real.pi ∧
        turn (next5 i) / Real.pi ≤ (13 : ℝ) / 25) := by
  have hroot := negative_pentagon_has_root_edge turn tangentArea perimeter
    hpos hltpi hsumAngles hphase hchakerian hnegative
  obtain ⟨i, hi, hn⟩ := pentagon_disjunction_to_cyclic turn hroot
  exact ⟨i, normalize_pent_root (turn i) hi.1 hi.2,
    normalize_pent_root (turn (next5 i)) hn.1 hn.2⟩

/-- At a trivalent endpoint, a selected owner angle in the quadrilateral root
box forces the opposite-cell angle into the verifier's `[0,0.54]` box. -/
theorem opposite_normalized_root
    (owner opposite third : ℝ)
    (howner : 23 * Real.pi / 50 ≤ owner)
    (hopposite : 0 ≤ opposite) (hthird : 0 ≤ third)
    (hsum : owner + opposite + third = Real.pi) :
    0 ≤ opposite / Real.pi ∧ opposite / Real.pi ≤ (27 : ℝ) / 50 := by
  constructor
  · exact div_nonneg hopposite Real.pi_pos.le
  · apply (div_le_iff₀ Real.pi_pos).2
    nlinarith

lemma line_four_lt_eight_point_two : line 4 < (41 : ℝ) / 5 := by
  rw [line_four]
  have hp8 : 0 ≤ p8 := by dsimp [p8]; positivity
  nlinarith [p6_upper]

lemma line_five_lt_eight_point_two : line 5 < (41 : ℝ) / 5 := by
  rw [line_five]
  have hp8 : 0 ≤ p8 := by dsimp [p8]; positivity
  nlinarith [p6_upper]

/-- The selected shared edge lies in the verifier's length root box. -/
theorem negative_owner_edge_length_lt_four_point_one
    (n : ℕ) (perimeter x : ℝ) (hn : n = 4 ∨ n = 5)
    (htwox : 2 * x ≤ perimeter) (hnegative : perimeter < line n) :
    x < (41 : ℝ) / 10 := by
  rcases hn with rfl | rfl
  · nlinarith [line_four_lt_eight_point_two]
  · nlinarith [line_five_lt_eight_point_two]

end

end CyclicRootEdgeSelectionStandalone
