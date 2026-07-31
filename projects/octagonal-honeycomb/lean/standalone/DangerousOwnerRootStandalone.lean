import DangerousFanClassificationStandalone
import ReducedFanBridgeStandalone

/-!
# Whole-fan classification and normalized selected root edges

This module closes the gap between the one-angle phase classification and the
six-variable interval root boxes.  A negative four- or five-sided reduced fan
has a small total phase-defect budget.  Nonnegativity makes the same budget
available for every individual turn.  The resulting angular windows force a
cyclic adjacent pair in the exact normalized owner boxes used by the interval
certificate.
-/

namespace DangerousOwnerRootStandalone

noncomputable section

open Real
open scoped BigOperators
open OctagonBase
open OctagonBenchmarkStandalone
open FirstSectorClassificationAlgebra
open AllSectorDefectStandalone
open PhaseGapBridgeStandalone
open ReducedFanBridgeStandalone
open DangerousFanClassificationStandalone

lemma phaseBase_four : phaseBase 4 = 4 := by
  dsimp [phaseBase, phaseSlope, cap, d]
  nlinarith [s_sq]

lemma phaseBase_five : phaseBase 5 = A5 := by
  dsimp [phaseBase, phaseSlope, cap, d, A5]
  nlinarith [s_sq]

lemma square_strict_of_nonneg_lt
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : a ^ 2 < b ^ 2 := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hp : 0 < (b - a) * (b + a) :=
    mul_pos (sub_pos.mpr hab) (add_pos_of_pos_of_nonneg hb ha)
  nlinarith

lemma term_le_sum_of_nonneg
    {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    f i ≤ ∑ j, f j := by
  exact Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

/-- Negative quadrilateral fans have total phase defect below `eta4`. -/
theorem quadrilateral_defect_budget
    (F : FanData 4) (perimeter : ℝ)
    (hchakerian : 2 * Real.sqrt F.tangentArea ≤ perimeter)
    (hnegative : perimeter < line 4) :
    (∑ i, actualDefect (F.gap i)) < eta4 := by
  have hD0 : 0 ≤ ∑ i, actualDefect (F.gap i) :=
    Finset.sum_nonneg fun i _ => defect_nonneg F i
  have hphase := tangent_area_lower F
  rw [phaseBase_four] at hphase
  have hbase : 0 ≤ 4 + ∑ i, actualDefect (F.gap i) := by linarith
  have harea0 : 0 ≤ F.tangentArea := le_trans hbase hphase
  have hsqrt0 : 0 ≤ 2 * Real.sqrt F.tangentArea := by positivity
  have hsqrtLine : 2 * Real.sqrt F.tangentArea < line 4 :=
    lt_of_le_of_lt hchakerian hnegative
  have hsq := square_strict_of_nonneg_lt
    (2 * Real.sqrt F.tangentArea) (line 4) hsqrt0 hsqrtLine
  have hsqrtSq : (2 * Real.sqrt F.tangentArea) ^ 2 = 4 * F.tangentArea := by
    rw [mul_pow, Real.sq_sqrt harea0]
    ring
  rw [hsqrtSq] at hsq
  dsimp [eta4, A4]
  nlinarith

/-- Negative pentagonal fans have total phase defect below `eta5`. -/
theorem pentagon_defect_budget
    (F : FanData 5) (perimeter : ℝ)
    (hchakerian : 2 * Real.sqrt F.tangentArea ≤ perimeter)
    (hnegative : perimeter < line 5) :
    (∑ i, actualDefect (F.gap i)) < eta5 := by
  have hD0 : 0 ≤ ∑ i, actualDefect (F.gap i) :=
    Finset.sum_nonneg fun i _ => defect_nonneg F i
  have hphase := tangent_area_lower F
  rw [phaseBase_five] at hphase
  have hA5 : 0 < A5 := A5_pos
  have hbase : 0 ≤ A5 + ∑ i, actualDefect (F.gap i) := by linarith
  have harea0 : 0 ≤ F.tangentArea := le_trans hbase hphase
  have hsqrt0 : 0 ≤ 2 * Real.sqrt F.tangentArea := by positivity
  have hsqrtLine : 2 * Real.sqrt F.tangentArea < line 5 :=
    lt_of_le_of_lt hchakerian hnegative
  have hsq := square_strict_of_nonneg_lt
    (2 * Real.sqrt F.tangentArea) (line 5) hsqrt0 hsqrtLine
  have hsqrtSq : (2 * Real.sqrt F.tangentArea) ^ 2 = 4 * F.tangentArea := by
    rw [mul_pow, Real.sq_sqrt harea0]
    ring
  rw [hsqrtSq] at hsq
  dsimp [eta5]
  nlinarith

def next4 (i : Fin 4) : Fin 4 := i + 1

def next5 (i : Fin 5) : Fin 5 := i + 1

/-- Four turns summing to a full turn and all below 92 degrees contain an
adjacent pair in the quadrilateral interval root box. -/
theorem quadrilateral_angles_have_root_edge
    (turn : Fin 4 → ℝ)
    (hsum : (∑ i, turn i) = 2 * Real.pi)
    (hu : ∀ i, turn i < 92 * Real.pi / 180) :
    ∃ i : Fin 4,
      (46 * Real.pi / 100 ≤ turn i ∧ turn i ≤ 53 * Real.pi / 100) ∧
      (46 * Real.pi / 100 ≤ turn (next4 i) ∧
        turn (next4 i) ≤ 53 * Real.pi / 100) := by
  have hsum' : turn 0 + (turn 1 + (turn 2 + turn 3)) = 2 * Real.pi := by
    simpa [Fin.sum_univ_succ] using hsum
  have u0 : turn 0 ≤ 53 * Real.pi / 100 := by nlinarith [hu 0, Real.pi_pos]
  have u1 : turn 1 ≤ 53 * Real.pi / 100 := by nlinarith [hu 1, Real.pi_pos]
  have u2 : turn 2 ≤ 53 * Real.pi / 100 := by nlinarith [hu 2, Real.pi_pos]
  have u3 : turn 3 ≤ 53 * Real.pi / 100 := by nlinarith [hu 3, Real.pi_pos]
  by_cases h0 : 46 * Real.pi / 100 ≤ turn 0
  · by_cases h1 : 46 * Real.pi / 100 ≤ turn 1
    · exact ⟨0, ⟨h0, u0⟩, by simpa [next4] using And.intro h1 u1⟩
    · by_cases h3 : 46 * Real.pi / 100 ≤ turn 3
      · exact ⟨3, ⟨h3, u3⟩, by simpa [next4] using And.intro h0 u0⟩
      · have h1' : turn 1 < 46 * Real.pi / 100 := lt_of_not_ge h1
        have h3' : turn 3 < 46 * Real.pi / 100 := lt_of_not_ge h3
        exfalso
        nlinarith [hu 0, hu 2, Real.pi_pos]
  · have h0' : turn 0 < 46 * Real.pi / 100 := lt_of_not_ge h0
    by_cases h2 : 46 * Real.pi / 100 ≤ turn 2
    · by_cases h1 : 46 * Real.pi / 100 ≤ turn 1
      · exact ⟨1, ⟨h1, u1⟩, by simpa [next4] using And.intro h2 u2⟩
      · by_cases h3 : 46 * Real.pi / 100 ≤ turn 3
        · exact ⟨2, ⟨h2, u2⟩, by simpa [next4] using And.intro h3 u3⟩
        · have h1' : turn 1 < 46 * Real.pi / 100 := lt_of_not_ge h1
          have h3' : turn 3 < 46 * Real.pi / 100 := lt_of_not_ge h3
          exfalso
          nlinarith [hu 2, Real.pi_pos]
    · have h2' : turn 2 < 46 * Real.pi / 100 := lt_of_not_ge h2
      exfalso
      nlinarith [hu 1, hu 3, Real.pi_pos]

def LowTurn (a : ℝ) : Prop :=
  43 * Real.pi / 180 < a ∧ a < 58 * Real.pi / 180

def HighTurn (a : ℝ) : Prop :=
  87 * Real.pi / 180 < a ∧ a < 91 * Real.pi / 180

/-- Five turns in the classified low/high windows and summing to 360 degrees
contain cyclically adjacent high turns. -/
theorem pentagon_windows_have_adjacent_high
    (turn : Fin 5 → ℝ)
    (hsum : (∑ i, turn i) = 2 * Real.pi)
    (hclass : ∀ i, LowTurn (turn i) ∨ HighTurn (turn i)) :
    ∃ i : Fin 5, HighTurn (turn i) ∧ HighTurn (turn (next5 i)) := by
  have hsum' : turn 0 + (turn 1 + (turn 2 + (turn 3 + turn 4))) = 2 * Real.pi := by
    simpa [Fin.sum_univ_succ] using hsum
  have h0 := hclass 0
  have h1 := hclass 1
  have h2 := hclass 2
  have h3 := hclass 3
  have h4 := hclass 4
  rcases h0 with h0 | h0 <;>
  rcases h1 with h1 | h1 <;>
  rcases h2 with h2 | h2 <;>
  rcases h3 with h3 | h3 <;>
  rcases h4 with h4 | h4
  all_goals
    first
    | exact ⟨0, h0, by simpa [next5] using h1⟩
    | exact ⟨1, h1, by simpa [next5] using h2⟩
    | exact ⟨2, h2, by simpa [next5] using h3⟩
    | exact ⟨3, h3, by simpa [next5] using h4⟩
    | exact ⟨4, h4, by simpa [next5] using h0⟩
    | rcases h0 with ⟨h0a, h0b⟩
      rcases h1 with ⟨h1a, h1b⟩
      rcases h2 with ⟨h2a, h2b⟩
      rcases h3 with ⟨h3a, h3b⟩
      rcases h4 with ⟨h4a, h4b⟩
      exfalso
      nlinarith [Real.pi_pos]

lemma normalize_quad
    (a : ℝ) (hlo : 46 * Real.pi / 100 ≤ a)
    (hhi : a ≤ 53 * Real.pi / 100) :
    (23 : ℝ) / 50 ≤ a / Real.pi ∧ a / Real.pi ≤ (53 : ℝ) / 100 := by
  constructor
  · apply (le_div_iff₀ Real.pi_pos).2
    nlinarith
  · apply (div_le_iff₀ Real.pi_pos).2
    nlinarith

lemma normalize_pent
    (a : ℝ) (h : HighTurn a) :
    (47 : ℝ) / 100 ≤ a / Real.pi ∧ a / Real.pi ≤ (13 : ℝ) / 25 := by
  rcases h with ⟨hlo, hhi⟩
  constructor
  · apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_pos]
  · apply (div_le_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_pos]

/-- Complete whole-fan root-box theorem for a negative quadrilateral. -/
theorem negative_quadrilateral_normalized_root_edge
    (F : FanData 4) (perimeter : ℝ)
    (hchakerian : 2 * Real.sqrt F.tangentArea ≤ perimeter)
    (hnegative : perimeter < line 4) :
    ∃ i : Fin 4,
      ((23 : ℝ) / 50 ≤ F.gap i / Real.pi ∧
        F.gap i / Real.pi ≤ (53 : ℝ) / 100) ∧
      ((23 : ℝ) / 50 ≤ F.gap (next4 i) / Real.pi ∧
        F.gap (next4 i) / Real.pi ≤ (53 : ℝ) / 100) := by
  have hbudget := quadrilateral_defect_budget F perimeter hchakerian hnegative
  have htotal : (∑ i, actualDefect (F.gap i)) < (17 : ℝ) / 1000 :=
    lt_trans hbudget eta4_lt_seventeen_thousandths
  have hu : ∀ i, F.gap i < 92 * Real.pi / 180 := by
    intro i
    have hterm := term_le_sum_of_nonneg
      (fun j => actualDefect (F.gap j)) (fun j => defect_nonneg F j) i
    have hsmall : actualDefect (F.gap i) < (17 : ℝ) / 1000 :=
      lt_of_le_of_lt hterm htotal
    by_contra hn
    have hlarge := defect_ge_q4_of_ninety_two_le
      (F.gap i) (le_of_not_gt hn) (F.gapLtPi i)
    exact (not_lt_of_ge hlarge hsmall).elim
  obtain ⟨i, hi, hn⟩ := quadrilateral_angles_have_root_edge F.gap F.gapSum hu
  exact ⟨i, normalize_quad (F.gap i) hi.1 hi.2,
    normalize_quad (F.gap (next4 i)) hn.1 hn.2⟩

/-- Complete whole-fan root-box theorem for a negative pentagon. -/
theorem negative_pentagon_normalized_root_edge
    (F : FanData 5) (perimeter : ℝ)
    (hchakerian : 2 * Real.sqrt F.tangentArea ≤ perimeter)
    (hnegative : perimeter < line 5) :
    ∃ i : Fin 5,
      ((47 : ℝ) / 100 ≤ F.gap i / Real.pi ∧
        F.gap i / Real.pi ≤ (13 : ℝ) / 25) ∧
      ((47 : ℝ) / 100 ≤ F.gap (next5 i) / Real.pi ∧
        F.gap (next5 i) / Real.pi ≤ (13 : ℝ) / 25) := by
  have hbudget := pentagon_defect_budget F perimeter hchakerian hnegative
  have htotal : (∑ i, actualDefect (F.gap i)) < q5 :=
    lt_trans hbudget eta5_lt_four_625
  have hclass : ∀ i, LowTurn (F.gap i) ∨ HighTurn (F.gap i) := by
    intro i
    have hterm := term_le_sum_of_nonneg
      (fun j => actualDefect (F.gap j)) (fun j => defect_nonneg F j) i
    have hsmall : actualDefect (F.gap i) < q5 := lt_of_le_of_lt hterm htotal
    simpa [LowTurn, HighTurn] using
      defect_lt_q5_classification (F.gap i) (F.gapPos i) (F.gapLtPi i) hsmall
  obtain ⟨i, hi, hn⟩ := pentagon_windows_have_adjacent_high F.gap F.gapSum hclass
  exact ⟨i, normalize_pent (F.gap i) hi,
    normalize_pent (F.gap (next5 i)) hn⟩

/-- A selected owner endpoint in the quadrilateral root box forces the opposite
cell endpoint into the interval verifier's `[0,0.54]` box. -/
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
  nlinarith [p6_upper_tight, p8_nonneg]

lemma line_five_lt_eight_point_two : line 5 < (41 : ℝ) / 5 := by
  rw [line_five]
  nlinarith [p6_upper_tight, p8_nonneg]

/-- The common selected edge length lies below the interval root cutoff. -/
theorem negative_owner_edge_length_lt_four_point_one
    (n : ℕ) (perimeter x : ℝ) (hn : n = 4 ∨ n = 5)
    (htwox : 2 * x ≤ perimeter) (hnegative : perimeter < line n) :
    x < (41 : ℝ) / 10 := by
  rcases hn with rfl | rfl
  · nlinarith [line_four_lt_eight_point_two]
  · nlinarith [line_five_lt_eight_point_two]

end

end DangerousOwnerRootStandalone
