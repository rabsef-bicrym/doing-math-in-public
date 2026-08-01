import PhaseSnappingSum
import OctagonalCornerBank
import LargeCellCornerBank

/-!
# Cell-level bridge from phase snapping to funded corner credits

This module packages the geometric data of one convex cell as a finite normal fan.
Once each normal gap satisfies the local phase-area and small-gap reserve bounds,
the summed phase-snapping theorem supplies the perimeter hypothesis required by
the octagonal corner bank.  The final theorem covers every side count `n ≥ 4`.
-/

namespace NoncrystallineCellBridge

noncomputable section

open Real
open scoped BigOperators
open PairGapCore
open NoncrystallineDomainReduction
open ContinuousCornerBank
open OctagonalCornerBank
open PhaseSnappingSum

/-- The scalar data extracted from the cyclic normal fan of one cell.  Angles are
normalized by `π`, so the gaps sum to two. -/
structure FanData (n : ℕ) where
  gap : Fin n → ℝ
  defect : Fin n → ℝ
  contribution : Fin n → ℝ
  tangentArea : ℝ
  perimeter : ℝ
  gapSum : (∑ i, gap i) = 2
  defectNonneg : ∀ i, 0 ≤ defect i
  localArea : ∀ i,
    phaseSlope * gap i - cap + defect i ≤ contribution i
  localReserve : ∀ i,
    smallGapReserve * pos (1 - 4 * gap i) ≤ defect i
  areaEq : tangentArea = ∑ i, contribution i
  baseNonneg : 0 ≤ phaseBase n + ∑ i, defect i
  chakerian : 2 * Real.sqrt tangentArea ≤ perimeter

/-- The summed geometric consequences of one fan. -/
theorem fan_phase_bridge {n : ℕ} (F : FanData n) :
    phaseBase n + (∑ i, F.defect i) ≤ F.tangentArea ∧
      ((n : ℝ) - 8) * smallGapReserve ≤ ∑ i, F.defect i ∧
      2 * Real.sqrt (phaseBase n + ∑ i, F.defect i) ≤ F.perimeter := by
  simpa using
    (phase_snapping_bridge (Finset.univ : Finset (Fin n))
      F.gap F.defect F.contribution F.tangentArea F.perimeter
      (by simpa using F.gapSum)
      (by intro i hi; exact F.localArea i)
      (by intro i hi; exact F.localReserve i)
      F.areaEq F.baseNonneg F.chakerian)

lemma phaseBase_four : phaseBase 4 = 4 := by
  dsimp [phaseBase, A8, cap, d]
  norm_num
  nlinarith [s_sq]

lemma phaseBase_five : phaseBase 5 = A5 := by
  dsimp [phaseBase, A8, A5, cap, d]
  norm_num
  nlinarith [s_sq]

lemma phaseBase_six : phaseBase 6 = A6 := by
  dsimp [phaseBase, A8, A6, cap, d]
  norm_num
  nlinarith [s_sq]

lemma phaseBase_seven : phaseBase 7 = A7 := by
  dsimp [phaseBase, A8, A7, cap, d]
  norm_num
  nlinarith [s_sq]

lemma phaseBase_eight : phaseBase 8 = A8 := by
  simp [phaseBase]

/-- Four-sided cells feed directly into the exact octagonal bank theorem. -/
theorem corner_bank_four (F : FanData 4) :
    (∑ i, cornerCredit 4 (F.defect i)) ≤
      ((17 : ℝ) / 80) * pos (F.perimeter - line 4) := by
  have hP := (fan_phase_bridge F).2.2
  rw [phaseBase_four] at hP
  exact bank4 F.defect F.perimeter F.defectNonneg hP

/-- Five-sided cells feed directly into the exact octagonal bank theorem. -/
theorem corner_bank_five (F : FanData 5) :
    (∑ i, cornerCredit 5 (F.defect i)) ≤
      ((17 : ℝ) / 80) * pos (F.perimeter - line 5) := by
  have hP := (fan_phase_bridge F).2.2
  rw [phaseBase_five] at hP
  exact bank5 F.defect F.perimeter F.defectNonneg hP

/-- Six-sided cells feed directly into the exact octagonal bank theorem. -/
theorem corner_bank_six (F : FanData 6) :
    (∑ i, cornerCredit 6 (F.defect i)) ≤
      ((17 : ℝ) / 80) * pos (F.perimeter - line 6) := by
  have hP := (fan_phase_bridge F).2.2
  rw [phaseBase_six] at hP
  exact bank6 F.defect F.perimeter F.defectNonneg hP

/-- Seven-sided cells feed directly into the exact octagonal bank theorem. -/
theorem corner_bank_seven (F : FanData 7) :
    (∑ i, cornerCredit 7 (F.defect i)) ≤
      ((17 : ℝ) / 80) * pos (F.perimeter - line 7) := by
  have hP := (fan_phase_bridge F).2.2
  rw [phaseBase_seven] at hP
  exact bank7 F.defect F.perimeter F.defectNonneg hP

/-- For every `n ≥ 4`, local phase snapping funds the complete corner bank.
For `n ≥ 8`, the only extra geometric input is the universal octagonal
isoperimetric lower bound `p8 ≤ perimeter`. -/
theorem corner_bank_all {n : ℕ} (F : FanData n) (hn : 4 ≤ n)
    (huniversal : 8 ≤ n → p8 ≤ F.perimeter) :
    (∑ i, cornerCredit n (F.defect i)) ≤
      ((17 : ℝ) / 80) * pos (F.perimeter - line n) := by
  by_cases hn8 : 8 ≤ n
  · have hP := (fan_phase_bridge F).2.2
    exact LargeCellCornerBank.bank_ge_eight n F.defect F.perimeter hn8
      F.defectNonneg (huniversal hn8) hP
  · have hn7 : n ≤ 7 := by omega
    have hcases : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact corner_bank_four F
    · exact corner_bank_five F
    · exact corner_bank_six F
    · exact corner_bank_seven F

end

end NoncrystallineCellBridge
