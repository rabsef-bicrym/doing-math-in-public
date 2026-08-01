import ContinuousCornerBank
import NoncrystallineDomainReduction

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Octagonal instantiation of the continuous corner bank

This module checks the exact octagonal constants needed to instantiate the
abstract corner-bank theorem for cells with four through nine sides.  The only
geometric input left as a hypothesis in each final theorem is the phase-snapping
perimeter lower bound

  `2 * sqrt (Aₙ + Σ δᵢ) ≤ P`.
-/

namespace OctagonalCornerBank

noncomputable section

open Real
open scoped BigOperators
open PairGapCore
open PairGapBounds
open NoncrystallineDomainReduction
open ContinuousCornerBank

def cap : ℝ := d ^ 2

def eta4 : ℝ := (line 4 / 2) ^ 2 - 4

def eta5 : ℝ := (line 5 / 2) ^ 2 - A5

def threshold (n : ℕ) : ℝ :=
  if n = 4 then eta4 else if n = 5 then eta5 else 0

def cornerCredit (n : ℕ) (defect : ℝ) : ℝ :=
  potential cap (threshold n) defect / 10

def underCredit (defect : ℝ) : ℝ :=
  potential cap eta4 defect / 10

lemma cap_eq : cap = 3 - 2 * s := by
  dsimp [cap, d]
  nlinarith [s_sq]

lemma cap_pos : 0 < cap := by
  rw [cap_eq]
  nlinarith [s_upper]

lemma cap_nonneg : 0 ≤ cap := cap_pos.le

lemma cap_lower : (17 : ℝ) / 100 < cap := by
  rw [cap_eq]
  nlinarith [s_upper]

lemma cap_upper : cap < (43 : ℝ) / 250 := by
  rw [cap_eq]
  nlinarith [s_lower]

lemma line4_pos : 0 < line 4 := by
  rw [line_four]
  nlinarith [p6_lower, p8_upper]

lemma line4_lower : (4007 : ℝ) / 1000 < line 4 := by
  rw [line_four]
  nlinarith [p6_lower, p8_upper]

lemma line4_upper : line 4 < (4009 : ℝ) / 1000 := by
  rw [line_four]
  nlinarith [p6_upper, p8_lower]

lemma line5_pos : 0 < line 5 := by
  rw [line_five]
  nlinarith [p6_lower, p8_upper]

lemma line5_upper : line 5 < (3917 : ℝ) / 1000 := by
  rw [line_five]
  nlinarith [p6_upper, p8_lower]

lemma line5_gt_p5 : p5 < line 5 := by
  rw [line_five]
  nlinarith [p6_lower, p8_upper, p5_upper]

lemma eta4_nonneg : 0 ≤ eta4 := by
  have hleft : 0 ≤ line 4 / 2 - 2 := by
    nlinarith [line4_lower]
  have hright : 0 ≤ line 4 / 2 + 2 := by
    nlinarith [line4_pos]
  have hprod := mul_nonneg hleft hright
  dsimp [eta4]
  nlinarith

lemma eta4_lower : (1 : ℝ) / 100 < eta4 := by
  have hhalf : (4007 : ℝ) / 2000 < line 4 / 2 := by
    nlinarith [line4_lower]
  have hsum : 0 < line 4 / 2 + (4007 : ℝ) / 2000 := by
    nlinarith [line4_pos]
  have hprod := mul_pos (sub_pos.mpr hhalf) hsum
  dsimp [eta4]
  nlinarith

lemma eta4_upper : eta4 < (1 : ℝ) / 50 := by
  have hhalf : line 4 / 2 < (4009 : ℝ) / 2000 := by
    nlinarith [line4_upper]
  have hsum : 0 < (4009 : ℝ) / 2000 + line 4 / 2 := by
    nlinarith [line4_pos]
  have hprod := mul_pos (sub_pos.mpr hhalf) hsum
  dsimp [eta4]
  nlinarith

lemma eta5_nonneg : 0 ≤ eta5 := by
  dsimp [eta5]
  have hp5sq := p5_sq
  have hp5nonneg := p5_nonneg
  have hline := line5_gt_p5
  nlinarith

lemma eta5_upper : eta5 < (1 : ℝ) / 100 := by
  have hhalf : line 5 / 2 < (3917 : ℝ) / 2000 := by
    nlinarith [line5_upper]
  have hsum : 0 < (3917 : ℝ) / 2000 + line 5 / 2 := by
    nlinarith [line5_pos]
  have hprod := mul_pos (sub_pos.mpr hhalf) hsum
  dsimp [eta5, A5]
  nlinarith [s_lower]

lemma eta5_le_eta4 : eta5 ≤ eta4 := by
  nlinarith [eta5_upper, eta4_lower]

lemma eta4_le_cap : eta4 ≤ cap := by
  nlinarith [eta4_upper, cap_lower]

lemma eta5_le_cap : eta5 ≤ cap := by
  nlinarith [eta5_upper, cap_lower]

lemma A4_eta4_sq : 4 + eta4 = (line 4 / 2) ^ 2 := by
  dsimp [eta4]
  ring

lemma A5_eta5_sq : A5 + eta5 = (line 5 / 2) ^ 2 := by
  dsimp [eta5]
  ring

lemma A4_eta4_sqrt : Real.sqrt (4 + eta4) = line 4 / 2 := by
  have hline : 0 ≤ line 4 / 2 := by
    nlinarith [line4_pos]
  rw [A4_eta4_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg hline]

lemma A5_eta5_sqrt : Real.sqrt (A5 + eta5) = line 5 / 2 := by
  have hline : 0 ≤ line 5 / 2 := by
    nlinarith [line5_pos]
  rw [A5_eta5_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg hline]

lemma sqrt_le_of_sq_bound
    (x b : ℝ) (hx : 0 ≤ x) (hb : 0 ≤ b) (hxb : x ≤ b ^ 2) :
    Real.sqrt x ≤ b := by
  have hs0 := Real.sqrt_nonneg x
  have hs2 := Real.sq_sqrt hx
  nlinarith

lemma denom_201_217
    (F Y : ℝ) (hF : 0 ≤ F) (hY : 0 ≤ Y)
    (hFupper : F ≤ ((201 : ℝ) / 100) ^ 2)
    (hFYupper : F + Y ≤ ((217 : ℝ) / 100) ^ 2) :
    Real.sqrt (F + Y) + Real.sqrt F ≤ (17 : ℝ) / 4 := by
  have hsF := sqrt_le_of_sq_bound F ((201 : ℝ) / 100) hF (by norm_num) hFupper
  have hFY : 0 ≤ F + Y := by linarith
  have hsFY := sqrt_le_of_sq_bound (F + Y) ((217 : ℝ) / 100)
    hFY (by norm_num) hFYupper
  nlinarith

lemma denom_183_221
    (F Y : ℝ) (hF : 0 ≤ F) (hY : 0 ≤ Y)
    (hFupper : F ≤ ((183 : ℝ) / 100) ^ 2)
    (hFYupper : F + Y ≤ ((221 : ℝ) / 100) ^ 2) :
    Real.sqrt (F + Y) + Real.sqrt F ≤ (17 : ℝ) / 4 := by
  have hsF := sqrt_le_of_sq_bound F ((183 : ℝ) / 100) hF (by norm_num) hFupper
  have hFY : 0 ≤ F + Y := by linarith
  have hsFY := sqrt_le_of_sq_bound (F + Y) ((221 : ℝ) / 100)
    hFY (by norm_num) hFYupper
  nlinarith

lemma common_endpoint_upper : 16 - 8 * s < ((217 : ℝ) / 100) ^ 2 := by
  nlinarith [s_lower]

lemma nine_endpoint_upper : 19 - 10 * s < ((221 : ℝ) / 100) ^ 2 := by
  nlinarith [s_lower]

lemma denom4 :
    Real.sqrt (4 + eta4 + 4 * (cap - eta4)) +
        Real.sqrt (4 + eta4) ≤ (17 : ℝ) / 4 := by
  apply denom_201_217
  · nlinarith [eta4_nonneg]
  · nlinarith [eta4_le_cap]
  · rw [A4_eta4_sq]
    have hhalf : line 4 / 2 ≤ (201 : ℝ) / 100 := by
      nlinarith [line4_upper]
    have hsum : 0 ≤ (201 : ℝ) / 100 + line 4 / 2 := by
      nlinarith [line4_pos]
    have hprod := mul_nonneg (sub_nonneg.mpr hhalf) hsum
    nlinarith
  · rw [cap_eq]
    nlinarith [eta4_nonneg, common_endpoint_upper]

lemma denom5 :
    Real.sqrt (A5 + eta5 + 5 * (cap - eta5)) +
        Real.sqrt (A5 + eta5) ≤ (17 : ℝ) / 4 := by
  apply denom_201_217
  · nlinarith [A5_pos.le, eta5_nonneg]
  · nlinarith [eta5_le_cap]
  · rw [A5_eta5_sq]
    have hhalf : line 5 / 2 ≤ (201 : ℝ) / 100 := by
      nlinarith [line5_upper]
    have hsum : 0 ≤ (201 : ℝ) / 100 + line 5 / 2 := by
      nlinarith [line5_pos]
    have hprod := mul_nonneg (sub_nonneg.mpr hhalf) hsum
    nlinarith
  · rw [cap_eq]
    dsimp [A5]
    nlinarith [eta5_nonneg, common_endpoint_upper]

lemma denom6 :
    Real.sqrt (A6 + 6 * cap) + Real.sqrt A6 ≤ (17 : ℝ) / 4 := by
  apply denom_201_217
  · exact A6_pos.le
  · nlinarith [cap_nonneg]
  · dsimp [A6]
    nlinarith [s_upper]
  · rw [cap_eq]
    dsimp [A6]
    nlinarith [common_endpoint_upper]

lemma denom7 :
    Real.sqrt (A7 + 7 * cap) + Real.sqrt A7 ≤ (17 : ℝ) / 4 := by
  apply denom_201_217
  · exact A7_pos.le
  · nlinarith [cap_nonneg]
  · dsimp [A7]
    nlinarith [s_upper]
  · rw [cap_eq]
    dsimp [A7]
    nlinarith [common_endpoint_upper]

lemma denom8 :
    Real.sqrt (A8 + 8 * cap) + Real.sqrt A8 ≤ (17 : ℝ) / 4 := by
  apply denom_201_217
  · exact A8_pos.le
  · nlinarith [cap_nonneg]
  · dsimp [A8, d]
    nlinarith [s_upper]
  · rw [cap_eq]
    dsimp [A8, d]
    nlinarith [common_endpoint_upper]

lemma denom9 :
    Real.sqrt (A8 + 9 * cap) + Real.sqrt A8 ≤ (17 : ℝ) / 4 := by
  apply denom_183_221
  · exact A8_pos.le
  · nlinarith [cap_nonneg]
  · dsimp [A8, d]
    nlinarith [s_upper]
  · rw [cap_eq]
    dsimp [A8, d]
    nlinarith [nine_endpoint_upper]

lemma line8_eq : line 8 = p8 := by
  have h := p8_sub_line 8
  norm_num at h
  linarith

lemma line9_le_p8 : line 9 ≤ p8 := by
  have h := p8_sub_line 9
  norm_num at h
  nlinarith [slope_pos]

lemma line6_base : line 6 ≤ 2 * Real.sqrt (A6 + 0) := by
  simp [line_six, p6]

lemma line7_base : line 7 ≤ 2 * Real.sqrt (A7 + 0) := by
  have hp : p7 = 2 * Real.sqrt A7 := rfl
  rw [add_zero, ← hp]
  exact p7_gt_line_seven.le

lemma line8_base : line 8 ≤ 2 * Real.sqrt (A8 + 0) := by
  simp [line8_eq, p8]

lemma line9_base : line 9 ≤ 2 * Real.sqrt (A8 + 0) := by
  rw [add_zero]
  exact line9_le_p8

lemma threshold_le_eta4 (n : ℕ) : threshold n ≤ eta4 := by
  by_cases h4 : n = 4
  · simp [threshold, h4]
  · by_cases h5 : n = 5
    · simp [threshold, h5, eta5_le_eta4]
    · simp [threshold, h4, h5, eta4_nonneg]

lemma underCredit_le_cornerCredit (n : ℕ) (defect : ℝ) :
    underCredit defect ≤ cornerCredit n defect := by
  dsimp [underCredit, cornerCredit]
  have h := potential_antitone_threshold cap defect (threshold n) eta4
    (threshold_le_eta4 n)
  nlinarith

theorem bank4
    (defect : Fin 4 → ℝ) (P : ℝ)
    (hdefect : ∀ i, 0 ≤ defect i)
    (hphase : 2 * Real.sqrt (4 + ∑ i, defect i) ≤ P) :
    (∑ i, cornerCredit 4 (defect i)) ≤
      ((17 : ℝ) / 80) * pos (P - line 4) := by
  have h := finite_corner_bank (Finset.univ : Finset (Fin 4)) defect
    cap eta4 4 (line 4) P
    (by simpa using hdefect) eta4_le_cap eta4_nonneg (by norm_num)
    (by rw [A4_eta4_sqrt]; nlinarith) (by simpa using denom4)
    (by simpa using hphase)
  simpa [cornerCredit, threshold] using h

theorem bank5
    (defect : Fin 5 → ℝ) (P : ℝ)
    (hdefect : ∀ i, 0 ≤ defect i)
    (hphase : 2 * Real.sqrt (A5 + ∑ i, defect i) ≤ P) :
    (∑ i, cornerCredit 5 (defect i)) ≤
      ((17 : ℝ) / 80) * pos (P - line 5) := by
  have h := finite_corner_bank (Finset.univ : Finset (Fin 5)) defect
    cap eta5 A5 (line 5) P
    (by simpa using hdefect) eta5_le_cap eta5_nonneg A5_pos.le
    (by rw [A5_eta5_sqrt]; nlinarith) (by simpa using denom5)
    (by simpa using hphase)
  simpa [cornerCredit, threshold] using h

theorem bank6
    (defect : Fin 6 → ℝ) (P : ℝ)
    (hdefect : ∀ i, 0 ≤ defect i)
    (hphase : 2 * Real.sqrt (A6 + ∑ i, defect i) ≤ P) :
    (∑ i, cornerCredit 6 (defect i)) ≤
      ((17 : ℝ) / 80) * pos (P - line 6) := by
  have h := finite_corner_bank (Finset.univ : Finset (Fin 6)) defect
    cap 0 A6 (line 6) P
    (by simpa using hdefect) cap_nonneg (by norm_num) A6_pos.le
    line6_base (by simpa using denom6) (by simpa using hphase)
  simpa [cornerCredit, threshold] using h

theorem bank7
    (defect : Fin 7 → ℝ) (P : ℝ)
    (hdefect : ∀ i, 0 ≤ defect i)
    (hphase : 2 * Real.sqrt (A7 + ∑ i, defect i) ≤ P) :
    (∑ i, cornerCredit 7 (defect i)) ≤
      ((17 : ℝ) / 80) * pos (P - line 7) := by
  have h := finite_corner_bank (Finset.univ : Finset (Fin 7)) defect
    cap 0 A7 (line 7) P
    (by simpa using hdefect) cap_nonneg (by norm_num) A7_pos.le
    line7_base (by simpa using denom7) (by simpa using hphase)
  simpa [cornerCredit, threshold] using h

theorem bank8
    (defect : Fin 8 → ℝ) (P : ℝ)
    (hdefect : ∀ i, 0 ≤ defect i)
    (hphase : 2 * Real.sqrt (A8 + ∑ i, defect i) ≤ P) :
    (∑ i, cornerCredit 8 (defect i)) ≤
      ((17 : ℝ) / 80) * pos (P - line 8) := by
  have h := finite_corner_bank (Finset.univ : Finset (Fin 8)) defect
    cap 0 A8 (line 8) P
    (by simpa using hdefect) cap_nonneg (by norm_num) A8_pos.le
    line8_base (by simpa using denom8) (by simpa using hphase)
  simpa [cornerCredit, threshold] using h

theorem bank9
    (defect : Fin 9 → ℝ) (P : ℝ)
    (hdefect : ∀ i, 0 ≤ defect i)
    (hphase : 2 * Real.sqrt (A8 + ∑ i, defect i) ≤ P) :
    (∑ i, cornerCredit 9 (defect i)) ≤
      ((17 : ℝ) / 80) * pos (P - line 9) := by
  have h := finite_corner_bank (Finset.univ : Finset (Fin 9)) defect
    cap 0 A8 (line 9) P
    (by simpa using hdefect) cap_nonneg (by norm_num) A8_pos.le
    line9_base (by simpa using denom9) (by simpa using hphase)
  simpa [cornerCredit, threshold] using h

end

end OctagonalCornerBank
