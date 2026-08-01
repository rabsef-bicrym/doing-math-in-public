import PhaseSnappingSum

/-!
# Correct corner bank for cells with at least eight sides

For an `n`-gap fan the phase-snapping baseline is

  `A₈ - (n-8) cap`.

The corner bank is funded by two independent pieces of positive charge:

* the universal circumscribed-area bound gives `P ≥ p₈`, hence the affine
  reserve `p₈ - L(n)`;
* phase defect beyond `(n-8) cap` gives an additional square-root perimeter
  increment above `p₈`.

The proof does **not** assume that total phase defect is at least
`(n-8) cap`; that stronger statement is false for some large fans.  Instead it
splits according to whether the defect has reached that threshold.
-/

namespace LargeCellCornerBank

noncomputable section

open Real
open scoped BigOperators
open PairGapCore
open NoncrystallineDomainReduction
open ContinuousCornerBank
open OctagonalCornerBank
open PhaseSnappingSum

lemma per_extra_corner_credit_le_reserve :
    cap / 10 ≤ ((17 : ℝ) / 80) * slope := by
  nlinarith [cap_upper, slope_lower]

lemma line_le_p8_of_eight_le (n : ℕ) (hn : 8 ≤ n) :
    line n ≤ p8 := by
  have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [← sub_nonneg, p8_sub_line]
  exact mul_nonneg slope_pos.le (sub_nonneg.mpr hnR)

/-- Scalar corner bank for every `n ≥ 8`.  `D` is total phase defect and `S`
is total unscaled capped corner potential. -/
theorem bank_ge_eight_scalar
    (n : ℕ) (D S P : ℝ)
    (hn : 8 ≤ n)
    (_hD0 : 0 ≤ D)
    (_hS0 : 0 ≤ S)
    (hSD : S ≤ D)
    (hScap : S ≤ (n : ℝ) * cap)
    (huniversal : p8 ≤ P)
    (hphase : 2 * Real.sqrt (phaseBase n + D) ≤ P) :
    S / 10 ≤ ((17 : ℝ) / 80) * pos (P - line n) := by
  let q : ℝ := (n : ℝ) - 8
  have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hline := line_le_p8_of_eight_le n hn
  have hPL : 0 ≤ P - line n := by linarith
  have hpos : pos (P - line n) = P - line n :=
    pos_eq_self_of_nonneg hPL
  have hp8line : p8 - line n = slope * q := by
    have h := p8_sub_line n
    simpa [q] using h
  have hmandatoryPay :
      q * cap / 10 ≤ ((17 : ℝ) / 80) * (q * slope) := by
    have hmul := mul_le_mul_of_nonneg_left
      per_extra_corner_credit_le_reserve hq
    nlinarith
  by_cases hsmall : D ≤ q * cap
  · have hSsmall : S / 10 ≤ q * cap / 10 := by linarith
    rw [hpos]
    nlinarith
  · have hqcap : q * cap < D := lt_of_not_ge hsmall
    let z : ℝ := D - q * cap
    let w : ℝ := min z (8 * cap)
    have hz : 0 ≤ z := by dsimp [z]; linarith
    have hY : 0 ≤ 8 * cap := mul_nonneg (by norm_num) cap_nonneg
    have hw : 0 ≤ w := by dsimp [w]; exact le_min hz hY
    have hwz : w ≤ z := by dsimp [w]; exact min_le_left _ _
    have hwY : w ≤ 8 * cap := by dsimp [w]; exact min_le_right _ _
    have hSD' : S - q * cap ≤ z := by
      dsimp [z]
      linarith
    have hScap' : S - q * cap ≤ 8 * cap := by
      have hid : (n : ℝ) * cap = q * cap + 8 * cap := by
        dsimp [q]
        ring
      rw [hid] at hScap
      linarith
    have hSw : S - q * cap ≤ w := by
      dsimp [w]
      exact le_min hSD' hScap'
    have hSsplit : S ≤ q * cap + w := by linarith
    have hbase : phaseBase n + D = A8 + z := by
      dsimp [phaseBase, z, q]
      ring
    have hphase' : 2 * Real.sqrt (A8 + z) ≤ P := by
      rw [← hbase]
      exact hphase
    have hsqrt : Real.sqrt (A8 + w) ≤ Real.sqrt (A8 + z) := by
      apply Real.sqrt_le_sqrt
      linarith
    have hinc := sqrt_increment_lower A8 w (8 * cap)
      A8_pos.le hw hwY hY denom8
    have hextra : ((8 : ℝ) / 17) * w ≤ P - p8 := by
      dsimp [p8]
      nlinarith
    have hextraPay : w / 10 ≤ ((17 : ℝ) / 80) * (P - p8) := by
      nlinarith
    rw [hpos]
    nlinarith

/-- Applied form for a finite list of phase defects. -/
theorem bank_ge_eight
    (n : ℕ) (defect : Fin n → ℝ) (P : ℝ)
    (hn : 8 ≤ n)
    (hdefect : ∀ i, 0 ≤ defect i)
    (huniversal : p8 ≤ P)
    (hphase : 2 * Real.sqrt (phaseBase n + ∑ i, defect i) ≤ P) :
    (∑ i, cornerCredit n (defect i)) ≤
      ((17 : ℝ) / 80) * pos (P - line n) := by
  have h4 : n ≠ 4 := by omega
  have h5 : n ≠ 5 := by omega
  let D : ℝ := ∑ i, defect i
  let S : ℝ := ∑ i, potential cap 0 (defect i)
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun i hi => hdefect i
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i hi => potential_nonneg _ _ _
  have hSD : S ≤ D := by
    have hsum0 : 0 ≤ ∑ i, defect i :=
      Finset.sum_nonneg fun i hi => hdefect i
    have h := sum_potential_le_total (Finset.univ : Finset (Fin n))
      defect cap 0 (by simpa using hdefect) (by norm_num)
    have hpos : pos ((∑ i, defect i) - 0) = ∑ i, defect i := by
      simpa using pos_eq_self_of_nonneg hsum0
    dsimp [S, D]
    rw [hpos] at h
    exact h
  have hScap : S ≤ (n : ℝ) * cap := by
    have h := sum_potential_le_card_mul (Finset.univ : Finset (Fin n))
      defect cap 0 cap_nonneg
    dsimp [S] at h ⊢
    simpa using h
  have hbank := bank_ge_eight_scalar n D S P hn hD0 hS0 hSD hScap
    huniversal (by simpa [D] using hphase)
  have hsum : (∑ i, cornerCredit n (defect i)) = S / 10 := by
    dsimp [cornerCredit, S]
    simp [threshold, h4, h5, Finset.sum_div]
  rw [hsum]
  exact hbank

end

end LargeCellCornerBank
