import ContinuousChargeAccounting

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Analytic core of the continuous corner bank

This module turns a phase-snapping lower bound into the `17/80` corner-bank
inequality.  It is independent of the octagonal constants except for the final
numerical denominator `17/4`.

For a corner defect `δ`, cap `c`, and activation threshold `t`, the unscaled
corner potential is

  `max 0 (min δ c - t)`.

The finite-sum lemmas show that the total potential is bounded both by
`max 0 (D-t)`, where `D` is the total phase defect, and by `N(c-t)`.  A
rationalized square-root estimate then proves that one tenth of this potential
fits inside `17/80` of the positive net cell charge.
-/

namespace ContinuousCornerBank

noncomputable section

open Real
open scoped BigOperators

/-- Positive part. -/
def pos (x : ℝ) : ℝ := max 0 x

/-- Unscaled corner potential.  The actual credit is one tenth of this value. -/
def potential (cap threshold defect : ℝ) : ℝ :=
  pos (min defect cap - threshold)

lemma pos_nonneg (x : ℝ) : 0 ≤ pos x := by
  simp [pos]

lemma le_pos (x : ℝ) : x ≤ pos x := by
  simp [pos]

lemma pos_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : pos x = 0 := by
  simp [pos, max_eq_left hx]

lemma pos_eq_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : pos x = x := by
  simp [pos, max_eq_right hx]

/-- Combining two nonnegative defect masses pays the threshold at most once. -/
lemma pos_sub_add_le
    (a b threshold : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ threshold) :
    pos (a - threshold) + pos (b - threshold) ≤
      pos (a + b - threshold) := by
  by_cases hat : a ≤ threshold
  · have ha0 : a - threshold ≤ 0 := sub_nonpos.mpr hat
    rw [pos_eq_zero_of_nonpos ha0, zero_add]
    apply max_le_max_left
    linarith
  · have hat' : threshold < a := lt_of_not_ge hat
    by_cases hbt : b ≤ threshold
    · have hb0 : b - threshold ≤ 0 := sub_nonpos.mpr hbt
      rw [pos_eq_zero_of_nonpos hb0, add_zero]
      apply max_le_max_left
      linarith
    · have hbt' : threshold < b := lt_of_not_ge hbt
      have ha1 : 0 ≤ a - threshold := by linarith
      have hb1 : 0 ≤ b - threshold := by linarith
      have hab1 : 0 ≤ a + b - threshold := by linarith
      rw [pos_eq_self_of_nonneg ha1, pos_eq_self_of_nonneg hb1,
        pos_eq_self_of_nonneg hab1]
      linarith

/-- Sum of activated defects is at most the positive part of total defect minus
one activation threshold. -/
theorem sum_pos_sub_le
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (threshold : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ht : 0 ≤ threshold) :
    (∑ i ∈ s, pos (a i - threshold)) ≤
      pos ((∑ i ∈ s, a i) - threshold) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [pos, max_eq_left (neg_nonpos.mpr ht)]
  | @insert x s hx ih =>
      have hax : 0 ≤ a x := ha x (by simp)
      have has : ∀ i ∈ s, 0 ≤ a i := by
        intro i hi
        exact ha i (by simp [hi])
      have hsum : 0 ≤ ∑ i ∈ s, a i :=
        Finset.sum_nonneg fun i hi => has i hi
      calc
        (∑ i ∈ insert x s, pos (a i - threshold)) =
            pos (a x - threshold) + ∑ i ∈ s, pos (a i - threshold) := by
          simp [hx]
        _ ≤ pos (a x - threshold) +
              pos ((∑ i ∈ s, a i) - threshold) := by
          linarith [ih has]
        _ ≤ pos (a x + (∑ i ∈ s, a i) - threshold) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            pos_sub_add_le (a x) (∑ i ∈ s, a i) threshold hax hsum ht
        _ = pos ((∑ i ∈ insert x s, a i) - threshold) := by
          simp [hx]

lemma potential_nonneg (cap threshold defect : ℝ) :
    0 ≤ potential cap threshold defect :=
  pos_nonneg _

lemma potential_le_pos_defect
    (cap threshold defect : ℝ) :
    potential cap threshold defect ≤ pos (defect - threshold) := by
  dsimp [potential]
  apply max_le_max_left
  exact sub_le_sub_right (min_le_left defect cap) threshold

lemma potential_le_cap
    (cap threshold defect : ℝ) :
    potential cap threshold defect ≤ pos (cap - threshold) := by
  dsimp [potential]
  apply max_le_max_left
  exact sub_le_sub_right (min_le_right defect cap) threshold

lemma potential_antitone_threshold
    (cap defect t₁ t₂ : ℝ) (ht : t₁ ≤ t₂) :
    potential cap t₂ defect ≤ potential cap t₁ defect := by
  dsimp [potential]
  apply max_le_max_left
  linarith

/-- Total corner potential is bounded by total defect minus one threshold. -/
theorem sum_potential_le_total
    {ι : Type*} (s : Finset ι) (defect : ι → ℝ)
    (cap threshold : ℝ)
    (hdefect : ∀ i ∈ s, 0 ≤ defect i)
    (hthreshold : 0 ≤ threshold) :
    (∑ i ∈ s, potential cap threshold (defect i)) ≤
      pos ((∑ i ∈ s, defect i) - threshold) := by
  calc
    (∑ i ∈ s, potential cap threshold (defect i)) ≤
        ∑ i ∈ s, pos (defect i - threshold) := by
      apply Finset.sum_le_sum
      intro i hi
      exact potential_le_pos_defect cap threshold (defect i)
    _ ≤ pos ((∑ i ∈ s, defect i) - threshold) :=
      sum_pos_sub_le s defect threshold hdefect hthreshold

/-- Total corner potential is also bounded by the number of corners times the
per-corner cap. -/
theorem sum_potential_le_card_mul
    {ι : Type*} (s : Finset ι) (defect : ι → ℝ)
    (cap threshold : ℝ) (hthreshold_cap : threshold ≤ cap) :
    (∑ i ∈ s, potential cap threshold (defect i)) ≤
      s.card * (cap - threshold) := by
  have hcap : pos (cap - threshold) = cap - threshold :=
    pos_eq_self_of_nonneg (sub_nonneg.mpr hthreshold_cap)
  calc
    (∑ i ∈ s, potential cap threshold (defect i)) ≤
        ∑ _i ∈ s, pos (cap - threshold) := by
      apply Finset.sum_le_sum
      intro i hi
      exact potential_le_cap cap threshold (defect i)
    _ = s.card * (cap - threshold) := by
      rw [hcap]
      simp
      ring

/-- Rationalized square-root increment.  The constant `17/4` is chosen so that
multiplication by `17/80` pays one tenth of the defect mass. -/
theorem sqrt_increment_lower
    (F z Y : ℝ)
    (hF : 0 ≤ F) (hz : 0 ≤ z) (hzY : z ≤ Y)
    (hY : 0 ≤ Y)
    (hden : Real.sqrt (F + Y) + Real.sqrt F ≤ (17 : ℝ) / 4) :
    ((8 : ℝ) / 17) * z ≤
      2 * Real.sqrt (F + z) - 2 * Real.sqrt F := by
  have hFz : 0 ≤ F + z := by linarith
  have hFY : 0 ≤ F + Y := by linarith
  have hsqrt_le : Real.sqrt (F + z) ≤ Real.sqrt (F + Y) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hsum :
      Real.sqrt (F + z) + Real.sqrt F ≤ (17 : ℝ) / 4 := by
    nlinarith [hsqrt_le, hden]
  have hdiff : 0 ≤ Real.sqrt (F + z) - Real.sqrt F := by
    have := Real.sqrt_le_sqrt (show F ≤ F + z by linarith)
    linarith
  have hsqF : (Real.sqrt F) ^ 2 = F := Real.sq_sqrt hF
  have hsqFz : (Real.sqrt (F + z)) ^ 2 = F + z :=
    Real.sq_sqrt hFz
  have hid :
      (Real.sqrt (F + z) - Real.sqrt F) *
          (Real.sqrt (F + z) + Real.sqrt F) = z := by
    nlinarith
  have hprod :
      z ≤ (Real.sqrt (F + z) - Real.sqrt F) * ((17 : ℝ) / 4) := by
    calc
      z = (Real.sqrt (F + z) - Real.sqrt F) *
          (Real.sqrt (F + z) + Real.sqrt F) := hid.symm
      _ ≤ (Real.sqrt (F + z) - Real.sqrt F) * ((17 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hsum hdiff
  nlinarith

/-- Scalar corner-bank theorem.  `S` is total unscaled potential, `D` total
phase defect, and `Y` the saturated potential cap. -/
theorem scalar_corner_bank
    (A threshold D Y L P S : ℝ)
    (hA : 0 ≤ A)
    (hthreshold : 0 ≤ threshold)
    (hD : 0 ≤ D)
    (hY : 0 ≤ Y)
    (hS0 : 0 ≤ S)
    (hStotal : S ≤ pos (D - threshold))
    (hScap : S ≤ Y)
    (hL : L ≤ 2 * Real.sqrt (A + threshold))
    (hden : Real.sqrt (A + threshold + Y) +
        Real.sqrt (A + threshold) ≤ (17 : ℝ) / 4)
    (hP : 2 * Real.sqrt (A + D) ≤ P) :
    S / 10 ≤ ((17 : ℝ) / 80) * pos (P - L) := by
  by_cases hDt : D ≤ threshold
  · have hpos0 : pos (D - threshold) = 0 :=
      pos_eq_zero_of_nonpos (sub_nonpos.mpr hDt)
    have hS : S = 0 := by
      rw [hpos0] at hStotal
      linarith
    have hp : 0 ≤ ((17 : ℝ) / 80) * pos (P - L) :=
      mul_nonneg (by norm_num) (pos_nonneg _)
    simpa [hS] using hp
  · have htD : threshold ≤ D := le_of_not_ge hDt
    let y : ℝ := D - threshold
    let z : ℝ := min y Y
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hz : 0 ≤ z := by
      dsimp [z]
      exact le_min hy hY
    have hzY : z ≤ Y := min_le_right _ _
    have hzy : z ≤ y := min_le_left _ _
    have hSle : S ≤ z := by
      have hposy : pos (D - threshold) = y := by
        dsimp [y]
        exact pos_eq_self_of_nonneg hy
      rw [hposy] at hStotal
      exact le_min hStotal hScap
    have hF : 0 ≤ A + threshold := by linarith
    have hinc := sqrt_increment_lower (A + threshold) z Y hF hz hzY hY hden
    have hAD : A + threshold + z ≤ A + D := by
      dsimp [y] at hzy
      linarith
    have hsqrt :
        Real.sqrt (A + threshold + z) ≤ Real.sqrt (A + D) :=
      Real.sqrt_le_sqrt hAD
    have hreserve : ((8 : ℝ) / 17) * z ≤ P - L := by
      calc
        ((8 : ℝ) / 17) * z ≤
            2 * Real.sqrt (A + threshold + z) -
              2 * Real.sqrt (A + threshold) := hinc
        _ ≤ 2 * Real.sqrt (A + D) - L := by
          nlinarith
        _ ≤ P - L := by linarith
    have hPL : 0 ≤ P - L := by
      have hz0 : 0 ≤ ((8 : ℝ) / 17) * z := by positivity
      linarith
    have hposPL : pos (P - L) = P - L :=
      pos_eq_self_of_nonneg hPL
    rw [hposPL]
    nlinarith

/-- Finite-cell corner bank, conditional only on the phase-snapping perimeter
lower bound and the explicit square-root denominator check. -/
theorem finite_corner_bank
    {ι : Type*} (corners : Finset ι) (defect : ι → ℝ)
    (cap threshold A L P : ℝ)
    (hdefect : ∀ i ∈ corners, 0 ≤ defect i)
    (hcap : threshold ≤ cap)
    (hthreshold : 0 ≤ threshold)
    (hA : 0 ≤ A)
    (hL : L ≤ 2 * Real.sqrt (A + threshold))
    (hden : Real.sqrt
          (A + threshold + corners.card * (cap - threshold)) +
        Real.sqrt (A + threshold) ≤ (17 : ℝ) / 4)
    (hphase :
      2 * Real.sqrt (A + ∑ i ∈ corners, defect i) ≤ P) :
    (∑ i ∈ corners, potential cap threshold (defect i) / 10) ≤
      ((17 : ℝ) / 80) * pos (P - L) := by
  let D : ℝ := ∑ i ∈ corners, defect i
  let S : ℝ := ∑ i ∈ corners, potential cap threshold (defect i)
  let Y : ℝ := corners.card * (cap - threshold)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun i hi => hdefect i hi
  have hY : 0 ≤ Y := by
    dsimp [Y]
    have hc : 0 ≤ cap - threshold := sub_nonneg.mpr hcap
    positivity
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i hi => potential_nonneg _ _ _
  have hStotal : S ≤ pos (D - threshold) := by
    dsimp [S, D]
    exact sum_potential_le_total corners defect cap threshold hdefect hthreshold
  have hScap : S ≤ Y := by
    dsimp [S, Y]
    exact sum_potential_le_card_mul corners defect cap threshold hcap
  have hscalar := scalar_corner_bank A threshold D Y L P S hA hthreshold
    hD hY hS0 hStotal hScap hL (by simpa [D, S, Y] using hden)
    (by simpa [D] using hphase)
  have hsumdiv :
      (∑ i ∈ corners, potential cap threshold (defect i) / 10) = S / 10 := by
    dsimp [S]
    rw [Finset.sum_div]
  rw [hsumdiv]
  exact hscalar

end

end ContinuousCornerBank
