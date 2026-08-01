import Mathlib

/-!
# Exact ear identity for splitting a tangent-fan gap

Inserting an intermediate supporting line splits one tangent-wedge contribution
into two.  The lost area is an explicit square.  This is the algebraic mechanism
that lets an arbitrary normal gap be subdivided at every octagonal sector
boundary without increasing the circumscribed tangent area.
-/

namespace WedgeSplitAlgebra

noncomputable section

/-- Tangent-wedge area written in terms of the sine and cosine of the gap. -/
def wedge (h₀ h₁ sn cs : ℝ) : ℝ :=
  h₀ * h₁ / sn - (h₀ ^ 2 + h₁ ^ 2) * cs / (2 * sn)

/-- The exact three-line ear identity.  The right side is the square of the
failure of the three support lines to be concurrent. -/
theorem wedge_split_identity
    (h₀ h₁ h₂ sA cA sB cB sC cC : ℝ)
    (hsA : sA ≠ 0) (hsB : sB ≠ 0) (hsC : sC ≠ 0)
    (hSin : sC = sA * cB + cA * sB)
    (hCos : cC = cA * cB - sA * sB)
    (hA : sA ^ 2 + cA ^ 2 = 1)
    (hB : sB ^ 2 + cB ^ 2 = 1) :
    2 * sA * sB * sC *
        (wedge h₀ h₂ sC cC - wedge h₀ h₁ sA cA - wedge h₁ h₂ sB cB) =
      (sC * h₁ - sB * h₀ - sA * h₂) ^ 2 := by
  have hcA : cA ^ 2 = 1 - sA ^ 2 := by nlinarith [hA]
  have hcB : cB ^ 2 = 1 - sB ^ 2 := by nlinarith [hB]
  have hsAB : sA * cB + cA * sB ≠ 0 := by
    rw [← hSin]
    exact hsC
  have hsAB' : sA * cB + sB * cA ≠ 0 := by
    simpa [mul_comm] using hsAB
  dsimp [wedge]
  rw [hSin, hCos]
  field_simp [hsA, hsB, hsAB, hsAB']
  ring_nf
  rw [hcA, hcB]
  ring

/-- For positive gaps summing to less than `π`, inserting the intermediate
support line cannot increase the sum of tangent-wedge contributions. -/
theorem wedge_split_le
    (h₀ h₁ h₂ sA cA sB cB sC cC : ℝ)
    (hsA : 0 < sA) (hsB : 0 < sB) (hsC : 0 < sC)
    (hSin : sC = sA * cB + cA * sB)
    (hCos : cC = cA * cB - sA * sB)
    (hA : sA ^ 2 + cA ^ 2 = 1)
    (hB : sB ^ 2 + cB ^ 2 = 1) :
    wedge h₀ h₁ sA cA + wedge h₁ h₂ sB cB ≤
      wedge h₀ h₂ sC cC := by
  have hid := wedge_split_identity h₀ h₁ h₂ sA cA sB cB sC cC
    hsA.ne' hsB.ne' hsC.ne' hSin hCos hA hB
  have hcoef : 0 < 2 * sA * sB * sC := by positivity
  have hsq : 0 ≤ (sC * h₁ - sB * h₀ - sA * h₂) ^ 2 := sq_nonneg _
  nlinarith

/-- Trigonometric specialization of the ear inequality. -/
theorem wedge_split_trig
    (h₀ h₁ h₂ A B : ℝ)
    (hA : 0 < Real.sin A) (hB : 0 < Real.sin B)
    (hAB : 0 < Real.sin (A + B)) :
    wedge h₀ h₁ (Real.sin A) (Real.cos A) +
        wedge h₁ h₂ (Real.sin B) (Real.cos B) ≤
      wedge h₀ h₂ (Real.sin (A + B)) (Real.cos (A + B)) := by
  apply wedge_split_le h₀ h₁ h₂
  · exact hA
  · exact hB
  · exact hAB
  · exact Real.sin_add A B
  · exact Real.cos_add A B
  · nlinarith [Real.sin_sq_add_cos_sq A]
  · nlinarith [Real.sin_sq_add_cos_sq B]

end

end WedgeSplitAlgebra
