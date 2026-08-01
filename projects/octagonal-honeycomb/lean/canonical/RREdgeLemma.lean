import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact algebraic core of the crystalline RR-edge lemma

This file replaces the mixed-area/Hodge-index proof of Lemma 3 in the
accompanying note by an elementary coordinate proof.

After a rigid motion, the distinguished RR edge is the east-pointing segment
of length `x`.  The two adjacent edges point north and south.  The remaining
possible crystalline directions, in cyclic order, are NW, W, SW.  Write their
lengths as `a`, `b`, `c`, and write the first northward length as `r`.
Closure eliminates `b` and the final southward length.  With `s = sqrt 2`:

  P = 2x + 2r + a + (1-s)c,
  A = rx + (s/2)ax - (a^2+c^2)/4.

For each of the seven nonempty subsets of {NW,W,SW}, the deficit

  D = 2Px - f x^2 - 4A

is zero, a square, or a sum of two squares.  The final theorem says that if
A=1, then 4 <= 2Px - f x^2, which is exactly the RR-edge inequality.
-/

namespace RREdgeLemma

noncomputable section

/-- Perimeter in the coordinate normal form. -/
def perimeter (s x r a c : ℝ) : ℝ :=
  2 * x + 2 * r + a + (1 - s) * c

/-- Euclidean area in the coordinate normal form. -/
def area (s x r a c : ℝ) : ℝ :=
  r * x + (s / 2) * a * x - (a ^ 2 + c ^ 2) / 4

/-- The homogeneous RR-edge deficit. -/
def deficit (s f x r a c : ℝ) : ℝ :=
  2 * perimeter s x r a c * x - f * x ^ 2 - 4 * area s x r a c

/-- Optional direction pattern for the upper chain of the polygon. -/
inductive Pattern where
  | w
  | nw
  | sw
  | nw_w
  | w_sw
  | nw_sw
  | all
  deriving DecidableEq, Repr

/-- Circumscribed-fan area for each pattern, with `s = sqrt 2`. -/
def fanArea (s : ℝ) : Pattern → ℝ
  | .w => 4
  | .nw => 2 + 2 * s
  | .sw => 2 + 2 * s
  | .nw_w => 1 + 2 * s
  | .w_sw => 1 + 2 * s
  | .nw_sw => 1 + 2 * s
  | .all => 4 * s - 2

/-- The coordinate constraints imposed when a direction is absent. -/
def Admissible (s x a c : ℝ) : Pattern → Prop
  | .w => a = 0 ∧ c = 0
  | .nw => a = s * x ∧ c = 0
  | .sw => a = 0 ∧ c = s * x
  | .nw_w => c = 0
  | .w_sw => a = 0
  | .nw_sw => c = s * x - a
  | .all => True

lemma w_identity (s x r : ℝ) :
    deficit s (fanArea s .w) x r 0 0 = 0 := by
  simp [deficit, fanArea, perimeter, area]
  ring

lemma nw_identity (s x r : ℝ) (hs : s ^ 2 = 2) :
    deficit s (fanArea s .nw) x r (s * x) 0 = 0 := by
  simp [deficit, fanArea, perimeter, area]
  nlinarith

lemma sw_identity (s x r : ℝ) (hs : s ^ 2 = 2) :
    deficit s (fanArea s .sw) x r 0 (s * x) = 0 := by
  simp [deficit, fanArea, perimeter, area]
  nlinarith

lemma nw_w_identity (s x r a : ℝ) (hs : s ^ 2 = 2) :
    deficit s (fanArea s .nw_w) x r a 0 =
      (a - (s - 1) * x) ^ 2 := by
  simp [deficit, fanArea, perimeter, area]
  nlinarith

lemma w_sw_identity (s x r c : ℝ) (hs : s ^ 2 = 2) :
    deficit s (fanArea s .w_sw) x r 0 c =
      (c - (s - 1) * x) ^ 2 := by
  simp [deficit, fanArea, perimeter, area]
  nlinarith

lemma nw_sw_identity (s x r a : ℝ) (hs : s ^ 2 = 2) :
    deficit s (fanArea s .nw_sw) x r a (s * x - a) =
      (a - (s * x - a)) ^ 2 / 2 := by
  simp [deficit, fanArea, perimeter, area]
  nlinarith

lemma all_identity (s x r a c : ℝ) (hs : s ^ 2 = 2) :
    deficit s (fanArea s .all) x r a c =
      (a - (s - 1) * x) ^ 2 + (c - (s - 1) * x) ^ 2 := by
  simp [deficit, fanArea, perimeter, area]
  nlinarith

/-- The seven exact identities imply nonnegativity of the RR deficit. -/
theorem deficit_nonneg
    (s x r a c : ℝ) (p : Pattern)
    (hs : s ^ 2 = 2) (hadm : Admissible s x a c p) :
    0 ≤ deficit s (fanArea s p) x r a c := by
  cases p with
  | w =>
      have h : a = 0 ∧ c = 0 := by simpa [Admissible] using hadm
      rcases h with ⟨rfl, rfl⟩
      rw [w_identity]
  | nw =>
      have h : a = s * x ∧ c = 0 := by simpa [Admissible] using hadm
      rcases h with ⟨rfl, rfl⟩
      rw [nw_identity s x r hs]
  | sw =>
      have h : a = 0 ∧ c = s * x := by simpa [Admissible] using hadm
      rcases h with ⟨rfl, rfl⟩
      rw [sw_identity s x r hs]
  | nw_w =>
      have hc : c = 0 := by simpa [Admissible] using hadm
      subst c
      rw [nw_w_identity s x r a hs]
      positivity
  | w_sw =>
      have ha : a = 0 := by simpa [Admissible] using hadm
      subst a
      rw [w_sw_identity s x r c hs]
      positivity
  | nw_sw =>
      have hc : c = s * x - a := by simpa [Admissible] using hadm
      subst c
      rw [nw_sw_identity s x r a hs]
      positivity
  | all =>
      rw [all_identity s x r a c hs]
      positivity

/-- Lemma 3, conditional only on the elementary coordinate normal form. -/
theorem rr_edge_inequality
    (s x r a c : ℝ) (p : Pattern)
    (hs : s ^ 2 = 2)
    (hadm : Admissible s x a c p)
    (harea : area s x r a c = 1) :
    4 ≤ 2 * perimeter s x r a c * x - fanArea s p * x ^ 2 := by
  have h := deficit_nonneg s x r a c p hs hadm
  unfold deficit at h
  rw [harea] at h
  linarith

end

end RREdgeLemma
