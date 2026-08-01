import Mathlib

/-!
# One-edge lower bound for a closed polygonal chain

The sum of the norm-lengths of a closed polygonal chain is at least twice the
norm of any chosen edge. This is the abstract triangle-inequality input used
by the noncrystalline shared-edge cutoff.
-/

namespace ClosedPolygonEdgeBound

open scoped BigOperators

variable {E : Type*} [SeminormedAddCommGroup E]

/-- A closed finite polygonal chain has perimeter at least twice the norm of
any one of its edge vectors. -/
theorem perimeter_ge_two_edge
    {m : ℕ} (v : Fin m → E) (e : Fin m)
    (hclosed : ∑ i, v i = 0) :
    2 * ‖v e‖ ≤ ∑ i, ‖v i‖ := by
  classical
  have hdecomp : (∑ i ∈ (Finset.univ.erase e), v i) + v e = 0 := by
    calc
      (∑ i ∈ (Finset.univ.erase e), v i) + v e = ∑ i : Fin m, v i := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ e)]
      _ = 0 := hclosed
  have hrest : (∑ i ∈ (Finset.univ.erase e), v i) = -v e :=
    eq_neg_of_add_eq_zero_left hdecomp
  have hnorm : ‖v e‖ ≤ ∑ i ∈ (Finset.univ.erase e), ‖v i‖ := by
    calc
      ‖v e‖ = ‖-v e‖ := (norm_neg _).symm
      _ = ‖∑ i ∈ (Finset.univ.erase e), v i‖ := by rw [hrest]
      _ ≤ ∑ i ∈ (Finset.univ.erase e), ‖v i‖ := norm_sum_le _ _
  have hperim :
      (∑ i : Fin m, ‖v i‖) =
        (∑ i ∈ (Finset.univ.erase e), ‖v i‖) + ‖v e‖ := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ e)]
  rw [hperim]
  linarith

end ClosedPolygonEdgeBound
