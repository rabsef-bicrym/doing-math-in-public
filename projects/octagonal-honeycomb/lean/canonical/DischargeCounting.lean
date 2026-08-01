import PairGapTheorem

/-!
# Selected-edge double counting

This file formalizes the combinatorial ledger used after the pair-gap lemma.
Each selected edge contributes excess from its two incident cells. If each cell
is incident to at most eight selected edges, the total selected-edge charge is
at most eight times the total cell excess.
-/

namespace DischargeCounting

noncomputable section

open scoped BigOperators

variable {Cell Edge : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype Edge]

/-- Number of selected edges using `c` as a specified endpoint. -/
def endpointCount (endpoint : Edge → Cell) (c : Cell) : ℕ :=
  ((Finset.univ : Finset Edge).filter fun e => endpoint e = c).card

/-- Total endpoint multiplicity of a cell among the selected edges. -/
def incidenceCount (left right : Edge → Cell) (c : Cell) : ℕ :=
  endpointCount left c + endpointCount right c

/-- Re-index an endpoint sum by the endpoint fibers. -/
lemma endpoint_sum_eq_counted
    (endpoint : Edge → Cell) (excess : Cell → ℝ) :
    (∑ e : Edge, excess (endpoint e)) =
      ∑ c : Cell, (endpointCount endpoint c : ℝ) * excess c := by
  classical
  calc
    (∑ e : Edge, excess (endpoint e)) =
        ∑ c : Cell,
          ∑ e ∈ (Finset.univ : Finset Edge) with endpoint e = c, excess c := by
      symm
      simpa using
        (Finset.sum_fiberwise'
          (s := (Finset.univ : Finset Edge)) endpoint excess)
    _ = ∑ c : Cell, (endpointCount endpoint c : ℝ) * excess c := by
      apply Finset.sum_congr rfl
      intro c hc
      simp [endpointCount, nsmul_eq_mul]

/-- The sum of the two endpoint excesses equals the incidence-weighted cell
sum. No injectivity or simplicity assumption on the endpoint maps is needed. -/
theorem endpoint_pair_sum_eq_incidence
    (left right : Edge → Cell) (excess : Cell → ℝ) :
    (∑ e : Edge, (excess (left e) + excess (right e))) =
      ∑ c : Cell, (incidenceCount left right c : ℝ) * excess c := by
  classical
  rw [Finset.sum_add_distrib,
    endpoint_sum_eq_counted left excess,
    endpoint_sum_eq_counted right excess,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  simp [incidenceCount, endpointCount]
  ring

/-- If every cell is used at most eight times, endpoint charge is bounded by
eight times total excess. -/
theorem endpoint_pair_sum_le_eight
    (left right : Edge → Cell) (excess : Cell → ℝ)
    (hexcess : ∀ c, 0 ≤ excess c)
    (hinc : ∀ c, incidenceCount left right c ≤ 8) :
    (∑ e : Edge, (excess (left e) + excess (right e))) ≤
      8 * ∑ c : Cell, excess c := by
  rw [endpoint_pair_sum_eq_incidence left right excess]
  calc
    (∑ c : Cell, (incidenceCount left right c : ℝ) * excess c) ≤
        ∑ c : Cell, 8 * excess c := by
      apply Finset.sum_le_sum
      intro c hc
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hinc c
      · exact hexcess c
    _ = 8 * ∑ c : Cell, excess c := by
      rw [Finset.mul_sum]

/-- Pointwise pair gaps yield the global `0.101 N ≤ 8 E` estimate. -/
theorem selected_edges_global_bound
    (left right : Edge → Cell) (excess : Cell → ℝ)
    (hexcess : ∀ c, 0 ≤ excess c)
    (hinc : ∀ c, incidenceCount left right c ≤ 8)
    (hpair : ∀ e, (101 : ℝ) / 1000 ≤
      excess (left e) + excess (right e)) :
    ((101 : ℝ) / 1000) * Fintype.card Edge ≤
      8 * ∑ c : Cell, excess c := by
  have hpoint :
      (∑ e : Edge, (101 : ℝ) / 1000) ≤
        ∑ e : Edge, (excess (left e) + excess (right e)) := by
    apply Finset.sum_le_sum
    intro e he
    exact hpair e
  have hcount :
      (∑ e : Edge, (101 : ℝ) / 1000) =
        ((101 : ℝ) / 1000) * Fintype.card Edge := by
    simp
    ring
  have hend := endpoint_pair_sum_le_eight left right excess hexcess hinc
  rw [hcount] at hpoint
  linarith

/-- The `0.101` pair gap with multiplicity eight pays any debt bounded by
`0.009` per selected dangerous cell. -/
theorem point_one_zero_one_pays_point_zero_zero_nine
    (N totalExcess : ℝ) (hN : 0 ≤ N)
    (hselected : ((101 : ℝ) / 1000) * N ≤ 8 * totalExcess) :
    ((9 : ℝ) / 1000) * N ≤ totalExcess := by
  nlinarith

/-- Strict payment whenever at least one dangerous cell is present. -/
theorem point_one_zero_one_strictly_pays_point_zero_zero_nine
    (N totalExcess : ℝ) (hN : 0 < N)
    (hselected : ((101 : ℝ) / 1000) * N ≤ 8 * totalExcess) :
    ((9 : ℝ) / 1000) * N < totalExcess := by
  nlinarith

end

end DischargeCounting
