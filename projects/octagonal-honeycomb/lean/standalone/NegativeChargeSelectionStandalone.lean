import Mathlib

set_option linter.unusedSectionVars false

/-!
# Negative charge as selected-owner debt

This module removes the abstract debt-partition hypothesis from the final
finite ledger. Negative cells are selected directly by the sign of their net
charge. Each negative cell chooses one physical edge, and each physical edge
has at most two selected owners. The total negative part therefore splits
exactly into ordinary singleton-edge debt and two-owner collision debt.
-/

namespace NegativeChargeSelectionStandalone

noncomputable section

open scoped BigOperators

variable {Cell Edge : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype Edge] [DecidableEq Edge]

/-- Positive part, written locally to keep this module dependency-free. -/
def pos (x : ℝ) : ℝ := max x 0

/-- Cells whose net charge is strictly negative. -/
def negativeCells (charge : Cell → ℝ) : Finset Cell :=
  (Finset.univ : Finset Cell).filter fun c => charge c < 0

/-- The debt carried by a negative cell. -/
def debt (charge : Cell → ℝ) (c : Cell) : ℝ := -charge c

lemma mem_negativeCells_iff (charge : Cell → ℝ) (c : Cell) :
    c ∈ negativeCells charge ↔ charge c < 0 := by
  simp [negativeCells]

lemma debt_pos_of_mem
    (charge : Cell → ℝ) {c : Cell} (hc : c ∈ negativeCells charge) :
    0 < debt charge c := by
  have hneg : charge c < 0 := (mem_negativeCells_iff charge c).1 hc
  dsimp [debt]
  linarith

lemma neg_part_pointwise (charge : Cell → ℝ) (c : Cell) :
    pos (-charge c) = if charge c < 0 then -charge c else 0 := by
  by_cases h : charge c < 0
  · have hn : 0 ≤ -charge c := by linarith
    simp [pos, h, max_eq_left hn]
  · have hc : 0 ≤ charge c := le_of_not_gt h
    have hn : -charge c ≤ 0 := neg_nonpos.mpr hc
    simp [pos, h, max_eq_right hn]

/-- The total negative part is exactly the debt sum over negative cells. -/
theorem total_negative_eq_filter (charge : Cell → ℝ) :
    (∑ c : Cell, pos (-charge c)) =
      ∑ c ∈ negativeCells charge, debt charge c := by
  classical
  rw [show (∑ c : Cell, pos (-charge c)) =
      ∑ c : Cell, if charge c < 0 then -charge c else 0 by
        apply Finset.sum_congr rfl
        intro c hc
        exact neg_part_pointwise charge c]
  rw [← Finset.sum_filter]
  rfl

/-- A selected-edge system on precisely the negative cells. -/
structure Selection (charge : Cell → ℝ) where
  edge : Cell → Edge
  fiber_le_two : ∀ e,
    ((negativeCells charge).filter fun c => edge c = e).card ≤ 2

variable {charge : Cell → ℝ} (S : Selection (Cell := Cell) (Edge := Edge) charge)

def fiber (e : Edge) : Finset Cell :=
  (negativeCells charge).filter fun c => S.edge c = e

def fiberCount (e : Edge) : ℕ := (fiber S e).card

def ordinaryCells : Finset Cell :=
  (negativeCells charge).filter fun c => fiberCount S (S.edge c) = 1

def collisionCells : Finset Cell :=
  (negativeCells charge).filter fun c => fiberCount S (S.edge c) = 2

def collisionEdges : Finset Edge :=
  (Finset.univ : Finset Edge).filter fun e => fiberCount S e = 2

lemma mem_fiber_self {c : Cell} (hc : c ∈ negativeCells charge) :
    c ∈ fiber S (S.edge c) := by
  exact Finset.mem_filter.mpr ⟨hc, rfl⟩

lemma selected_fiber_pos {c : Cell} (hc : c ∈ negativeCells charge) :
    0 < fiberCount S (S.edge c) := by
  rw [fiberCount, Finset.card_pos]
  exact ⟨c, mem_fiber_self S hc⟩

lemma selected_fiber_one_or_two {c : Cell} (hc : c ∈ negativeCells charge) :
    fiberCount S (S.edge c) = 1 ∨ fiberCount S (S.edge c) = 2 := by
  have hp := selected_fiber_pos S hc
  have hle : fiberCount S (S.edge c) ≤ 2 := by
    simpa [fiberCount, fiber] using S.fiber_le_two (S.edge c)
  omega

lemma ordinary_union_collision :
    ordinaryCells S ∪ collisionCells S = negativeCells charge := by
  ext c
  constructor
  · intro h
    rcases Finset.mem_union.mp h with ho | hc
    · exact (Finset.mem_filter.mp ho).1
    · exact (Finset.mem_filter.mp hc).1
  · intro hc
    rcases selected_fiber_one_or_two S hc with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc, h2⟩)

lemma ordinary_disjoint_collision :
    Disjoint (ordinaryCells S) (collisionCells S) := by
  rw [Finset.disjoint_left]
  intro c ho hc
  have h1 := (Finset.mem_filter.mp ho).2
  have h2 := (Finset.mem_filter.mp hc).2
  omega

/-- Exact finite debt partition, derived from charge signs and selected edges. -/
theorem total_negative_partition :
    (∑ c : Cell, pos (-charge c)) =
      (∑ c ∈ ordinaryCells S, debt charge c) +
        ∑ c ∈ collisionCells S, debt charge c := by
  rw [total_negative_eq_filter charge]
  calc
    (∑ c ∈ negativeCells charge, debt charge c) =
        ∑ c ∈ ordinaryCells S ∪ collisionCells S, debt charge c := by
      rw [ordinary_union_collision S]
    _ = (∑ c ∈ ordinaryCells S, debt charge c) +
          ∑ c ∈ collisionCells S, debt charge c :=
      Finset.sum_union (ordinary_disjoint_collision S)

/-- The selected edge is injective on ordinary negative cells. -/
theorem ordinary_edge_injective :
    Set.InjOn S.edge (↑(ordinaryCells S) : Set Cell) := by
  intro a ha b hb hab
  have ha' : a ∈ ordinaryCells S := ha
  have hb' : b ∈ ordinaryCells S := hb
  have haCount := (Finset.mem_filter.mp ha').2
  have hcard : (fiber S (S.edge a)).card = 1 := haCount
  obtain ⟨o, ho⟩ := Finset.card_eq_one.mp hcard
  have haMem : a ∈ fiber S (S.edge a) :=
    mem_fiber_self S (Finset.mem_filter.mp ha').1
  have hbMem : b ∈ fiber S (S.edge a) := by
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hb').1, hab.symm⟩
  rw [ho] at haMem hbMem
  have hae : a = o := by simpa using haMem
  have hbe : b = o := by simpa using hbMem
  exact hae.trans hbe.symm

/-- Every recorded collision edge has exactly two negative owners. -/
theorem collision_edge_has_two
    {e : Edge} (he : e ∈ collisionEdges S) :
    (fiber S e).card = 2 := by
  have he' := he
  change e ∈ (Finset.univ.filter fun x => fiberCount S x = 2) at he'
  exact (Finset.mem_filter.mp he').2

/-- Distinct collision edges have disjoint owner fibers. -/
theorem collision_fibers_disjoint
    {e₁ e₂ : Edge} (hne : e₁ ≠ e₂) :
    Disjoint (fiber S e₁) (fiber S e₂) := by
  rw [Finset.disjoint_left]
  intro c h1 h2
  have he1 := (Finset.mem_filter.mp h1).2
  have he2 := (Finset.mem_filter.mp h2).2
  exact hne (he1.symm.trans he2)

end

end NegativeChargeSelectionStandalone
