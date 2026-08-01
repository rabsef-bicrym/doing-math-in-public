import Mathlib

/-!
# Partitioning selected owners into ordinary edges and collisions

Each negative owner chooses one physical edge. A physical edge has only two
sides, so it can be chosen by at most two owners. This module derives, rather
than assumes, the exact partition of the owner debt into singleton selected
edges and two-owner collision edges.
-/

namespace SelectedEdgePartitionStandalone

noncomputable section

open scoped BigOperators

variable {Owner Edge : Type*}
variable [Fintype Owner] [DecidableEq Owner]
variable [Fintype Edge] [DecidableEq Edge]

structure Selection (Owner Edge : Type*) [Fintype Owner] [DecidableEq Owner]
    [Fintype Edge] [DecidableEq Edge] where
  edge : Owner → Edge
  fiber_le_two : ∀ e,
    ((Finset.univ : Finset Owner).filter fun o => edge o = e).card ≤ 2

variable (S : Selection Owner Edge)

def fiber (e : Edge) : Finset Owner :=
  (Finset.univ : Finset Owner).filter fun o => S.edge o = e

def fiberCount (e : Edge) : ℕ := (fiber S e).card

def ordinaryOwners : Finset Owner :=
  (Finset.univ : Finset Owner).filter fun o => fiberCount S (S.edge o) = 1

def collisionOwners : Finset Owner :=
  (Finset.univ : Finset Owner).filter fun o => fiberCount S (S.edge o) = 2

def collisionEdges : Finset Edge :=
  (Finset.univ : Finset Edge).filter fun e => fiberCount S e = 2

lemma mem_fiber_self (o : Owner) : o ∈ fiber S (S.edge o) := by
  simp [fiber]

lemma owner_fiber_pos (o : Owner) : 0 < fiberCount S (S.edge o) := by
  rw [fiberCount, Finset.card_pos]
  exact ⟨o, mem_fiber_self S o⟩

lemma owner_fiber_one_or_two (o : Owner) :
    fiberCount S (S.edge o) = 1 ∨ fiberCount S (S.edge o) = 2 := by
  have hp := owner_fiber_pos S o
  have hle : fiberCount S (S.edge o) ≤ 2 := by
    simpa [fiberCount, fiber] using S.fiber_le_two (S.edge o)
  omega

lemma ordinary_union_collision :
    ordinaryOwners S ∪ collisionOwners S = Finset.univ := by
  ext o
  simp only [ordinaryOwners, collisionOwners, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro _
    trivial
  · intro _
    exact owner_fiber_one_or_two S o

lemma ordinary_disjoint_collision :
    Disjoint (ordinaryOwners S) (collisionOwners S) := by
  rw [Finset.disjoint_left]
  intro o ho hc
  have ho' := ho
  have hc' := hc
  change o ∈ (Finset.univ.filter fun x => fiberCount S (S.edge x) = 1) at ho'
  change o ∈ (Finset.univ.filter fun x => fiberCount S (S.edge x) = 2) at hc'
  have h1 := (Finset.mem_filter.mp ho').2
  have h2 := (Finset.mem_filter.mp hc').2
  omega

/-- Exact debt partition: every owner occurs once, either on a singleton edge
or as a member of a two-owner collision. -/
theorem sum_owner_partition (debt : Owner → ℝ) :
    (∑ o : Owner, debt o) =
      (∑ o ∈ ordinaryOwners S, debt o) +
        ∑ o ∈ collisionOwners S, debt o := by
  calc
    (∑ o : Owner, debt o) =
        ∑ o ∈ ordinaryOwners S ∪ collisionOwners S, debt o := by
      rw [ordinary_union_collision S]
    _ = (∑ o ∈ ordinaryOwners S, debt o) +
          ∑ o ∈ collisionOwners S, debt o :=
      Finset.sum_union (ordinary_disjoint_collision S)

/-- Distinct selected edges have disjoint owner fibers. -/
lemma fiber_disjoint_of_ne {e₁ e₂ : Edge} (hne : e₁ ≠ e₂) :
    Disjoint (fiber S e₁) (fiber S e₂) := by
  rw [Finset.disjoint_left]
  intro o h1 h2
  have he1 : S.edge o = e₁ := (Finset.mem_filter.mp h1).2
  have he2 : S.edge o = e₂ := (Finset.mem_filter.mp h2).2
  exact hne (he1.symm.trans he2)

/-- On ordinary owners, the selected physical-edge map is injective. -/
theorem ordinary_edge_injective :
    Function.Injective
      (fun o : {o : Owner // o ∈ ordinaryOwners S} => S.edge o.1) := by
  intro a b hab
  change S.edge a.1 = S.edge b.1 at hab
  have haCount : fiberCount S (S.edge a.1) = 1 := by
    have ha := a.property
    change a.1 ∈
      (Finset.univ.filter fun o => fiberCount S (S.edge o) = 1) at ha
    exact (Finset.mem_filter.mp ha).2
  have hbCount : fiberCount S (S.edge b.1) = 1 := by
    have hb := b.property
    change b.1 ∈
      (Finset.univ.filter fun o => fiberCount S (S.edge o) = 1) at hb
    exact (Finset.mem_filter.mp hb).2
  have hcard : (fiber S (S.edge a.1)).card = 1 := by
    exact haCount
  obtain ⟨o, ho⟩ := Finset.card_eq_one.mp hcard
  have haMem : a.1 ∈ fiber S (S.edge a.1) := mem_fiber_self S a.1
  have hbMem : b.1 ∈ fiber S (S.edge a.1) := by
    change b.1 ∈
      (Finset.univ.filter fun x => S.edge x = S.edge a.1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩
  rw [ho] at haMem hbMem
  have hae : a.1 = o := by simpa using haMem
  have hbe : b.1 = o := by simpa using hbMem
  exact Subtype.ext (hae.trans hbe.symm)

/-- Every edge recorded as a collision has exactly two selected owners. -/
theorem collision_edge_has_two
    {e : Edge} (he : e ∈ collisionEdges S) :
    (fiber S e).card = 2 := by
  have he' := he
  change e ∈ (Finset.univ.filter fun x => fiberCount S x = 2) at he'
  have hcount := (Finset.mem_filter.mp he').2
  exact hcount

end

end SelectedEdgePartitionStandalone
