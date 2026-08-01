import Mathlib

set_option linter.unusedSectionVars false

/-!
# Finite capacity maps for selected-edge resource roles

A role is globally no-double-spending when it injects into a finite family of
resource slots. This module turns that geometric slot assignment into the exact
fiber-cardinality bounds used by the octagonal side/corner ledger.
-/

namespace RoleCapacityStandalone

noncomputable section

open scoped BigOperators

variable {Role Resource Slot : Type*}
variable [Fintype Role] [DecidableEq Role]
variable [Fintype Resource] [DecidableEq Resource]
variable [Fintype Slot] [DecidableEq Slot]

/-- Number of roles charged to one resource. -/
def fiberCount (resource : Role → Resource) (c : Resource) : ℕ :=
  ((Finset.univ : Finset Role).filter fun r => resource r = c).card

/-- Reindex any role sum by the number of roles charged to each resource. -/
theorem sum_eq_counted (resource : Role → Resource) (value : Resource → ℝ) :
    (∑ r : Role, value (resource r)) =
      ∑ c : Resource, (fiberCount resource c : ℝ) * value c := by
  classical
  calc
    (∑ r : Role, value (resource r)) =
        ∑ r : Role, ∑ c : Resource,
          if resource r = c then value c else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      simp
    _ = ∑ c : Resource, ∑ r : Role,
          if resource r = c then value c else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c : Resource, (fiberCount resource c : ℝ) * value c := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.sum_filter]
      simp [fiberCount]

/-- A role-to-slot injection whose slots are partitioned by resource and whose
per-resource slot counts are known exactly. -/
structure CapacityMap (Role Resource Slot : Type*)
    [Fintype Role] [DecidableEq Role]
    [Fintype Resource] [DecidableEq Resource]
    [Fintype Slot] [DecidableEq Slot] where
  resource : Role → Resource
  slotResource : Slot → Resource
  slot : Role → Slot
  slot_injective : Function.Injective slot
  slot_resource : ∀ r, slotResource (slot r) = resource r
  capacity : Resource → ℕ
  slot_count : ∀ c,
    ((Finset.univ : Finset Slot).filter fun s => slotResource s = c).card =
      capacity c

/-- Injecting roles into resource slots bounds every resource fiber by its
available capacity. -/
theorem fiberCount_le_capacity
    (M : CapacityMap Role Resource Slot) (c : Resource) :
    fiberCount M.resource c ≤ M.capacity c := by
  let roles : Finset Role :=
    (Finset.univ : Finset Role).filter fun r => M.resource r = c
  let slots : Finset Slot :=
    (Finset.univ : Finset Slot).filter fun s => M.slotResource s = c
  have hinj : Set.InjOn M.slot (↑roles : Set Role) := by
    intro a ha b hb hab
    exact M.slot_injective hab
  have hcard : (roles.image M.slot).card = roles.card :=
    Finset.card_image_of_injOn hinj
  have hsubset : roles.image M.slot ⊆ slots := by
    intro s hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    have hrc : M.resource r = c := by
      exact (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (M.slot_resource r).trans hrc⟩
  have hle : roles.card ≤ slots.card := by
    rw [← hcard]
    exact Finset.card_le_card hsubset
  have hslots : slots.card = M.capacity c := by
    exact M.slot_count c
  have hfinal : roles.card ≤ M.capacity c := by
    rw [← hslots]
    exact hle
  simpa [fiberCount, roles] using hfinal

/-- Capacity maps with two endpoint slots, one third-cell slot, and one
collision slot imply the weighted `1+1+3` or exclusive `5` corner budget. -/
theorem weighted_corner_budget
    {EndpointRole ThirdRole CollisionRole Corner EndpointSlot ThirdSlot CollisionSlot : Type*}
    [Fintype EndpointRole] [DecidableEq EndpointRole]
    [Fintype ThirdRole] [DecidableEq ThirdRole]
    [Fintype CollisionRole] [DecidableEq CollisionRole]
    [Fintype Corner] [DecidableEq Corner]
    [Fintype EndpointSlot] [DecidableEq EndpointSlot]
    [Fintype ThirdSlot] [DecidableEq ThirdSlot]
    [Fintype CollisionSlot] [DecidableEq CollisionSlot]
    (E : CapacityMap EndpointRole Corner EndpointSlot)
    (T : CapacityMap ThirdRole Corner ThirdSlot)
    (C : CapacityMap CollisionRole Corner CollisionSlot)
    (hE : ∀ k, E.capacity k = 2)
    (hT : ∀ k, T.capacity k = 1)
    (hC : ∀ k, C.capacity k = 1)
    (hexclusive : ∀ k, 0 < fiberCount C.resource k →
      fiberCount E.resource k = 0 ∧ fiberCount T.resource k = 0) :
    ∀ k,
      fiberCount E.resource k +
          3 * fiberCount T.resource k +
          5 * fiberCount C.resource k ≤ 5 := by
  intro k
  have he := fiberCount_le_capacity E k
  have ht := fiberCount_le_capacity T k
  have hc := fiberCount_le_capacity C k
  rw [hE k] at he
  rw [hT k] at ht
  rw [hC k] at hc
  by_cases hz : fiberCount C.resource k = 0
  · rw [hz]
    omega
  · have hp : 0 < fiberCount C.resource k := Nat.pos_of_ne_zero hz
    obtain ⟨he0, ht0⟩ := hexclusive k hp
    rw [he0, ht0]
    omega

end

end RoleCapacityStandalone
