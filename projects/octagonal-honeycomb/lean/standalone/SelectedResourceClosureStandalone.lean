import CapacityBankStandalone
import CollisionDebtGroupingStandalone
import SelectedChargeLedgerStandalone

set_option linter.unusedSectionVars false

/-!
# Finite closure from selected-edge local payments and resource capacities

This theorem combines the exact negative-owner partition, collision grouping,
and the globally funded `63/80` side plus `17/80` corner banks. The only
remaining local hypothesis is the aggregate of the ordinary-edge and
collision-edge inequalities; no global debt-partition or no-double-spending
inequality is assumed.
-/

namespace SelectedResourceClosureStandalone

noncomputable section

open scoped BigOperators
open RoleCapacityStandalone
open NegativeChargeSelectionStandalone
open CollisionDebtGroupingStandalone
open SelectedChargeLedgerStandalone
open CapacityBankStandalone

variable {Cell Edge SideRole SideSlot EndpointRole ThirdRole CollisionRole Corner
  EndpointSlot ThirdSlot CollisionSlot : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype SideRole] [DecidableEq SideRole]
variable [Fintype SideSlot] [DecidableEq SideSlot]
variable [Fintype EndpointRole] [DecidableEq EndpointRole]
variable [Fintype ThirdRole] [DecidableEq ThirdRole]
variable [Fintype CollisionRole] [DecidableEq CollisionRole]
variable [Fintype Corner] [DecidableEq Corner]
variable [Fintype EndpointSlot] [DecidableEq EndpointSlot]
variable [Fintype ThirdSlot] [DecidableEq ThirdSlot]
variable [Fintype CollisionSlot] [DecidableEq CollisionSlot]

/-- The complete finite resource-ledger closure. -/
theorem finite_charge_nonneg
    (charge : Cell → ℝ)
    (selection : Selection (Cell := Cell) (Edge := Edge) charge)
    (sideMap : CapacityMap SideRole Cell SideSlot)
    (endpointMap : CapacityMap EndpointRole Corner EndpointSlot)
    (thirdMap : CapacityMap ThirdRole Corner ThirdSlot)
    (collisionMap : CapacityMap CollisionRole Corner CollisionSlot)
    (sideCount : Cell → ℕ)
    (cornerCell : Corner → Cell) (credit : Corner → ℝ)
    (hcredit : ∀ k, 0 ≤ credit k)
    (hsideCapacity : ∀ c, sideMap.capacity c = sideCount c)
    (hsidePos : ∀ c, 0 < sideCount c)
    (hEndpointCapacity : ∀ k, endpointMap.capacity k = 2)
    (hThirdCapacity : ∀ k, thirdMap.capacity k = 1)
    (hCollisionCapacity : ∀ k, collisionMap.capacity k = 1)
    (hCollisionExclusive : ∀ k,
      0 < fiberCount collisionMap.resource k →
        fiberCount endpointMap.resource k = 0 ∧
          fiberCount thirdMap.resource k = 0)
    (hcornerBank : ∀ c,
      (∑ k ∈ (Finset.univ : Finset Corner) with cornerCell k = c, credit k) ≤
        ((17 : ℝ) / 80) * pos (charge c))
    (hlocal :
      (∑ c ∈ ordinaryCells selection, debt charge c) +
          (∑ e ∈ collisionEdges selection, collisionDebt selection e) ≤
        (∑ r : SideRole,
            sideShare sideCount charge (sideMap.resource r)) +
          ((1 : ℝ) / 5) *
            (∑ r : EndpointRole, credit (endpointMap.resource r)) +
          ((3 : ℝ) / 5) *
            (∑ r : ThirdRole, credit (thirdMap.resource r)) +
          (∑ r : CollisionRole, credit (collisionMap.resource r))) :
    0 ≤ ∑ c : Cell, charge c := by
  have hfunded := globally_safe_resource_use sideMap endpointMap thirdMap
    collisionMap sideCount charge cornerCell credit hcredit hsideCapacity
    hsidePos hEndpointCapacity hThirdCapacity hCollisionCapacity
    hCollisionExclusive hcornerBank
  have hneg := total_negative_partition selection
  have hgroup := collision_debt_grouped selection
  have hpaid :
      (∑ c : Cell, pos (-charge c)) ≤ ∑ c : Cell, pos (charge c) := by
    rw [hneg, hgroup]
    exact le_trans hlocal hfunded
  rw [sum_charge_identity]
  linarith

end

end SelectedResourceClosureStandalone
