import RoleCapacityStandalone
import NegativeChargeSelectionStandalone

set_option linter.unusedSectionVars false

/-!
# Side and corner banks from finite resource capacities

This module converts geometric slot injections into the global no-double-
spending inequality used by the unrestricted octagonal ledger. The `63/80`
side bank and `17/80` corner bank are handled independently and then combined.
-/

namespace CapacityBankStandalone

noncomputable section

open scoped BigOperators
open RoleCapacityStandalone
open NegativeChargeSelectionStandalone

/-- Per-side allocation from a cell's `63/80` side bank. -/
def sideShare {Cell : Type*} (sideCount : Cell → ℕ)
    (charge : Cell → ℝ) (c : Cell) : ℝ :=
  ((63 : ℝ) / 80) * pos (charge c) / sideCount c

/-- An injective side-role placement into the genuine sides of each cell spends
at most the total `63/80` side bank. -/
theorem side_bank_safe
    {Role Cell Slot : Type*}
    [Fintype Role] [DecidableEq Role]
    [Fintype Cell] [DecidableEq Cell]
    [Fintype Slot] [DecidableEq Slot]
    (M : CapacityMap Role Cell Slot)
    (sideCount : Cell → ℕ) (charge : Cell → ℝ)
    (hcapacity : ∀ c, M.capacity c = sideCount c)
    (hside_pos : ∀ c, 0 < sideCount c) :
    (∑ r : Role, sideShare sideCount charge (M.resource r)) ≤
      ((63 : ℝ) / 80) * ∑ c : Cell, pos (charge c) := by
  rw [sum_eq_counted M.resource (sideShare sideCount charge)]
  calc
    (∑ c : Cell,
        (fiberCount M.resource c : ℝ) * sideShare sideCount charge c) ≤
        ∑ c : Cell, ((63 : ℝ) / 80) * pos (charge c) := by
      apply Finset.sum_le_sum
      intro c hc
      have hq : 0 < (sideCount c : ℝ) := by exact_mod_cast hside_pos c
      have hmNat := fiberCount_le_capacity M c
      rw [hcapacity c] at hmNat
      have hm : (fiberCount M.resource c : ℝ) ≤ sideCount c := by
        exact_mod_cast hmNat
      have hratio :
          (fiberCount M.resource c : ℝ) / sideCount c ≤ 1 :=
        (div_le_one hq).2 hm
      have hcharge : 0 ≤ pos (charge c) := le_max_right _ _
      calc
        (fiberCount M.resource c : ℝ) * sideShare sideCount charge c =
            ((63 : ℝ) / 80) *
              (((fiberCount M.resource c : ℝ) / sideCount c) *
                pos (charge c)) := by
          dsimp [sideShare]
          field_simp [ne_of_gt hq]
          ring
        _ ≤ ((63 : ℝ) / 80) * (1 * pos (charge c)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hratio hcharge
        _ = ((63 : ℝ) / 80) * pos (charge c) := by ring
    _ = ((63 : ℝ) / 80) * ∑ c : Cell, pos (charge c) := by
      rw [Finset.mul_sum]

/-- Endpoint roles cost `1/5`, third-cell roles cost `3/5`, and collision roles
cost the full corner credit. Slot capacities and collision exclusivity imply
that their combined use is at most the total corner-credit supply. -/
theorem corner_roles_safe
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
    (credit : Corner → ℝ) (hcredit : ∀ k, 0 ≤ credit k)
    (hE : ∀ k, E.capacity k = 2)
    (hT : ∀ k, T.capacity k = 1)
    (hC : ∀ k, C.capacity k = 1)
    (hexclusive : ∀ k, 0 < fiberCount C.resource k →
      fiberCount E.resource k = 0 ∧ fiberCount T.resource k = 0) :
    ((1 : ℝ) / 5) * (∑ r : EndpointRole, credit (E.resource r)) +
        ((3 : ℝ) / 5) * (∑ r : ThirdRole, credit (T.resource r)) +
        (∑ r : CollisionRole, credit (C.resource r)) ≤
      ∑ k : Corner, credit k := by
  rw [sum_eq_counted E.resource credit,
    sum_eq_counted T.resource credit,
    sum_eq_counted C.resource credit]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hnat := weighted_corner_budget E T C hE hT hC hexclusive k
  have hreal :
      (fiberCount E.resource k : ℝ) +
          3 * (fiberCount T.resource k : ℝ) +
          5 * (fiberCount C.resource k : ℝ) ≤ 5 := by
    exact_mod_cast hnat
  have hcoef :
      ((1 : ℝ) / 5) * (fiberCount E.resource k : ℝ) +
          ((3 : ℝ) / 5) * (fiberCount T.resource k : ℝ) +
          (fiberCount C.resource k : ℝ) ≤ 1 := by
    nlinarith
  calc
    ((1 : ℝ) / 5) *
          ((fiberCount E.resource k : ℝ) * credit k) +
        ((3 : ℝ) / 5) *
          ((fiberCount T.resource k : ℝ) * credit k) +
        (fiberCount C.resource k : ℝ) * credit k =
      (((1 : ℝ) / 5) * (fiberCount E.resource k : ℝ) +
          ((3 : ℝ) / 5) * (fiberCount T.resource k : ℝ) +
          (fiberCount C.resource k : ℝ)) * credit k := by ring
    _ ≤ 1 * credit k :=
      mul_le_mul_of_nonneg_right hcoef (hcredit k)
    _ = credit k := one_mul _

/-- Reindex corner credits by their owning cells and apply each cell's funded
`17/80` corner-bank bound. -/
theorem total_corner_credit_le
    {Corner Cell : Type*}
    [Fintype Corner] [DecidableEq Corner]
    [Fintype Cell] [DecidableEq Cell]
    (cornerCell : Corner → Cell) (credit : Corner → ℝ)
    (charge : Cell → ℝ)
    (hbank : ∀ c,
      (∑ k ∈ (Finset.univ : Finset Corner) with cornerCell k = c, credit k) ≤
        ((17 : ℝ) / 80) * pos (charge c)) :
    (∑ k : Corner, credit k) ≤
      ((17 : ℝ) / 80) * ∑ c : Cell, pos (charge c) := by
  classical
  calc
    (∑ k : Corner, credit k) =
        ∑ k : Corner, ∑ c : Cell,
          if cornerCell k = c then credit k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp
    _ = ∑ c : Cell, ∑ k : Corner,
          if cornerCell k = c then credit k else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c : Cell,
          ∑ k ∈ (Finset.univ : Finset Corner) with cornerCell k = c,
            credit k := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_filter]
    _ ≤ ∑ c : Cell, ((17 : ℝ) / 80) * pos (charge c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hbank c
    _ = ((17 : ℝ) / 80) * ∑ c : Cell, pos (charge c) := by
      rw [Finset.mul_sum]

/-- The side bank and all corner roles together spend no more than total
positive net charge. -/
theorem globally_safe_resource_use
    {SideRole Cell SideSlot EndpointRole ThirdRole CollisionRole Corner
      EndpointSlot ThirdSlot CollisionSlot : Type*}
    [Fintype SideRole] [DecidableEq SideRole]
    [Fintype Cell] [DecidableEq Cell]
    [Fintype SideSlot] [DecidableEq SideSlot]
    [Fintype EndpointRole] [DecidableEq EndpointRole]
    [Fintype ThirdRole] [DecidableEq ThirdRole]
    [Fintype CollisionRole] [DecidableEq CollisionRole]
    [Fintype Corner] [DecidableEq Corner]
    [Fintype EndpointSlot] [DecidableEq EndpointSlot]
    [Fintype ThirdSlot] [DecidableEq ThirdSlot]
    [Fintype CollisionSlot] [DecidableEq CollisionSlot]
    (S : CapacityMap SideRole Cell SideSlot)
    (E : CapacityMap EndpointRole Corner EndpointSlot)
    (T : CapacityMap ThirdRole Corner ThirdSlot)
    (C : CapacityMap CollisionRole Corner CollisionSlot)
    (sideCount : Cell → ℕ) (charge : Cell → ℝ)
    (cornerCell : Corner → Cell) (credit : Corner → ℝ)
    (hcredit : ∀ k, 0 ≤ credit k)
    (hsideCapacity : ∀ c, S.capacity c = sideCount c)
    (hsidePos : ∀ c, 0 < sideCount c)
    (hE : ∀ k, E.capacity k = 2)
    (hT : ∀ k, T.capacity k = 1)
    (hC : ∀ k, C.capacity k = 1)
    (hexclusive : ∀ k, 0 < fiberCount C.resource k →
      fiberCount E.resource k = 0 ∧ fiberCount T.resource k = 0)
    (hcornerBank : ∀ c,
      (∑ k ∈ (Finset.univ : Finset Corner) with cornerCell k = c, credit k) ≤
        ((17 : ℝ) / 80) * pos (charge c)) :
    (∑ r : SideRole, sideShare sideCount charge (S.resource r)) +
        ((1 : ℝ) / 5) * (∑ r : EndpointRole, credit (E.resource r)) +
        ((3 : ℝ) / 5) * (∑ r : ThirdRole, credit (T.resource r)) +
        (∑ r : CollisionRole, credit (C.resource r)) ≤
      ∑ c : Cell, pos (charge c) := by
  have hs := side_bank_safe S sideCount charge hsideCapacity hsidePos
  have hr := corner_roles_safe E T C credit hcredit hE hT hC hexclusive
  have hb := total_corner_credit_le cornerCell credit charge hcornerBank
  have hc :
      ((1 : ℝ) / 5) * (∑ r : EndpointRole, credit (E.resource r)) +
          ((3 : ℝ) / 5) * (∑ r : ThirdRole, credit (T.resource r)) +
          (∑ r : CollisionRole, credit (C.resource r)) ≤
        ((17 : ℝ) / 80) * ∑ c : Cell, pos (charge c) :=
    le_trans hr hb
  nlinarith

end

end CapacityBankStandalone
