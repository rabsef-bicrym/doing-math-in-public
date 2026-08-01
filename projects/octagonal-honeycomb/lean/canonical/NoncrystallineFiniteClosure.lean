import NoncrystallineNetLedger
import ContinuousChargeAccounting

/-!
# Finite unrestricted closure from local payments

This module packages the complete finite discharging ledger.  Once ordinary
selected owners are paid by side/endpoint/third resources, collision owners are
paid by exclusive full-corner resources, and the global role allocation is
safe, the total net cell charge is nonnegative.
-/

namespace NoncrystallineFiniteClosure

noncomputable section

open scoped BigOperators
open ContinuousCornerBank
open ContinuousChargeAccounting
open NoncrystallineNetLedger

variable {Cell Owner Collision SideRole Corner EndpointRole ThirdRole CollisionRole : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype Owner] [DecidableEq Owner]
variable [Fintype Collision] [DecidableEq Collision]
variable [Fintype SideRole] [DecidableEq SideRole]
variable [Fintype Corner] [DecidableEq Corner]
variable [Fintype EndpointRole] [DecidableEq EndpointRole]
variable [Fintype ThirdRole] [DecidableEq ThirdRole]
variable [Fintype CollisionRole] [DecidableEq CollisionRole]

/-- Aggregate closure theorem.  It deliberately separates local geometric
payment inequalities from the global no-double-spending theorem. -/
theorem close_from_aggregate_payments
    (charge : Cell → ℝ)
    (ordinaryDebt : Owner → ℝ)
    (collisionDebt : Collision → ℝ)
    (sideUse endpointUse thirdUse collisionUse : ℝ)
    (hdebt :
      (∑ c : Cell, pos (-charge c)) =
        (∑ o : Owner, ordinaryDebt o) +
          (∑ g : Collision, collisionDebt g))
    (hordinary :
      (∑ o : Owner, ordinaryDebt o) ≤
        sideUse + endpointUse + thirdUse)
    (hcollision :
      (∑ g : Collision, collisionDebt g) ≤ collisionUse)
    (hsafe :
      sideUse + endpointUse + thirdUse + collisionUse ≤
        ∑ c : Cell, pos (charge c)) :
    0 ≤ ∑ c : Cell, charge c := by
  apply finite_net_charge_nonneg charge
    (∑ o : Owner, ordinaryDebt o)
    (∑ g : Collision, collisionDebt g)
    (sideUse + endpointUse + thirdUse)
    collisionUse hdebt hordinary hcollision
  nlinarith

/-- Structured closure theorem using the exact `63/80` side bank and
`1/5,1/5,3/5` corner allocation. -/
theorem close_from_role_allocation
    (charge : Cell → ℝ)
    (ordinaryDebt : Owner → ℝ)
    (collisionDebt : Collision → ℝ)
    (sideCell : SideRole → Cell)
    (sideCount : Cell → ℕ)
    (cornerCell : Corner → Cell)
    (endpointCorner : EndpointRole → Corner)
    (thirdCorner : ThirdRole → Corner)
    (collisionCorner : CollisionRole → Corner)
    (credit : Corner → ℝ)
    (hdebt :
      (∑ c : Cell, pos (-charge c)) =
        (∑ o : Owner, ordinaryDebt o) +
          (∑ g : Collision, collisionDebt g))
    (hcharge : ∀ c, 0 ≤ pos (charge c))
    (hcredit : ∀ k, 0 ≤ credit k)
    (hside_pos : ∀ c, 0 < sideCount c)
    (hside_mult : ∀ c,
      DischargeCounting.endpointCount sideCell c ≤ sideCount c)
    (hcorner_bank : ∀ c,
      (∑ k ∈ (Finset.univ : Finset Corner) with cornerCell k = c, credit k) ≤
        ((17 : ℝ) / 80) * pos (charge c))
    (hrole_budget :
      CornerRoleBudget endpointCorner thirdCorner collisionCorner)
    (hordinary :
      (∑ o : Owner, ordinaryDebt o) ≤
        (∑ r : SideRole, sideShare sideCount (fun c => pos (charge c))
          (sideCell r)) +
        ((1 : ℝ) / 5) *
          (∑ r : EndpointRole, credit (endpointCorner r)) +
        ((3 : ℝ) / 5) *
          (∑ r : ThirdRole, credit (thirdCorner r)))
    (hcollision :
      (∑ g : Collision, collisionDebt g) ≤
        ∑ r : CollisionRole, credit (collisionCorner r)) :
    0 ≤ ∑ c : Cell, charge c := by
  have hsafe := globally_safe_allocation sideCell sideCount cornerCell
    endpointCorner thirdCorner collisionCorner
    (fun c => pos (charge c)) credit hcharge hcredit hside_pos hside_mult
    hcorner_bank hrole_budget
  apply close_from_aggregate_payments charge ordinaryDebt collisionDebt
    (∑ r : SideRole, sideShare sideCount (fun c => pos (charge c)) (sideCell r))
    (((1 : ℝ) / 5) * (∑ r : EndpointRole, credit (endpointCorner r)))
    (((3 : ℝ) / 5) * (∑ r : ThirdRole, credit (thirdCorner r)))
    (∑ r : CollisionRole, credit (collisionCorner r))
    hdebt hordinary hcollision
  exact hsafe

end

end NoncrystallineFiniteClosure
