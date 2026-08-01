import ContinuousCornerBank
import ContinuousChargeAccounting
import CollisionChargeAccounting

/-!
# Final finite net-charge ledger

This module isolates the last purely algebraic step of the unrestricted
argument.  Negative cell charge is partitioned into ordinary selected owners
and collision owners.  Their local inequalities pay those debts from globally
safe positive side/corner resources.  Once total resource use is bounded by
total positive cell charge, the sum of all net cell charges is nonnegative.
-/

namespace NoncrystallineNetLedger

noncomputable section

open scoped BigOperators
open ContinuousCornerBank

variable {Cell : Type*} [Fintype Cell]

lemma charge_eq_pos_sub (x : ℝ) : x = pos x - pos (-x) := by
  by_cases hx : 0 ≤ x
  · have hneg : -x ≤ 0 := neg_nonpos.mpr hx
    rw [pos_eq_self_of_nonneg hx, pos_eq_zero_of_nonpos hneg]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hneg : 0 ≤ -x := neg_nonneg.mpr hx'
    rw [pos_eq_zero_of_nonpos hx', pos_eq_self_of_nonneg hneg]
    ring

lemma sum_charge_identity (charge : Cell → ℝ) :
    (∑ c : Cell, charge c) =
      (∑ c : Cell, pos (charge c)) -
        (∑ c : Cell, pos (-charge c)) := by
  calc
    (∑ c : Cell, charge c) =
        ∑ c : Cell, (pos (charge c) - pos (-charge c)) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact charge_eq_pos_sub (charge c)
    _ = (∑ c : Cell, pos (charge c)) -
        (∑ c : Cell, pos (-charge c)) := by
      rw [Finset.sum_sub_distrib]

/-- Abstract terminal ledger.  `ordinaryDebt` and `collisionDebt` partition all
negative charge; `ordinaryUse` and `collisionUse` are their corresponding
positive-resource expenditures. -/
theorem finite_net_charge_nonneg
    (charge : Cell → ℝ)
    (ordinaryDebt collisionDebt ordinaryUse collisionUse : ℝ)
    (hdebt :
      (∑ c : Cell, pos (-charge c)) = ordinaryDebt + collisionDebt)
    (hordinary : ordinaryDebt ≤ ordinaryUse)
    (hcollision : collisionDebt ≤ collisionUse)
    (huse : ordinaryUse + collisionUse ≤
      ∑ c : Cell, pos (charge c)) :
    0 ≤ ∑ c : Cell, charge c := by
  rw [sum_charge_identity]
  rw [hdebt]
  nlinarith

/-- Local ordinary-owner inequalities may be summed before entering the final
ledger. -/
theorem ordinary_debts_paid
    {Owner : Type*} [Fintype Owner]
    (debt use : Owner → ℝ)
    (hlocal : ∀ o, debt o ≤ use o) :
    (∑ o : Owner, debt o) ≤ ∑ o : Owner, use o := by
  exact Finset.sum_le_sum fun o ho => hlocal o

/-- If ordinary and collision debts are represented by finite occurrence
families, their local payment theorems plug directly into the terminal ledger. -/
theorem finite_net_charge_nonneg_of_local
    {Owner Collision : Type*} [Fintype Owner] [Fintype Collision]
    (charge : Cell → ℝ)
    (ordinaryDebt ordinaryUse : Owner → ℝ)
    (collisionDebt collisionUse : Collision → ℝ)
    (hdebt :
      (∑ c : Cell, pos (-charge c)) =
        (∑ o : Owner, ordinaryDebt o) +
          (∑ g : Collision, collisionDebt g))
    (hordinary : ∀ o, ordinaryDebt o ≤ ordinaryUse o)
    (hcollision : ∀ g, collisionDebt g ≤ collisionUse g)
    (huse :
      (∑ o : Owner, ordinaryUse o) +
          (∑ g : Collision, collisionUse g) ≤
        ∑ c : Cell, pos (charge c)) :
    0 ≤ ∑ c : Cell, charge c := by
  apply finite_net_charge_nonneg charge
    (∑ o : Owner, ordinaryDebt o)
    (∑ g : Collision, collisionDebt g)
    (∑ o : Owner, ordinaryUse o)
    (∑ g : Collision, collisionUse g)
    hdebt
  · exact Finset.sum_le_sum fun o ho => hordinary o
  · exact Finset.sum_le_sum fun g hg => hcollision g
  · exact huse

end

end NoncrystallineNetLedger
