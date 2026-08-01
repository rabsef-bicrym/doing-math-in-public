import ContinuousChargeAccounting

set_option linter.unusedSectionVars false

/-!
# Collision groups in the continuous discharging argument

Two negative owners may choose the same physical edge after the crystalline
angle restriction is removed.  Such an edge is treated as one collision group:
the two owner debts are paid by the full credits of the two third-cell corners.
This module formalizes the finite summation and the exclusivity condition that
allows full collision credits to coexist with the ordinary `1/5,3/5` roles.
-/

namespace CollisionChargeAccounting

noncomputable section

open scoped BigOperators
open DischargeCounting
open ContinuousChargeAccounting

variable {Collision Owner Corner EndpointRole ThirdRole CollisionRole : Type*}
variable [Fintype Collision] [DecidableEq Collision]
variable [Fintype Owner] [DecidableEq Owner]
variable [Fintype Corner] [DecidableEq Corner]
variable [Fintype EndpointRole] [DecidableEq EndpointRole]
variable [Fintype ThirdRole] [DecidableEq ThirdRole]
variable [Fintype CollisionRole] [DecidableEq CollisionRole]

/-- Summing the local two-owner collision inequalities pays all collision-group
debts by the corresponding two third-corner credits. -/
theorem collision_groups_paid
    (leftOwner rightOwner : Collision → Owner)
    (startCorner endCorner : Collision → Corner)
    (debt : Owner → ℝ) (credit : Corner → ℝ)
    (hlocal : ∀ c,
      debt (leftOwner c) + debt (rightOwner c) ≤
        credit (startCorner c) + credit (endCorner c)) :
    (∑ c : Collision,
        (debt (leftOwner c) + debt (rightOwner c))) ≤
      ∑ c : Collision,
        (credit (startCorner c) + credit (endCorner c)) := by
  apply Finset.sum_le_sum
  intro c hc
  exact hlocal c

/-- A convenient occurrence type for the two owners in every collision. -/
abbrev OwnerOccurrence (Collision : Type*) := Collision × Bool

/-- A convenient occurrence type for the two endpoint corners of every
collision edge. -/
abbrev CornerOccurrence (Collision : Type*) := Collision × Bool

def occurrenceOwner
    (leftOwner rightOwner : Collision → Owner) :
    OwnerOccurrence Collision → Owner
  | (c, false) => leftOwner c
  | (c, true) => rightOwner c

def occurrenceCorner
    (startCorner endCorner : Collision → Corner) :
    CornerOccurrence Collision → Corner
  | (c, false) => startCorner c
  | (c, true) => endCorner c

/-- If owner occurrences are injective, collision edges form a matching on the
negative-owner set: no owner participates in two collision groups. -/
theorem collision_owners_form_matching
    (leftOwner rightOwner : Collision → Owner)
    (hinj : Function.Injective (occurrenceOwner leftOwner rightOwner)) :
    ∀ c₁ c₂ b₁ b₂,
      occurrenceOwner leftOwner rightOwner (c₁,b₁) =
          occurrenceOwner leftOwner rightOwner (c₂,b₂) →
        c₁ = c₂ ∧ b₁ = b₂ := by
  intro c₁ c₂ b₁ b₂ h
  have hp : (c₁,b₁) = (c₂,b₂) := hinj h
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- A collision endpoint is used at most once when the occurrence-to-corner
map is injective. -/
theorem collision_corner_count_le_one
    (collisionCorner : CollisionRole → Corner)
    (hinj : Function.Injective collisionCorner) :
    ∀ k, endpointCount collisionCorner k ≤ 1 := by
  intro k
  classical
  have hcard :
      ((Finset.univ : Finset CollisionRole).filter fun r => collisionCorner r = k).card ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤
        ((Finset.univ : Finset CollisionRole).filter fun r => collisionCorner r = k).card := by
      omega
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Finset.one_lt_card.mp (lt_of_lt_of_le (by norm_num) htwo)
    have hca : collisionCorner a = k := (Finset.mem_filter.mp ha).2
    have hcb : collisionCorner b = k := (Finset.mem_filter.mp hb).2
    exact hab (hinj (hca.trans hcb.symm))
  simpa [endpointCount] using hcard

/-- Collision corners consume the whole credit and therefore exclude ordinary
endpoint and third roles.  Away from collisions, the usual `2+3=5` role count
suffices. -/
theorem collision_exclusive_budget
    (endpointCorner : EndpointRole → Corner)
    (thirdCorner : ThirdRole → Corner)
    (collisionCorner : CollisionRole → Corner)
    (hcollision : ∀ k, endpointCount collisionCorner k ≤ 1)
    (hexclusive : ∀ k, 0 < endpointCount collisionCorner k →
      endpointCount endpointCorner k = 0 ∧
        endpointCount thirdCorner k = 0)
    (hordinary : ∀ k, endpointCount collisionCorner k = 0 →
      endpointCount endpointCorner k ≤ 2 ∧
        endpointCount thirdCorner k ≤ 1) :
    CornerRoleBudget endpointCorner thirdCorner collisionCorner := by
  intro k
  by_cases hc : endpointCount collisionCorner k = 0
  · obtain ⟨he, ht⟩ := hordinary k hc
    rw [hc]
    omega
  · have hcpos : 0 < endpointCount collisionCorner k := Nat.pos_of_ne_zero hc
    obtain ⟨he0, ht0⟩ := hexclusive k hcpos
    have hcle := hcollision k
    rw [he0, ht0]
    omega

/-- The two-corner local collision bound in the uniform form used later: if
each owner debt is below `d` and each endpoint credit is at least `d`, the
collision pair is paid. -/
theorem two_uniform_credits_pay_collision
    (d debtLeft debtRight creditStart creditEnd : ℝ)
    (hdebtLeft : debtLeft ≤ d) (hdebtRight : debtRight ≤ d)
    (hcreditStart : d ≤ creditStart) (hcreditEnd : d ≤ creditEnd) :
    debtLeft + debtRight ≤ creditStart + creditEnd := by
  linarith

end

end CollisionChargeAccounting
