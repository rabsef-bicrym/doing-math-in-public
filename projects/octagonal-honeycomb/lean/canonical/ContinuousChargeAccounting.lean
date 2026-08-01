import DischargeCounting

set_option linter.unusedSectionVars false

/-!
# Globally safe continuous charge allocation

This module contains the bookkeeping needed by the unrestricted octagonal
honeycomb argument.  A positive cell reserves `63/80` of its charge for side
roles and at most `17/80` for a corner bank.  At a corner, ordinary selected
edges may use `1/5` for each endpoint role and `3/5` for the unique third-cell
role.  A collision role may use the whole corner credit, but then the combined
integer budget forces all ordinary roles at that corner to vanish.
-/

namespace ContinuousChargeAccounting

noncomputable section

open scoped BigOperators
open DischargeCounting

variable {Cell SideRole Corner EndpointRole ThirdRole CollisionRole : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype SideRole] [DecidableEq SideRole]
variable [Fintype Corner] [DecidableEq Corner]
variable [Fintype EndpointRole] [DecidableEq EndpointRole]
variable [Fintype ThirdRole] [DecidableEq ThirdRole]
variable [Fintype CollisionRole] [DecidableEq CollisionRole]

/-- Per-side allocation of the `63/80` side bank. -/
def sideShare (sideCount : Cell → ℕ) (charge : Cell → ℝ) (c : Cell) : ℝ :=
  ((63 : ℝ) / 80) * charge c / sideCount c

/-- Reindex a sum of per-cell values along a finite role-to-cell map. -/
lemma role_sum_eq_counted
    {Role : Type*} [Fintype Role] [DecidableEq Role]
    (roleCell : Role → Cell) (value : Cell → ℝ) :
    (∑ r : Role, value (roleCell r)) =
      ∑ c : Cell, (endpointCount roleCell c : ℝ) * value c :=
  endpoint_sum_eq_counted roleCell value

/-- If a cell is used by at most one side role per genuine side, its allocated
side bank is no larger than `63/80` of its positive charge. -/
theorem side_bank_safe
    (roleCell : SideRole → Cell)
    (sideCount : Cell → ℕ)
    (charge : Cell → ℝ)
    (hcharge : ∀ c, 0 ≤ charge c)
    (hside_pos : ∀ c, 0 < sideCount c)
    (hmult : ∀ c, endpointCount roleCell c ≤ sideCount c) :
    (∑ r : SideRole, sideShare sideCount charge (roleCell r)) ≤
      ((63 : ℝ) / 80) * ∑ c : Cell, charge c := by
  rw [role_sum_eq_counted roleCell (sideShare sideCount charge)]
  calc
    (∑ c : Cell,
        (endpointCount roleCell c : ℝ) * sideShare sideCount charge c) ≤
        ∑ c : Cell, ((63 : ℝ) / 80) * charge c := by
      apply Finset.sum_le_sum
      intro c hc
      have hq : 0 < (sideCount c : ℝ) := by exact_mod_cast hside_pos c
      have hm : (endpointCount roleCell c : ℝ) ≤ sideCount c := by
        exact_mod_cast hmult c
      have hratio :
          (endpointCount roleCell c : ℝ) / sideCount c ≤ 1 :=
        (div_le_one hq).2 hm
      have hcoeff : 0 ≤ (63 : ℝ) / 80 := by norm_num
      calc
        (endpointCount roleCell c : ℝ) * sideShare sideCount charge c =
            ((63 : ℝ) / 80) *
              (((endpointCount roleCell c : ℝ) / sideCount c) * charge c) := by
          dsimp [sideShare]
          field_simp [ne_of_gt hq]
        _ ≤ ((63 : ℝ) / 80) * (1 * charge c) := by
          apply mul_le_mul_of_nonneg_left _ hcoeff
          exact mul_le_mul_of_nonneg_right hratio (hcharge c)
        _ = ((63 : ℝ) / 80) * charge c := by ring
    _ = ((63 : ℝ) / 80) * ∑ c : Cell, charge c := by
      rw [Finset.mul_sum]

/-- The exact integer multiplicity budget at one corner.  Multiplication by
five avoids rational counting: two endpoint roles cost `1+1`, one third role
costs `3`, and one collision role costs all `5`. -/
def CornerRoleBudget
    (endpointCorner : EndpointRole → Corner)
    (thirdCorner : ThirdRole → Corner)
    (collisionCorner : CollisionRole → Corner) : Prop :=
  ∀ k,
    endpointCount endpointCorner k +
        3 * endpointCount thirdCorner k +
        5 * endpointCount collisionCorner k ≤ 5

/-- The `1/5, 1/5, 3/5` role allocation, together with exclusive full-credit
collision roles, never spends more than the available corner credits. -/
theorem corner_roles_safe
    (endpointCorner : EndpointRole → Corner)
    (thirdCorner : ThirdRole → Corner)
    (collisionCorner : CollisionRole → Corner)
    (credit : Corner → ℝ)
    (hcredit : ∀ k, 0 ≤ credit k)
    (hbudget : CornerRoleBudget endpointCorner thirdCorner collisionCorner) :
    ((1 : ℝ) / 5) * (∑ r : EndpointRole, credit (endpointCorner r)) +
        ((3 : ℝ) / 5) * (∑ r : ThirdRole, credit (thirdCorner r)) +
        (∑ r : CollisionRole, credit (collisionCorner r)) ≤
      ∑ k : Corner, credit k := by
  rw [role_sum_eq_counted endpointCorner credit,
    role_sum_eq_counted thirdCorner credit,
    role_sum_eq_counted collisionCorner credit]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hnat := hbudget k
  have hreal :
      (endpointCount endpointCorner k : ℝ) +
          3 * (endpointCount thirdCorner k : ℝ) +
          5 * (endpointCount collisionCorner k : ℝ) ≤ 5 := by
    exact_mod_cast hnat
  have hcoef :
      ((1 : ℝ) / 5) * (endpointCount endpointCorner k : ℝ) +
          ((3 : ℝ) / 5) * (endpointCount thirdCorner k : ℝ) +
          (endpointCount collisionCorner k : ℝ) ≤ 1 := by
    nlinarith
  calc
    ((1 : ℝ) / 5) *
          ((endpointCount endpointCorner k : ℝ) * credit k) +
        ((3 : ℝ) / 5) *
          ((endpointCount thirdCorner k : ℝ) * credit k) +
        (endpointCount collisionCorner k : ℝ) * credit k =
      (((1 : ℝ) / 5) * (endpointCount endpointCorner k : ℝ) +
          ((3 : ℝ) / 5) * (endpointCount thirdCorner k : ℝ) +
          (endpointCount collisionCorner k : ℝ)) * credit k := by ring
    _ ≤ 1 * credit k :=
      mul_le_mul_of_nonneg_right hcoef (hcredit k)
    _ = credit k := one_mul _

/-- Reindex all corner credits by their owning cells. -/
theorem total_corner_credit_le
    (cornerCell : Corner → Cell)
    (credit : Corner → ℝ)
    (charge : Cell → ℝ)
    (hbank : ∀ c,
      (∑ k ∈ (Finset.univ : Finset Corner) with cornerCell k = c, credit k) ≤
        ((17 : ℝ) / 80) * charge c) :
    (∑ k : Corner, credit k) ≤
      ((17 : ℝ) / 80) * ∑ c : Cell, charge c := by
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
          ∑ k ∈ (Finset.univ : Finset Corner) with cornerCell k = c, credit k := by
      apply Finset.sum_congr rfl
      intro c hc
      simp [Finset.sum_filter]
    _ ≤ ∑ c : Cell, ((17 : ℝ) / 80) * charge c := by
      apply Finset.sum_le_sum
      intro c hc
      exact hbank c
    _ = ((17 : ℝ) / 80) * ∑ c : Cell, charge c := by
      rw [Finset.mul_sum]

/-- The side bank and corner bank together spend at most the total positive
cell charge. -/
theorem globally_safe_allocation
    (sideCell : SideRole → Cell)
    (sideCount : Cell → ℕ)
    (cornerCell : Corner → Cell)
    (endpointCorner : EndpointRole → Corner)
    (thirdCorner : ThirdRole → Corner)
    (collisionCorner : CollisionRole → Corner)
    (charge : Cell → ℝ)
    (credit : Corner → ℝ)
    (hcharge : ∀ c, 0 ≤ charge c)
    (hcredit : ∀ k, 0 ≤ credit k)
    (hside_pos : ∀ c, 0 < sideCount c)
    (hside_mult : ∀ c, endpointCount sideCell c ≤ sideCount c)
    (hcorner_bank : ∀ c,
      (∑ k ∈ (Finset.univ : Finset Corner) with cornerCell k = c, credit k) ≤
        ((17 : ℝ) / 80) * charge c)
    (hrole_budget : CornerRoleBudget endpointCorner thirdCorner collisionCorner) :
    (∑ r : SideRole, sideShare sideCount charge (sideCell r)) +
        ((1 : ℝ) / 5) * (∑ r : EndpointRole, credit (endpointCorner r)) +
        ((3 : ℝ) / 5) * (∑ r : ThirdRole, credit (thirdCorner r)) +
        (∑ r : CollisionRole, credit (collisionCorner r)) ≤
      ∑ c : Cell, charge c := by
  have hs := side_bank_safe sideCell sideCount charge hcharge hside_pos hside_mult
  have hcRoles := corner_roles_safe endpointCorner thirdCorner collisionCorner
    credit hcredit hrole_budget
  have hcBank := total_corner_credit_le cornerCell credit charge hcorner_bank
  have hcorner :
      ((1 : ℝ) / 5) * (∑ r : EndpointRole, credit (endpointCorner r)) +
          ((3 : ℝ) / 5) * (∑ r : ThirdRole, credit (thirdCorner r)) +
          (∑ r : CollisionRole, credit (collisionCorner r)) ≤
        ((17 : ℝ) / 80) * ∑ c : Cell, charge c :=
    le_trans hcRoles hcBank
  nlinarith

end

end ContinuousChargeAccounting
