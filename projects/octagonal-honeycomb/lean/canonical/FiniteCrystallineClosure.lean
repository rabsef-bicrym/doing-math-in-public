import DangerousPatterns
import CollisionCore

/-!
# Finite crystalline selected-edge closure

This module closes the finite combinatorial part of the octagonal honeycomb
argument. A selected family chooses one RR side from each dangerous cell.
Trivalent positive-turn arithmetic makes the selected physical edges distinct;
positive crystalline turn budget bounds total selected incidence at each cell by
8. The previously formalized 0.101 pair gap then pays a 0.009 debt per dangerous
cell.
-/

namespace FiniteCrystallineClosure

noncomputable section

open scoped BigOperators
open CrystallineSelection
open DischargeCounting

variable {Cell Edge Bad : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype Bad] [DecidableEq Bad]

structure SelectedFamily (D : CoreData Cell Edge) (Bad : Type*) where
  owner : Bad → Cell
  edge : Bad → Edge
  side : Bad → Bool
  owner_injective : Function.Injective owner
  owner_incidence : ∀ b, D.cell (edge b) (side b) = owner b
  start_rr : ∀ b, D.turnStart (edge b) (side b) = 2
  end_rr : ∀ b, D.turnEnd (edge b) (side b) = 2

variable {D : CoreData Cell Edge}

noncomputable def ofDangerousWitness
    (bad : Cell → Prop) [DecidablePred bad]
    (witness : ∀ b : {c : Cell // bad c},
      DangerousPatterns.DangerousWitness D b.1) :
    SelectedFamily D {c : Cell // bad c} where
  owner := fun b => b.1
  edge := fun b => (DangerousPatterns.chosenRR D (witness b)).1.1
  side := fun b => (DangerousPatterns.chosenRR D (witness b)).1.2
  owner_injective := Subtype.val_injective
  owner_incidence := fun b => (DangerousPatterns.chosenRR D (witness b)).2
  start_rr := fun b => (DangerousPatterns.chosenRR_is_rr D (witness b)).1
  end_rr := fun b => (DangerousPatterns.chosenRR_is_rr D (witness b)).2

def neighbor (S : SelectedFamily D Bad) (b : Bad) : Cell :=
  D.cell (S.edge b) (opposite (S.side b))

omit [Fintype Bad] in
theorem selected_edge_injective (S : SelectedFamily D Bad) :
    Function.Injective S.edge := by
  intro a b hab
  by_cases hs : S.side a = S.side b
  · apply S.owner_injective
    calc
      S.owner a = D.cell (S.edge a) (S.side a) := (S.owner_incidence a).symm
      _ = D.cell (S.edge b) (S.side b) := by rw [hab, hs]
      _ = S.owner b := S.owner_incidence b
  · have hra := S.start_rr a
    have hrb := S.start_rr b
    have hsum := D.start_vertex_sum (S.edge a)
    have hthird := D.thirdStart_pos (S.edge a)
    cases ha : S.side a <;> cases hb : S.side b
    · exact (hs (by simp [ha, hb])).elim
    · have hfalse : D.turnStart (S.edge a) false = 2 := by
        simpa [ha] using hra
      have htrue : D.turnStart (S.edge a) true = 2 := by
        simpa [hab, hb] using hrb
      omega
    · have htrue : D.turnStart (S.edge a) true = 2 := by
        simpa [ha] using hra
      have hfalse : D.turnStart (S.edge a) false = 2 := by
        simpa [hab, hb] using hrb
      omega
    · exact (hs (by simp [ha, hb])).elim

abbrev OwnerAt (S : SelectedFamily D Bad) (c : Cell) :=
  {b : Bad // S.owner b = c}

abbrev NeighborAt (S : SelectedFamily D Bad) (c : Cell) :=
  {b : Bad // neighbor S b = c}

def occurrenceToSide (S : SelectedFamily D Bad) (c : Cell) :
    OwnerAt S c ⊕ NeighborAt S c → SideIncidence D.cell c
  | Sum.inl b =>
      ⟨(S.edge b.1, S.side b.1), (S.owner_incidence b.1).trans b.2⟩
  | Sum.inr b =>
      ⟨(S.edge b.1, opposite (S.side b.1)), by
        simpa [neighbor] using b.2⟩

omit [Fintype Bad] in
theorem occurrenceToSide_injective (S : SelectedFamily D Bad) (c : Cell) :
    Function.Injective (occurrenceToSide S c) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          have hed : S.edge x.1 = S.edge y.1 :=
            congrArg (fun p => p.1.1) hxy
          have hbase : x.1 = y.1 := selected_edge_injective S hed
          have hsub : x = y := Subtype.ext hbase
          simp [hsub]
      | inr y =>
          exfalso
          have hed : S.edge x.1 = S.edge y.1 :=
            congrArg (fun p => p.1.1) hxy
          have hside : S.side x.1 = opposite (S.side y.1) :=
            congrArg (fun p => p.1.2) hxy
          have hbase : x.1 = y.1 := selected_edge_injective S hed
          have hself : S.side x.1 = opposite (S.side x.1) := by
            simpa [hbase] using hside
          exact (opposite_ne_self (S.side x.1)) hself.symm
  | inr x =>
      cases y with
      | inl y =>
          exfalso
          have hed : S.edge x.1 = S.edge y.1 :=
            congrArg (fun p => p.1.1) hxy
          have hside : opposite (S.side x.1) = S.side y.1 :=
            congrArg (fun p => p.1.2) hxy
          have hbase : x.1 = y.1 := selected_edge_injective S hed
          have hself : opposite (S.side x.1) = S.side x.1 := by
            simpa [hbase] using hside
          exact (opposite_ne_self (S.side x.1)) hself
      | inr y =>
          have hed : S.edge x.1 = S.edge y.1 :=
            congrArg (fun p => p.1.1) hxy
          have hbase : x.1 = y.1 := selected_edge_injective S hed
          have hsub : x = y := Subtype.ext hbase
          simp [hsub]

theorem incidence_le_eight (S : SelectedFamily D Bad) (c : Cell) :
    incidenceCount S.owner (neighbor S) c ≤ 8 := by
  have hcard :
      Fintype.card (OwnerAt S c ⊕ NeighborAt S c) ≤
        Fintype.card (SideIncidence D.cell c) :=
    Fintype.card_le_of_injective (occurrenceToSide S c)
      (occurrenceToSide_injective S c)
  have hside := side_count_le_eight D c
  have hsum : Fintype.card (OwnerAt S c ⊕ NeighborAt S c) ≤ 8 :=
    le_trans hcard hside
  have hsum' :
      Fintype.card (OwnerAt S c) + Fintype.card (NeighborAt S c) ≤ 8 := by
    simpa using hsum
  have howner :
      Fintype.card (OwnerAt S c) = endpointCount S.owner c := by
    simpa [OwnerAt, endpointCount] using
      (Fintype.card_of_subtype
        (p := fun b : Bad => S.owner b = c)
        ((Finset.univ : Finset Bad).filter fun b => S.owner b = c)
        (by intro b; simp))
  have hneighbor :
      Fintype.card (NeighborAt S c) = endpointCount (neighbor S) c := by
    simpa [NeighborAt, endpointCount] using
      (Fintype.card_of_subtype
        (p := fun b : Bad => neighbor S b = c)
        ((Finset.univ : Finset Bad).filter fun b => neighbor S b = c)
        (by intro b; simp))
  rw [howner, hneighbor] at hsum'
  exact hsum'

theorem finite_payment
    (S : SelectedFamily D Bad)
    (excess : Cell → ℝ)
    (hexcess : ∀ c, 0 ≤ excess c)
    (hpair : ∀ b, (101 : ℝ) / 1000 ≤
      excess (S.owner b) + excess (neighbor S b)) :
    ((9 : ℝ) / 1000) * Fintype.card Bad ≤
      ∑ c : Cell, excess c := by
  have hselected := selected_edges_global_bound
    S.owner (neighbor S) excess hexcess (incidence_le_eight S) hpair
  have hN : 0 ≤ (Fintype.card Bad : ℝ) := by positivity
  exact point_one_zero_one_pays_point_zero_zero_nine
    (Fintype.card Bad : ℝ) (∑ c : Cell, excess c) hN hselected

end

end FiniteCrystallineClosure
