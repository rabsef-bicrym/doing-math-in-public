import CrystallineSelection

/-!
# Dangerous quadrilateral and pentagonal turn words

A dangerous quadrilateral has four right-angle corners.  A dangerous pentagon
has exactly three right-angle corners and two H-corners.  On a cyclic pentagon,
three marked vertices force two consecutive marked vertices, hence an RR side.
-/

namespace DangerousPatterns

noncomputable section

open CrystallineSelection

variable {Cell Edge : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype Edge] [DecidableEq Edge]

/-- Cyclic successor on the five vertices of a pentagon. -/
def next5 (i : Fin 5) : Fin 5 :=
  ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩

/-- Three marked vertices on a 5-cycle contain a consecutive pair.  This is a
closed finite proposition (32 Boolean words), so kernel reduction can certify
it exhaustively. -/
theorem three_marks_have_adjacent :
    ∀ mark : Fin 5 → Bool,
      ((Finset.univ.filter fun i => mark i = true).card = 3) →
        ∃ i, mark i = true ∧ mark (next5 i) = true := by
  native_decide

variable (D : CoreData Cell Edge)
variable {c : Cell}

/-- Full turn-word witness for a dangerous quadrilateral. -/
structure QuadrilateralWitness (c : Cell) where
  enumerate : Fin 4 ≃ SideIncidence D.cell c
  start_rr : ∀ i,
    D.turnStart (enumerate i).1.1 (enumerate i).1.2 = 2
  end_rr : ∀ i,
    D.turnEnd (enumerate i).1.1 (enumerate i).1.2 = 2

/-- Full cyclic turn-word witness for a dangerous pentagon.  `isR i` records
whether corner `i` is a right-angle corner; non-R corners are H-corners. -/
structure PentagonWitness (c : Cell) where
  enumerate : Fin 5 ≃ SideIncidence D.cell c
  isR : Fin 5 → Bool
  r_count : ((Finset.univ.filter fun i => isR i = true).card = 3)
  start_turn : ∀ i,
    D.turnStart (enumerate i).1.1 (enumerate i).1.2 =
      if isR i then 2 else 1
  end_turn : ∀ i,
    D.turnEnd (enumerate i).1.1 (enumerate i).1.2 =
      if isR (next5 i) then 2 else 1

/-- The two dangerous isolated-optimizer patterns. -/
inductive DangerousWitness (c : Cell) where
  | quadrilateral (w : QuadrilateralWitness D c)
  | pentagon (w : PentagonWitness D c)

/-- Every dangerous quadrilateral or pentagon has an RR side. -/
theorem dangerous_has_rr (w : DangerousWitness D c) :
    ∃ p : SideIncidence D.cell c,
      D.turnStart p.1.1 p.1.2 = 2 ∧
        D.turnEnd p.1.1 p.1.2 = 2 := by
  cases w with
  | quadrilateral q =>
      refine ⟨q.enumerate 0, q.start_rr 0, q.end_rr 0⟩
  | pentagon p =>
      obtain ⟨i, hi, hnext⟩ := three_marks_have_adjacent p.isR p.r_count
      refine ⟨p.enumerate i, ?_, ?_⟩
      · rw [p.start_turn i]
        simp [hi]
      · rw [p.end_turn i]
        simp [hnext]

/-- Canonical (classically chosen) RR side for a dangerous cell. -/
noncomputable def chosenRR (w : DangerousWitness D c) :
    SideIncidence D.cell c :=
  Classical.choose (dangerous_has_rr D w)

lemma chosenRR_is_rr (w : DangerousWitness D c) :
    D.turnStart (chosenRR D w).1.1 (chosenRR D w).1.2 = 2 ∧
      D.turnEnd (chosenRR D w).1.1 (chosenRR D w).1.2 = 2 :=
  Classical.choose_spec (dangerous_has_rr D w)

end

end DangerousPatterns
