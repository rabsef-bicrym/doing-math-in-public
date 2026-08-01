import PhaseSnappingSum

/-! Exact identification of the affine phase baseline with the Lángi--Wang
minimum tangent-fan areas for four through eight sides. -/

namespace PhaseBaseIdentities

noncomputable section

open PairGapCore
open NoncrystallineDomainReduction
open OctagonalCornerBank
open PhaseSnappingSum

lemma phaseBase4 : phaseBase 4 = 4 := by
  dsimp [phaseBase, A8, cap, d]
  norm_num
  nlinarith [s_sq]

lemma phaseBase5 : phaseBase 5 = A5 := by
  dsimp [phaseBase, A8, cap, A5, d]
  norm_num
  nlinarith [s_sq]

lemma phaseBase6 : phaseBase 6 = A6 := by
  dsimp [phaseBase, A8, cap, A6, d]
  norm_num
  nlinarith [s_sq]

lemma phaseBase7 : phaseBase 7 = A7 := by
  dsimp [phaseBase, A8, cap, A7, d]
  norm_num
  nlinarith [s_sq]

lemma phaseBase8 : phaseBase 8 = A8 := by
  simp [phaseBase]

end

end PhaseBaseIdentities
