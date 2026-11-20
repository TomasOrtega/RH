import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenDiagonalSliceLevelSubgroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SliceTwo.isOpen_levelSub` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenDiagonalSliceLevelSubgroup.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isOpen_diagonalSliceLevelSubgroup : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → IsOpen (GlobalTheory.SliceTwo.levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) := by
  first | exact @GlobalTheory.SliceTwo.isOpen_levelSub | exact GlobalTheory.SliceTwo.isOpen_levelSub | (intros; apply GlobalTheory.SliceTwo.isOpen_levelSub <;> assumption)
