import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedAtPlaceOfIsHalfSplitPoint
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FMatrixSupportedAtPlaceOfIsHalfSplitPoint.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.matrixSupportedAtPlace_of_isHalf_splitPoint : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (m n : ℕ) (w : Mx D m n), IsHalf (q.e + cA D q.e) w → MxAt (· = q.v) w := by
  first | exact @GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above | exact GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above | (intros; apply GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above <;> assumption)
