import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalTotallyPositiveDefinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RowsOrb.pd_hU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAnisotropicOrthogonalTotallyPositiveDefinite.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.anisotropicOrthogonal_totallyPositiveDefinite : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.Mass.PD (GlobalTheory.RowsOrb.hU X u) := by
  first | exact @GlobalTheory.RowsOrb.pd_hU | exact GlobalTheory.RowsOrb.pd_hU | (intros; apply GlobalTheory.RowsOrb.pd_hU <;> assumption)
