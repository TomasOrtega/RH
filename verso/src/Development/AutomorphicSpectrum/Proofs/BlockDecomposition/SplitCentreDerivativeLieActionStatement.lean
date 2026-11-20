import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSplitCentreDerivativeLieAction.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.split_centre_derivative_lie_action : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (s : ℝ), HasDerivAt (fun s : ℝ => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) ((lie E a (oneL E a) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) s := by
  first | exact @GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre | exact GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre | (intros; apply GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre <;> assumption)
