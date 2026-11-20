import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDualFamilyHolds
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedDualFamilyHolds.lean&line=256#L256)
-/
theorem _root_.GlobalTheory.T.unramified_dual_family_holds : PositivityTheory.Rg.Tf.Loc.IntegralBasisUnramified → PositivityTheory.Rg.Tf.Loc.TraceOneIntegralElement := by
  first | exact @GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family | exact GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family | (intros; apply GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family <;> assumption)
