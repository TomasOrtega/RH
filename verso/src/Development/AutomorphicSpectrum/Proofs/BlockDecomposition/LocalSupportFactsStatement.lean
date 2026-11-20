import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalSupportFacts.lean&line=146#L146)
-/
theorem _root_.GlobalTheory.T.local_support_facts : PositivityTheory.Rg.BcB.G8.Fin.LocSupp := by
  first | exact @GlobalTheory.CompanionTheory.TwistOrbit.locSupp | exact GlobalTheory.CompanionTheory.TwistOrbit.locSupp | (intros; apply GlobalTheory.CompanionTheory.TwistOrbit.locSupp <;> assumption)
