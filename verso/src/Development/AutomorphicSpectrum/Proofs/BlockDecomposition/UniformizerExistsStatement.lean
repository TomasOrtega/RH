import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformizerExists.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.uniformizer_exists : UnifEx := by
  first | exact @GlobalTheory.CompanionTheory.UnifFix.unifEx | exact GlobalTheory.CompanionTheory.UnifFix.unifEx | (intros; apply GlobalTheory.CompanionTheory.UnifFix.unifEx <;> assumption)
