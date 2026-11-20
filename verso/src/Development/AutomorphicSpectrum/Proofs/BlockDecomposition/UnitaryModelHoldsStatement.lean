import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryModelHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnitaryModelHolds.lean&line=168#L168)
-/
theorem _root_.GlobalTheory.T.unitary_model_holds : UModel := by
  first | exact @GlobalTheory.CompanionTheory.UMod.uModel | exact GlobalTheory.CompanionTheory.UMod.uModel | (intros; apply GlobalTheory.CompanionTheory.UMod.uModel <;> assumption)
