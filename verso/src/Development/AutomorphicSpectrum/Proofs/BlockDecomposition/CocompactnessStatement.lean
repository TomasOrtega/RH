import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cocompactness
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCocompactness.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.cocompactness : CoCpt := by
  first | exact @GlobalTheory.CompanionTheory.MassCocompact.coCpt | exact GlobalTheory.CompanionTheory.MassCocompact.coCpt | (intros; apply GlobalTheory.CompanionTheory.MassCocompact.coCpt <;> assumption)
