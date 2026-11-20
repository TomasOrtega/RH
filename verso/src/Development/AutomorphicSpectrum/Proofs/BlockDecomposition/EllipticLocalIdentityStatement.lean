import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticLocalIdentity
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.EllLoc.ellLocal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEllipticLocalIdentity.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.elliptic_local_identity : EllLocal := by
  first | exact @GlobalTheory.CompanionTheory.EllLoc.ellLocal | exact GlobalTheory.CompanionTheory.EllLoc.ellLocal | (intros; apply GlobalTheory.CompanionTheory.EllLoc.ellLocal <;> assumption)
