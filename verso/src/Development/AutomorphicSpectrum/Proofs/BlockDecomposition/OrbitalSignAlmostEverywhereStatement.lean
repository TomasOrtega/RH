import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitalSignAlmostEverywhere
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FOrbitalSignAlmostEverywhere.lean&line=141#L141)
-/
theorem _root_.GlobalTheory.T.orbital_sign_almost_everywhere : KapOrbAE := by
  first | exact @GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | exact GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | (intros; apply GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE <;> assumption)
