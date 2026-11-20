import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G2OfLocalOrbitCharacter
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.GlobalComplexCoefficients
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLaplaceFactorisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantFactorsProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FG2OfLocalOrbitCharacter.lean&line=420#L420)
-/
theorem _root_.GlobalTheory.T.globalComplexCoefficients_of_local_orbit_character : EllLocal → KapOrbAE → ChWMap → GlobalComplexCoefficients := by
  first | exact @GlobalTheory.CompanionTheory.resultantFactorHypotheses.g2c | exact GlobalTheory.CompanionTheory.resultantFactorHypotheses.g2c | (intros; apply GlobalTheory.CompanionTheory.resultantFactorHypotheses.g2c <;> assumption)
