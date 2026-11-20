import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishing
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSatakePowerNonvanishing.lean&line=218#L218)
-/
theorem _root_.GlobalTheory.T.satake_power_nonvanishing : PositivityTheory.SphericalProduct.SatPowNonvan := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.satPowNonvan | exact GlobalTheory.CompanionTheory.SatPow.satPowNonvan | (intros; apply GlobalTheory.CompanionTheory.SatPow.satPowNonvan <;> assumption)
