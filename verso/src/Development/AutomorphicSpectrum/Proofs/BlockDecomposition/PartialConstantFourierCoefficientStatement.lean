import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficient
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PcFc.target` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPartialConstantFourierCoefficient.lean&line=144#L144)
-/
theorem _root_.GlobalTheory.T.partial_constant_fourier_coefficient : MapsExist → PositivityTheory.PfSWUS.FourierZero → PcFc := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.target | exact GlobalTheory.CompanionTheory.PcFc.target | (intros; apply GlobalTheory.CompanionTheory.PcFc.target <;> assumption)
