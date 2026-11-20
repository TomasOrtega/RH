import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinThetaInvariance
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEisensteinThetaInvariance.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.eisenstein_theta_invariance : PositivityTheory.GramSchwartzFunctions.EC.ThetaInv := by
  first | exact @GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv | exact GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv | (intros; apply GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv <;> assumption)
