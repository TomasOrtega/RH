import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FThetaConvergenceOfSiegelSet.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.theta_convergence_of_siegel_set : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.WeilThetaConvergence := by
  first | exact @GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet | exact GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet | (intros; apply GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet <;> assumption)
