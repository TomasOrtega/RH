import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAutomorphicOfConvergence
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ThetaAutoPf.thetaAuto` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FThetaAutomorphicOfConvergence.lean&line=302#L302)
-/
theorem _root_.GlobalTheory.T.theta_automorphic_of_convergence : GlobalTheory.Published.WeilThetaConvergence → PositivityTheory.PfSWUS.ThetaAuto := by
  first | exact @GlobalTheory.CompanionTheory.ThetaAutoPf.thetaAuto | exact GlobalTheory.CompanionTheory.ThetaAutoPf.thetaAuto | (intros; apply GlobalTheory.CompanionTheory.ThetaAutoPf.thetaAuto <;> assumption)
