import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityIntegral
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.density_integral : PositivityTheory.PfSWUS.SchInf.DensInt := by
  first | exact @GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf | exact GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf | (intros; apply GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf <;> assumption)
