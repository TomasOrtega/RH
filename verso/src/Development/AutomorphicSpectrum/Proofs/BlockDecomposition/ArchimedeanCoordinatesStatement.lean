import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinates
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SW.CoordR.coordInf | exact GlobalTheory.CompanionTheory.SW.CoordR.coordInf | (intros; apply GlobalTheory.CompanionTheory.SW.CoordR.coordInf <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.archimedean_coordinates : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  first | exact @GlobalTheory.CompanionTheory.SW.CoordR.coordInf | exact GlobalTheory.CompanionTheory.SW.CoordR.coordInf | (intros; apply GlobalTheory.CompanionTheory.SW.CoordR.coordInf <;> assumption)
