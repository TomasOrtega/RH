import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCovolumeFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.hermitian_covolume_formula : PositivityTheory.SiegelWeilFormula.KWhit.MeasP.HermCovol := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermCov.hermCovol | exact GlobalTheory.CompanionTheory.SW.HermCov.hermCovol | (intros; apply GlobalTheory.CompanionTheory.SW.HermCov.hermCovol <;> assumption)
