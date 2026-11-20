import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianVolumeOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.integral_hermitian_volume_one : PositivityTheory.SiegelWeilFormula.Gunr.HermitianLatticeVolumeOne := by
  first | exact @GlobalTheory.CompanionTheory.GoodHerm.volume_integral_hermitian_one | exact GlobalTheory.CompanionTheory.GoodHerm.volume_integral_hermitian_one | (intros; apply GlobalTheory.CompanionTheory.GoodHerm.volume_integral_hermitian_one <;> assumption)
