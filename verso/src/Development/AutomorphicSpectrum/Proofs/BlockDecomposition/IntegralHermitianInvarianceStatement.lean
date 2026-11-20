import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianInvariance
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.integral_hermitian_invariance : PositivityTheory.SiegelWeilFormula.Gunr.HermitianLatticeInvariance := by
  first | exact @GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian | exact GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian | (intros; apply GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian <;> assumption)
