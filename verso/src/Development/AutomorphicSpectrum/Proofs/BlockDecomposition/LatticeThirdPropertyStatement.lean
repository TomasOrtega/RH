import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeThirdProperty
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.lattice_third_property : PositivityTheory.Rg.Tf.Loc.TraceOneIntegralElement → PositivityTheory.Rg.Tf.Loc.L1 → PositivityTheory.Rg.Tf.Loc.L3 := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.Descent.unramified_descent_coset | exact GlobalTheory.CompanionTheory.TfLoc.Descent.unramified_descent_coset | (intros; apply GlobalTheory.CompanionTheory.TfLoc.Descent.unramified_descent_coset <;> assumption)
