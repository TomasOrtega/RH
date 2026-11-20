import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetMeasureFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.coset_measure_formula : PositivityTheory.SiegelWeilFormula.Gunr.CosetMeas := by
  first | exact @GlobalTheory.CompanionTheory.GunrCoset.cosetMeas | exact GlobalTheory.CompanionTheory.GunrCoset.cosetMeas | (intros; apply GlobalTheory.CompanionTheory.GunrCoset.cosetMeas <;> assumption)
