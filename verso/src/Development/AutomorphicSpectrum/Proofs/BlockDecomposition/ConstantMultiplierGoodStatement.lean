import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGood
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.constant_multiplier_good : PositivityTheory.RgEis.StdGood → PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.DictInf → PositivityTheory.RgEis.CMGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCM.cmGood | exact GlobalTheory.CompanionTheory.RgEisCM.cmGood | (intros; apply GlobalTheory.CompanionTheory.RgEisCM.cmGood <;> assumption)
