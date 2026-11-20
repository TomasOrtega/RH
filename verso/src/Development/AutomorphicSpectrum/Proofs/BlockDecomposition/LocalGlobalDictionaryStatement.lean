import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionary
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.local_global_dictionary : PositivityTheory.RgEis.Dict := by
  first | exact @GlobalTheory.CompanionTheory.EisDict.dict | exact GlobalTheory.CompanionTheory.EisDict.dict | (intros; apply GlobalTheory.CompanionTheory.EisDict.dict <;> assumption)
