import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustion
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.level_exhaustion : PositivityTheory.SiegelWeilFormula.Gunr.Exhaust := by
  first | exact @GlobalTheory.CompanionTheory.GunrExhaust.exhaust | exact GlobalTheory.CompanionTheory.GunrExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.GunrExhaust.exhaust <;> assumption)
