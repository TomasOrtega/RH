import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustion
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.GunrExhaust.exhaust | exact GlobalTheory.CompanionTheory.GunrExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.GunrExhaust.exhaust <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.level_exhaustion : PositivityTheory.SiegelWeilFormula.Gunr.Exhaust := by
  first | exact @GlobalTheory.CompanionTheory.GunrExhaust.exhaust | exact GlobalTheory.CompanionTheory.GunrExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.GunrExhaust.exhaust <;> assumption)
