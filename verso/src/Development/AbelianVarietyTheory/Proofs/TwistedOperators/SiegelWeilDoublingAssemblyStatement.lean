import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelWeilDoublingAssembly
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PrimIn.hypotheses3_intro` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSiegelWeilDoublingAssembly.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.siegel_weil_doubling_assembly : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.SiegelEisensteinSimplePole → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → GlobalTheory.PrimIn.Hypotheses3 := by
  first | exact @GlobalTheory.PrimIn.hypotheses3_intro | exact GlobalTheory.PrimIn.hypotheses3_intro | (intros; apply GlobalTheory.PrimIn.hypotheses3_intro <;> assumption)
