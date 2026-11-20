import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteGLHaarMeasureEqPiLocal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HaarPi.haarGL_eq_pi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FInfiniteGLHaarMeasureEqPiLocal.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ), haarGL E j = (Measure.pi fun _ : InfinitePlace E => haarLoc j : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) := by
  first | exact @GlobalTheory.HaarPi.haarGL_eq_pi | exact GlobalTheory.HaarPi.haarGL_eq_pi | (intros; apply GlobalTheory.HaarPi.haarGL_eq_pi <;> assumption)
