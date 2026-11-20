import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMonE.winThm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFrobeniusPolydiscWindowsSurjectiveBoundsZero.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.frobenius_polydisc_windows_surjective_bounds_zero : WinThm := by
  first | exact @GlobalTheory.PMonE.winThm | exact GlobalTheory.PMonE.winThm | (intros; apply GlobalTheory.PMonE.winThm <;> assumption)
