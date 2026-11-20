import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFrobeniusWindowSeriesTermMono
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMonE.term_norm_mono` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNormFrobeniusWindowSeriesTermMono.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.norm_frobeniusWindowSeriesTerm_mono : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π x : Fin h → F), (∀ j, ‖x j‖ ≤ ‖π j‖) → ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam x r j n‖ ≤ ‖term p ϖ lam π r j n‖ := by
  first | exact @GlobalTheory.PMonE.term_norm_mono | exact GlobalTheory.PMonE.term_norm_mono | (intros; apply GlobalTheory.PMonE.term_norm_mono <;> assumption)
