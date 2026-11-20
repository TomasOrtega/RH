import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeOfDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FN.lv_mono` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGammaLeOfDvd.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.lv_mono_of_dvd_of_le : ∀ (E : Subring ℂ) (N N' w w' : ℕ) (f : ℍ → ℂ), 0 < N' → N ∣ N' → w ≤ w' → Lv E N w f → Lv E N' w' f := by
  first | exact @GlobalTheory.FN.lv_mono | exact GlobalTheory.FN.lv_mono | (intros; apply GlobalTheory.FN.lv_mono <;> assumption)
