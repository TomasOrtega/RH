import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerSmallTranslationContinuity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
open scoped SchwartzMap

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArchUniq.SchrLip.schrF_sub_seminorm_le_abs` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchrodingerSmallTranslationContinuity.lean&line=269#L269)
-/
theorem _root_.GlobalTheory.T.schrodinger_small_translation_continuity : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ (u : V × V) (s₀ : Finset (ℕ × ℕ)), ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (t : ℝ), |t| ≤ 1 → ∀ (h g : 𝓢(V, ℂ)), ⇑g = GlobalTheory.ArchUniq.schrF P (t • u) ⇑h → (s₀.sup (schwartzSeminormFamily ℂ V ℂ)) (g - h) ≤ C * |t| * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
  first | exact @GlobalTheory.ArchUniq.SchrLip.schrF_sub_seminorm_le_abs | exact GlobalTheory.ArchUniq.SchrLip.schrF_sub_seminorm_le_abs | (intros; apply GlobalTheory.ArchUniq.SchrLip.schrF_sub_seminorm_le_abs <;> assumption)
