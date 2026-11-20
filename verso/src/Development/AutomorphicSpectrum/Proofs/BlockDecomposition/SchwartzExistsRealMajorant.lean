import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormTheta2TailLeOfLeOne

open scoped SchwartzMap

namespace GlobalTheory.CompanionTheory.SchwartzMaj

/- English proof (translation)
Take `⟨Φ, r, hΦ, hr⟩` from `GlobalTheory.CompanionTheory.EisRk1.exists_schwartz_majorant f`. Use `⟨Φ, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ x]`. Conclude with `⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hr x⟩`.
-/
theorem exists_nonneg_schwartz_majorant (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : SchwartzMap E ℂ) :
    ∃ F : SchwartzMap E ℂ, ∀ x, (F x).im = 0 ∧ ‖f x‖ ≤ (F x).re := by
  obtain ⟨Φ, r, hΦ, hr⟩ := GlobalTheory.CompanionTheory.EisRk1.exists_schwartz_majorant f
  refine ⟨Φ, fun x => ?_⟩
  rw [hΦ x]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hr x⟩

end GlobalTheory.CompanionTheory.SchwartzMaj
