import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstant
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FNelsonExistsWordGrowthConstant.lean&line=287#L287)
-/
theorem _root_.GlobalTheory.T.nelson_exists_word_growth_constant : ∀ {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {d : ℕ} (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a) (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖) (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V), ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ C ^ (l.length + 1) * l.length.factorial * ‖u‖ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth <;> assumption)
