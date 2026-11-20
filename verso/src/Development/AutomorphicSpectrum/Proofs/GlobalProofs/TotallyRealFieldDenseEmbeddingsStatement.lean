import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyRealFieldDenseEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FTotallyRealFieldDenseEmbeddings.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.totally_real_field_dense_embeddings : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (F →+* ℝ) → ℝ) (ε : ℝ), 0 < ε → ∃ x : F, ∀ σ : F →+* ℝ, |σ x - y σ| < ε := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx <;> assumption)
