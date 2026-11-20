import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteUnitsBoundedEmbeddingRatio
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FFiniteUnitsBoundedEmbeddingRatio.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.finite_units_bounded_embedding_ratio : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (R : ℝ),
    {u : (𝓞 F)ˣ | TotPos F ((u : 𝓞 F) : F) ∧ ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F)}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio <;> assumption)
