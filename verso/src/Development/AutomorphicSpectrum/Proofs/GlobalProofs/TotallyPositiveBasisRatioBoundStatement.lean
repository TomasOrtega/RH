import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyPositiveBasisRatioBound
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FTotallyPositiveBasisRatioBound.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.totally_positive_basis_ratio_bound : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) →
    ∃ R : ℝ, 0 < R ∧ ∀ x : F, (∀ i, 0 < b.repr x i) → ∀ σ τ : F →+* ℝ, σ x ≤ R * τ x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone <;> assumption)
