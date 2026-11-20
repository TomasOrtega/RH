import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsTotallyPositiveBasisPositiveCoords
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FExistsTotallyPositiveBasisPositiveCoords.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.exists_totally_positive_basis_positive_coords : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : ℝ),
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) ∧
      ∀ x : F, TotPos F x → (∀ σ τ : F →+* ℝ, σ x ≤ M * τ x) → ∀ i, 0 < b.repr x i := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis <;> assumption)
