import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFamilyExistsOnEigenspace
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FAdaptedFamilyExistsOnEigenspace.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.adapted_family_exists_on_eigenspace : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  first | exact @GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace | exact GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace | (intros; apply GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace <;> assumption)
