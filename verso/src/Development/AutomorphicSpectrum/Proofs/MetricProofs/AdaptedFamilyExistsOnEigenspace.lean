import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.OrthogonalFamilyAdaptedBasis
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `LevelTowerAlt.orthogonal_family_adapted_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FPlurisubharmonicCones%2FOrthogonalFamilyAdaptedBasis.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  first | exact @LevelTowerAlt.orthogonal_family_adapted_basis | exact LevelTowerAlt.orthogonal_family_adapted_basis
