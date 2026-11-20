import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LatticeCongruenceSubgroupsOpenCompact
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BLevel.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FLatticeCongruenceSubgroupsOpenCompact.lean&line=252#L252)
-/
theorem _root_.GlobalTheory.T.lattice_congruence_subgroups_open_compact : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (s : L →+* L), (∀ x, ‖s x‖ = ‖x‖) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) L) (Λ : AddSubgroup (Fin n → L)), IsLat L Λ → (∀ π : L, π ≠ 0 → ‖π‖ < 1 → ∃ K K₀ : Subgroup (UG s J), (∀ g, g ∈ K ↔ ∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) ∧ (∀ g, g ∈ K₀ ↔ ∀ x, g.1.1.mulVec x ∈ Λ ↔ x ∈ Λ) ∧ IsOpen (K : Set (UG s J)) ∧ IsCompact (K : Set (UG s J)) ∧ IsCompact (K₀ : Set (UG s J)) ∧ K ≤ K₀ ∧ ∀ c ∈ K₀, ∀ k, k ∈ K ↔ c * k * c⁻¹ ∈ K) ∧ ∀ U : Subgroup (UG s J), IsOpen (U : Set (UG s J)) → ∃ π : L, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ g : UG s J, (∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) → g ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.BLevel.main | exact GlobalTheory.CompanionTheory.BLevel.main | (intros; apply GlobalTheory.CompanionTheory.BLevel.main <;> assumption)
