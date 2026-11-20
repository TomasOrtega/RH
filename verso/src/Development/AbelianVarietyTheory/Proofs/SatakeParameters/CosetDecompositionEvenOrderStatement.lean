import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CosetDecompositionEvenOrder
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.frobenius_orbit_positions` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCosetDecompositionEvenOrder.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.coset_decomposition_even_order : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (φ c : G), (∀ a b : G, a * b = b * a) → H.index = 2 → φ ∉ H → c ∉ H → c * c = 1 → c ∉ Subgroup.zpowers φ → 2 ≤ orderOf φ ∧ Even (orderOf φ) ∧ ∃ (N : ℕ) (g : Fin N → G) (pos : (Σ _ : Fin N, Fin (orderOf φ)) ≃ H), 0 < N ∧ (∀ v s, (pos ⟨v, s⟩ : G) = φ ^ s.val * g v * c ^ s.val) ∧ (∀ v v', g v' * (g v)⁻¹ ∈ Subgroup.zpowers φ → v = v') ∧ (∀ v v', g v' * c * (g v)⁻¹ ∉ Subgroup.zpowers φ) ∧ ∀ x : G, ∃ v, g v * x⁻¹ ∈ Subgroup.zpowers φ ∨ g v * c * x⁻¹ ∈ Subgroup.zpowers φ := by
  first | exact @GlobalTheory.frobenius_orbit_positions | exact GlobalTheory.frobenius_orbit_positions | (intros; apply GlobalTheory.frobenius_orbit_positions <;> assumption)
