import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelian
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardLeWildJumpSumOfElementaryAbelian.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.card_le_wildJumpSum_of_elementaryAbelian : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  first | exact @GlobalTheory.PMon.Ram.card_le_jumpSum_wild | exact GlobalTheory.PMon.Ram.card_le_jumpSum_wild | (intros; apply GlobalTheory.PMon.Ram.card_le_jumpSum_wild <;> assumption)
