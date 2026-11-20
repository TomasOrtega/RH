import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumPowGrowth
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRamificationJumpSumPowGrowth.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.ramificationJumpSum_pow_growth : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B C : Subgroup (L ≃ₐ[K] L)), A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ ∈ A, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild K L) A B) (jumpSum (wild K L) A B + E) ≤ jumpSum (wild K L) A C := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_pow_growth | exact GlobalTheory.PMon.Ram.jumpSum_pow_growth | (intros; apply GlobalTheory.PMon.Ram.jumpSum_pow_growth <;> assumption)
