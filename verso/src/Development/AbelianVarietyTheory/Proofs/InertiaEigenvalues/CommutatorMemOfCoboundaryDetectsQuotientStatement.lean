import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutatorMemOfCoboundaryDetectsQuotient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Ram.commutator_mem_of_detects` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCommutatorMemOfCoboundaryDetectsQuotient.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.commutator_mem_of_coboundary_detects_quotient : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → Detects p r A B → ∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B := by
  first | exact @GlobalTheory.PMon.Ram.commutator_mem_of_detects | exact GlobalTheory.PMon.Ram.commutator_mem_of_detects | (intros; apply GlobalTheory.PMon.Ram.commutator_mem_of_detects <;> assumption)
