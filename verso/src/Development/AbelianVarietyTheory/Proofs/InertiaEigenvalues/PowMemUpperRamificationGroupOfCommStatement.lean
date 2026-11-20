import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupOfComm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPowMemUpperRamificationGroupOfComm.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.pow_mem_upperRamificationGroup_of_comm' : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ) (v : ℝ), (∀ σ τ : M ≃ₐ[F] M, σ * τ = τ * σ) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F M v, σ ^ p ∈ upperRamificationGroup F M (min (2 * v) (v + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm | exact GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm <;> assumption)
