import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperRamificationGroupOneEqTopOfExponentPrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUpperRamificationGroupOneEqTopOfExponentPrime.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.upperRamificationGroup_one_eq_top_of_exponent_prime : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ), p.Prime → 0 < e → OrdIs F p e → upperRamificationGroup F M 0 = ⊤ → (∀ σ : M ≃ₐ[F] M, σ ^ p = 1) → upperRamificationGroup F M 1 = ⊤ := by
  first | exact @GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent | exact GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent | (intros; apply GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent <;> assumption)
