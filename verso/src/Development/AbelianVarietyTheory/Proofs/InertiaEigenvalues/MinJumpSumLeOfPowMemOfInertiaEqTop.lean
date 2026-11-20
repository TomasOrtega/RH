import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperModCommutatorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemUpperRamificationGroupJumpSumNotMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtensionStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Check the signs of the components of the expression. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Reduce the equality to equality of the corresponding arguments. Clear the denominators using the available nonvanishing facts. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem min_jumpSum_le_of_pow_mem_of_inertia_eq_top : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B C : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) ≤ jumpSum (wild F L) ⊤ C := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E B C h0 hE hcomm hpow
  by_cases hB : B = ⊤
  ·
    subst hB
    have hzero : jumpSum (wild F L) ⊤ (⊤ : Subgroup (L ≃ₐ[F] L)) = 0 := by
      simp [jumpSum]
    simp [hzero]
  ·
    obtain ⟨e, he, hEe, hram⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hE
    have hcard : ramificationIndex F L = Nat.card (L ≃ₐ[F] L) := by
      rw [hram, h0]; simp
    have hnpos : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ) := by
      exact_mod_cast Nat.card_pos

    obtain ⟨σ, hσ, hσB⟩ := GlobalTheory.T.exists_mem_upperRamificationGroup_jumpSum_not_mem' F L B h0 hB
    have hv : (0 : ℝ) ≤ (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) := by
      positivity

    obtain ⟨τ, hτ, hτC⟩ := GlobalTheory.T.exists_upper_mem_inv_mul_pow_mem_of_commutator F L p e _ C hcomm hv he σ hσ

    have hτ' : τ ∉ C := by
      intro hτmem
      apply hσB
      apply hpow
      have hsplit : σ ^ p = τ * (τ⁻¹ * σ ^ p) := by group
      rw [hsplit]
      exact C.mul_mem hτmem hτC
    have key := GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem F L C _ h0 τ hτ hτ'
    have hR : ((min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) : ℕ) : ℝ)
        ≤ (jumpSum (wild F L) ⊤ C : ℝ) := by
      refine le_trans (le_of_eq ?_) key
      rw [mul_min_of_nonneg _ _ hnpos.le, hEe, hcard]
      push_cast
      congr 1
      · field_simp
      · field_simp
    exact_mod_cast hR

end GlobalTheory.PMon.Ram
