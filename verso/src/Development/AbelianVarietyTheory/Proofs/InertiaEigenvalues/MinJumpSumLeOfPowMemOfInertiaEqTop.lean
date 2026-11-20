import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperModCommutatorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemUpperRamificationGroupJumpSumNotMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtensionStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Introduce `F L _ _ _ _ _ _ _ _ _ _ _ _ p E B C h0 hE hcomm hpow`. Distinguish the cases in `hB : B = ⊤`. Substitute `hB` using the available equality. Establish `hzero : jumpSum (wild F L) ⊤ (⊤ : Subgroup (L ≃ₐ[F] L)) = 0`. Simplify using `[jumpSum]`.

Simplify using `[hzero]`. Take `⟨e, he, hEe, hram⟩` from `GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hE`. Establish `hcard : ramificationIndex F L = Nat.card (L ≃ₐ[F] L)`. Rewrite using `[hram, h0]`. Simplify using the standard rewrite rules.

Establish `hnpos : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ)`. Conclude with `Nat.card_pos` after adjusting the coercions. Take `⟨σ, hσ, hσB⟩` from `GlobalTheory.T.exists_mem_upperRamificationGroup_jumpSum_not_mem' F L B h0 hB`. Establish `hv : (0 : ℝ) ≤ (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ)`. Check the signs of the components of the expression.

Take `⟨τ, hτ, hτC⟩` from `GlobalTheory.T.exists_upper_mem_inv_mul_pow_mem_of_commutator F L p e _ C hcomm hv he σ hσ`. Establish `hτ' : τ ∉ C`. Introduce `hτmem`. Apply `hσB` to reduce the goal to its premises. Apply `hpow` to reduce the goal to its premises.

Establish `hsplit : σ ^ p = τ * (τ⁻¹ * σ ^ p)` using `by group`. Rewrite using `[hsplit]`. Conclude with `C.mul_mem hτmem hτC`. Establish `key` using `GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem F L C _ h0 τ hτ hτ'`. Establish `hR : ((min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) : ℕ) : ℝ) ≤ (jumpSum (wild F L) ⊤ C : ℝ)`.

Use `le_trans (le_of_eq ?_) key` and prove the remaining obligations. Rewrite using `[mul_min_of_nonneg _ _ hnpos.le, hEe, hcard]`. Use `push_cast`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Clear the denominators using the available nonvanishing facts. Conclude with `hR` after adjusting the coercions.
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
