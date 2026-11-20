import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

open IsLocalRing

/- English proof (translation)
Introduce `Λ T _ _ _ _ _ hreg P hP`. Establish `hP' : P.IsPrime` using `hP.1.1`. Establish `hbot : P.comap (algebraMap Λ T) = ⊥`. Use `(Submodule.eq_bot_iff _).2 fun a ha => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Conclude with `Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) ha (hreg a hne)`. Use `⟨hbot, fun p hp => ?_, ?_⟩` and prove the remaining obligations. Take `⟨Q, hQ, hQp, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral p P (by rw [hbot]; exact bot_le)`. Conclude with `⟨Q, hQ, hQp, hQc⟩`. Use `haveI : FaithfulSMul Λ (T ⧸ P) := by`.

Rewrite using `[faithfulSMul_iff_algebraMap_injective]`. Introduce `a b hab`. Rewrite `hab` using `[IsScalarTower.algebraMap_apply Λ T (T ⧸ P), IsScalarTower.algebraMap_apply Λ T (T ⧸ P)]`. Establish `hm : Ideal.Quotient.mk P (algebraMap Λ T a) = Ideal.Quotient.mk P (algebraMap Λ T b)` using `hab`. Establish `h1 : algebraMap Λ T a - algebraMap Λ T b ∈ P` using `Ideal.Quotient.eq.1 hm`.

Establish `h2 : a - b ∈ P.comap (algebraMap Λ T)`. Rewrite using `[Ideal.mem_comap, map_sub]`. Conclude with `h1`. Rewrite `h2` using `[hbot, Submodule.mem_bot, sub_eq_zero]`. Conclude with `h2`.

Conclude with `GlobalTheory.ringKrullDim_eq_of_isIntegral Λ (T ⧸ P)`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.component :
    ∀ (Λ T : Type) [CommRing Λ] [IsDomain Λ] [CommRing T] [Algebra Λ T] [Algebra.IsIntegral Λ T], (∀ a : Λ, a ≠ 0 → algebraMap Λ T a ∈ nonZeroDivisors T) → ∀ P ∈ minimalPrimes T, P.comap (algebraMap Λ T) = ⊥ ∧ (∀ p : Ideal Λ, p.IsPrime → ∃ Q : Ideal T, P ≤ Q ∧ Q.IsPrime ∧ Q.comap (algebraMap Λ T) = p) ∧ ringKrullDim (T ⧸ P) = ringKrullDim Λ := by
  intro Λ T _ _ _ _ _ hreg P hP
  have hP' : P.IsPrime := hP.1.1
  have hbot : P.comap (algebraMap Λ T) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun a ha => ?_
    by_contra hne
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) ha (hreg a hne)
  refine ⟨hbot, fun p hp => ?_, ?_⟩
  · obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p P (by rw [hbot]; exact bot_le)
    exact ⟨Q, hQ, hQp, hQc⟩
  · haveI : FaithfulSMul Λ (T ⧸ P) := by
      rw [faithfulSMul_iff_algebraMap_injective]
      intro a b hab
      rw [IsScalarTower.algebraMap_apply Λ T (T ⧸ P), IsScalarTower.algebraMap_apply Λ T (T ⧸ P)] at hab
      have hm : Ideal.Quotient.mk P (algebraMap Λ T a) = Ideal.Quotient.mk P (algebraMap Λ T b) := hab
      have h1 : algebraMap Λ T a - algebraMap Λ T b ∈ P := Ideal.Quotient.eq.1 hm
      have h2 : a - b ∈ P.comap (algebraMap Λ T) := by
        rw [Ideal.mem_comap, map_sub]
        exact h1
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at h2
      exact h2
    exact GlobalTheory.ringKrullDim_eq_of_isIntegral Λ (T ⧸ P)
