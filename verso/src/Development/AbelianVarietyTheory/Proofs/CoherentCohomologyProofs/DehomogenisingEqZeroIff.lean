import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `ι _ _ R _ M _ _ _ _ ℳ _ _ i B _ π P _ _ ε hπ hker y`. Establish `hkill : ∀ w : M, ε ((X i - 1 : MvPolynomial ι R) • w) = 0`. Introduce `w`. Rewrite using `[ε.map_smulₛₗ, map_sub, hπ, map_one, sub_self, zero_smul]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Take `⟨n₀, hn⟩` from `exists_homogeneous_add_X_sub_one_smul ℳ i y`. Take `⟨y', hy', w, rfl⟩` from `hn n₀ le_rfl`. Establish `hε : ε y' = 0`. Rewrite `hy` using `[map_add, hkill, add_zero]`. Then use the resulting hypothesis.

Take `⟨k, hk⟩` from `hker n₀ y' hy' hε`. Use `⟨w - (∑ j ∈ Finset.range k, (X i : MvPolynomial ι R) ^ j) • y', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, smul_smul, mul_geom_sum, sub_smul ((X i : MvPolynomial ι R) ^ k), hk, one_smul]`. Normalize the expressions using the abelian group laws. Introduce and unpack `⟨w, rfl⟩`.

Conclude with `hkill w`.
-/
theorem dehomogenising_eq_zero_iff : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) (B : Type) [CommRing B] (π : MvPolynomial ι R →+* B) (P : Type) [AddCommGroup P] [Module B P] (ε : M →ₛₗ[π] P), π (X i) = 1 → (∀ n, ∀ y ∈ ℳ n, ε y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) → ∀ y, ε y = 0 ↔ ∃ w : M, y = (X i - 1 : MvPolynomial ι R) • w := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i B _ π P _ _ ε hπ hker y
  have hkill : ∀ w : M, ε ((X i - 1 : MvPolynomial ι R) • w) = 0 := by
    intro w
    rw [ε.map_smulₛₗ, map_sub, hπ, map_one, sub_self, zero_smul]
  constructor
  · intro hy
    obtain ⟨n₀, hn⟩ := exists_homogeneous_add_X_sub_one_smul ℳ i y
    obtain ⟨y', hy', w, rfl⟩ := hn n₀ le_rfl
    have hε : ε y' = 0 := by
      rwa [map_add, hkill, add_zero] at hy
    obtain ⟨k, hk⟩ := hker n₀ y' hy' hε
    refine ⟨w - (∑ j ∈ Finset.range k, (X i : MvPolynomial ι R) ^ j) • y', ?_⟩
    rw [smul_sub, smul_smul, mul_geom_sum, sub_smul ((X i : MvPolynomial ι R) ^ k), hk, one_smul]
    abel
  · rintro ⟨w, rfl⟩
    exact hkill w

end GlobalTheory
