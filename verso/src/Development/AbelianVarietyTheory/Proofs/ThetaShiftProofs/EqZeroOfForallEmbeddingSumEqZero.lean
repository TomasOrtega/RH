import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `K K₁ _ _ _ _ _ σ₀ n e y hind hrel`. Use `letI : Algebra K ℂ := σ₀.toAlgebra`. Establish `hσ : ∀ x : K, algebraMap K ℂ x = σ₀ x` using `fun _ => rfl`. Set `ω` to `Module.finBasis K K₁`. Establish `hcard : Fintype.card (Fin (Module.finrank K K₁)) = Fintype.card (K₁ →ₐ[K] ℂ)`.

Rewrite using `[AlgHom.card, Fintype.card_fin]`. Set `ε : Fin (Module.finrank K K₁) ≃ (K₁ →ₐ[K] ℂ)` to `Fintype.equivOfCardEq hcard`. Establish `hd` using `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K ℂ ω ε`. Establish `hd0 : Algebra.discr K ω ≠ 0` using `Algebra.discr_not_zero_of_basis K ω`. Establish `hdet : (Algebra.embeddingsMatrixReindex K ℂ ω ε).det ≠ 0`.

Introduce `h`. Rewrite `hd` using `[h, zero_pow two_ne_zero]`. Conclude with `hd0 ((algebraMap K ℂ).injective (by rw [hd, map_zero]))`. Set `u : Fin (Module.finrank K K₁) → ℂ` to `fun s => ∑ b, σ₀ (ω.repr (y b) s) * e b`. Establish `hu : u = 0`.

Apply `Matrix.eq_zero_of_vecMul_eq_zero hdet` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Establish `h1` using `hrel (ε j : K₁ →+* ℂ) (by`. Use extensionality with `x`. Simplify using `[hσ])`.

Establish `h2 : ∀ b, (ε j : K₁ →+* ℂ) (y b) = ∑ s, σ₀ (ω.repr (y b) s) * ε j (ω s)`. Introduce `b`. Use `conv_lhs => rw [← ω.sum_repr (y b)]`. Simplify using `only [RingHom.coe_coe, map_sum, Algebra.smul_def, map_mul, AlgHom.commutes, hσ]`. Simplify using `only [h2, Finset.mul_sum] at h1`.

Rewrite `h1` using `[Finset.sum_comm]`. Simplify using `only [Matrix.vecMul, dotProduct, u, Finset.sum_mul, Pi.zero_apply]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `: Algebra.embeddingsMatrixReindex K ℂ ω ε s j = ε j (ω s)`.

Simplify using `[Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `b`. Apply `ω.repr.injective` to reduce the goal to its premises.

Use extensionality with `s`. Use `congrFun (hind (fun b => ω.repr (y b) s) (congrFun hu s)) b` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_zero_of_forall_embedding_sum_eq_zero :
    ∀ (K K₁ : Type) [Field K] [CharZero K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁] (σ₀ : K →+* ℂ) (n : ℕ) (e : Fin n → ℂ) (y : Fin n → K₁), (∀ c : Fin n → K, ∑ b, σ₀ (c b) * e b = 0 → c = 0) → (∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap K K₁) = σ₀ → ∑ b, e b * σ₁ (y b) = 0) → y = 0 := by
  intro K K₁ _ _ _ _ _ σ₀ n e y hind hrel
  classical
  letI : Algebra K ℂ := σ₀.toAlgebra
  have hσ : ∀ x : K, algebraMap K ℂ x = σ₀ x := fun _ => rfl
  let ω := Module.finBasis K K₁
  have hcard : Fintype.card (Fin (Module.finrank K K₁)) = Fintype.card (K₁ →ₐ[K] ℂ) := by
    rw [AlgHom.card, Fintype.card_fin]
  let ε : Fin (Module.finrank K K₁) ≃ (K₁ →ₐ[K] ℂ) := Fintype.equivOfCardEq hcard
  have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K ℂ ω ε
  have hd0 : Algebra.discr K ω ≠ 0 := Algebra.discr_not_zero_of_basis K ω
  have hdet : (Algebra.embeddingsMatrixReindex K ℂ ω ε).det ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hd
    exact hd0 ((algebraMap K ℂ).injective (by rw [hd, map_zero]))
  let u : Fin (Module.finrank K K₁) → ℂ := fun s => ∑ b, σ₀ (ω.repr (y b) s) * e b
  have hu : u = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    funext j
    have h1 := hrel (ε j : K₁ →+* ℂ) (by
      ext x
      simp [hσ])
    have h2 : ∀ b, (ε j : K₁ →+* ℂ) (y b) = ∑ s, σ₀ (ω.repr (y b) s) * ε j (ω s) := by
      intro b
      conv_lhs => rw [← ω.sum_repr (y b)]
      simp only [RingHom.coe_coe, map_sum, Algebra.smul_def, map_mul, AlgHom.commutes, hσ]
    simp only [h2, Finset.mul_sum] at h1
    rw [Finset.sum_comm] at h1
    simp only [Matrix.vecMul, dotProduct, u, Finset.sum_mul, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ => ?_
    have : Algebra.embeddingsMatrixReindex K ℂ ω ε s j = ε j (ω s) := by
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
    rw [this]; ring
  funext b
  apply ω.repr.injective
  ext s
  have := congrFun (hind (fun b => ω.repr (y b) s) (congrFun hu s)) b
  simpa using this

end GlobalTheory
