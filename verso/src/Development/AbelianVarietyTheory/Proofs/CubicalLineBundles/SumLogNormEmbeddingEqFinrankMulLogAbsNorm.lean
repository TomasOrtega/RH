import Mathlib

open NumberField

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem exists_span_singleton_eq_map_of_integral (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∃ β₀ : 𝓞 M, (β₀ : M) = β ∧ Ideal.span {β₀} = 𝔟.map (algebraMap (𝓞 K) (𝓞 M)) := by
  have hint : IsIntegral ℤ β := by
    have := h₁ 1 (fun b _ => by simpa using RingOfIntegers.isIntegral_coe b)
    simpa using this
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : 𝓞 M, (β₀ : M) = β := ⟨⟨β, hint⟩, rfl⟩
  refine ⟨β₀, hβ₀, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have hone : (1 : K) ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹) := by
      rw [FractionalIdeal.coe_ideal_mul_inv 𝔟 h𝔟]
      exact FractionalIdeal.one_mem_one _
    have key : ∀ r ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹),
        ∃ z ∈ 𝔟.map (algebraMap (𝓞 K) (𝓞 M)), (z : M) = β * algebraMap K M r := by
      intro r hr
      refine FractionalIdeal.mul_induction_on
        (C := fun r => ∃ z ∈ 𝔟.map (algebraMap (𝓞 K) (𝓞 M)), (z : M) = β * algebraMap K M r)
        hr ?_ ?_
      · intro i hi j hj
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have h0 : (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
          FractionalIdeal.coeIdeal_ne_zero.2 h𝔟
        have hj' := (FractionalIdeal.mem_inv_iff h0).1 hj
        have hI : IsIntegral ℤ (β * algebraMap K M j) := by
          refine h₁ j fun c hc => ?_
          obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
            (hj' _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨c, hc, rfl⟩))
          have : j * (c : K) = (w : K) := hw.symm
          rw [this]
          exact RingOfIntegers.isIntegral_coe w
        refine ⟨algebraMap (𝓞 K) (𝓞 M) b * ⟨_, hI⟩,
          Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb), ?_⟩
        change algebraMap K M (b : K) * (β * algebraMap K M j) =
          β * algebraMap K M ((b : K) * j)
        rw [map_mul]; ring
      · rintro x y ⟨z, hz, hx⟩ ⟨w, hw, hy⟩
        refine ⟨z + w, Ideal.add_mem _ hz hw, ?_⟩
        change (z : M) + (w : M) = _
        rw [hx, hy, map_add]; ring
    obtain ⟨z, hz, hz'⟩ := key 1 hone
    have : β₀ = z := by
      apply RingOfIntegers.ext
      rw [hz', hβ₀]; simp
    rw [this]; exact hz
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨⟨_, h₂ y hy⟩, ?_⟩
    apply RingOfIntegers.ext
    change β⁻¹ * algebraMap K M (y : K) * (β₀ : M) = algebraMap K M (y : K)
    rw [hβ₀]
    field_simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem abs_norm_eq_absNorm_pow_of_integral (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    |Algebra.norm ℚ β| = (Ideal.absNorm 𝔟 : ℚ) ^ Module.finrank K M := by
  obtain ⟨β₀, rfl, hspan⟩ := exists_span_singleton_eq_map_of_integral K M 𝔟 β h𝔟 hβ h₁ h₂
  have h := congrArg Ideal.absNorm hspan
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_algebraMap,
    ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 M) M] at h
  rw [← Algebra.coe_norm_int, ← Nat.cast_pow, ← h, Nat.cast_natAbs, Int.cast_abs]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.
-/
theorem sum_log_norm_embedding_eq_finrank_mul_log_absNorm (K M : Type) [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∑ σ : M →+* ℂ, Real.log ‖σ β‖ =
      (Module.finrank K M : ℝ) * Real.log (Ideal.absNorm 𝔟 : ℝ) := by
  have h := abs_norm_eq_absNorm_pow_of_integral K M 𝔟 β h𝔟 hβ h₁ h₂
  have hp : ∏ σ : M →+* ℂ, ‖σ β‖ = ((|Algebra.norm ℚ β| : ℚ) : ℝ) := by
    have h3 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ β)
    rw [norm_prod] at h3
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom M ℂ) (fun σ : M →+* ℂ => ‖σ β‖)
      (fun σ : M →ₐ[ℚ] ℂ => ‖σ β‖) (fun _ => rfl), ← h3]
    simp
  rw [← Real.log_prod (fun σ _ => by simpa using hβ), hp, h]
  push_cast
  rw [Real.log_pow]

end GlobalTheory
