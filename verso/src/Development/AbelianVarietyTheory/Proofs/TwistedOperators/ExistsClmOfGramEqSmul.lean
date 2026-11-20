import Mathlib
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Set `Φ : (α →₀ ℂ) →ₗ[ℂ] Hs` to `Finsupp.linearCombination ℂ u`. Set `Ψ : (α →₀ ℂ) →ₗ[ℂ] E` to `Finsupp.linearCombination ℂ f`. Establish `hinner : ∀ z w : α →₀ ℂ, ⟪Ψ z, Ψ w⟫_ℂ = (K : ℂ) * ⟪Φ z, Φ w⟫_ℂ`. Introduce `z w`. Proceed by induction on `z using Finsupp.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add z₁ z₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `single a c`. Proceed by induction on `w using Finsupp.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add w₁ w₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `single b d`. Simplify using `only [Φ, Ψ, Finsupp.linearCombination_single, inner_smul_left, inner_smul_right, hK]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnorm : ∀ z, ‖Ψ z‖ ^ 2 = K * ‖Φ z‖ ^ 2`. Introduce `z`. Establish `h` using `hinner z z`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Simplify using `using h`. Establish `hbound : ∀ z, ‖Ψ z‖ ≤ Real.sqrt (max K 0) * ‖Φ z‖`. Introduce `z`.

Establish `hs : Real.sqrt (max K 0) ^ 2 = max K 0` using `Real.sq_sqrt (le_max_right _ _)`. Establish `h0 : 0 ≤ Real.sqrt (max K 0)` using `Real.sqrt_nonneg _`. Establish `h1 : ‖Ψ z‖ ^ 2 ≤ (Real.sqrt (max K 0) * ‖Φ z‖) ^ 2`. Rewrite using `[mul_pow, hs, hnorm]`. Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)`.

Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _)) two_ne_zero).1 h1`. Establish `hdense : DenseRange Φ`. Establish `hr : Set.range Φ = (Submodule.span ℂ (Set.range u) : Set Hs)`. Rewrite using `[← LinearMap.coe_range]`. Conclude with `congrArg _ (Finsupp.range_linearCombination ℂ)`.

Rewrite using `[DenseRange, hr]`. Conclude with `hd`. Use `⟨Ψ.extendOfNorm Φ, fun a => ?_⟩` and prove the remaining obligations. Establish `h` using `LinearMap.extendOfNorm_eq hdense ⟨_, hbound⟩ (Finsupp.single a 1)`. Simplify `h` using `[Φ, Ψ, Finsupp.linearCombination_single]`.
-/
theorem exists_clm_of_gram_eq_smul {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E)
    (K : ℝ) (hK : ∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range u) : Set Hs)) :
    ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by
  classical
  let Φ : (α →₀ ℂ) →ₗ[ℂ] Hs := Finsupp.linearCombination ℂ u
  let Ψ : (α →₀ ℂ) →ₗ[ℂ] E := Finsupp.linearCombination ℂ f
  have hinner : ∀ z w : α →₀ ℂ, ⟪Ψ z, Ψ w⟫_ℂ = (K : ℂ) * ⟪Φ z, Φ w⟫_ℂ := by
    intro z w
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]; ring
    | single a c =>
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add w₁ w₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]; ring
      | single b d =>
        simp only [Φ, Ψ, Finsupp.linearCombination_single, inner_smul_left, inner_smul_right, hK]
        ring
  have hnorm : ∀ z, ‖Ψ z‖ ^ 2 = K * ‖Φ z‖ ^ 2 := by
    intro z
    have h := hinner z z
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    simpa using h
  have hbound : ∀ z, ‖Ψ z‖ ≤ Real.sqrt (max K 0) * ‖Φ z‖ := by
    intro z
    have hs : Real.sqrt (max K 0) ^ 2 = max K 0 := Real.sq_sqrt (le_max_right _ _)
    have h0 : 0 ≤ Real.sqrt (max K 0) := Real.sqrt_nonneg _
    have h1 : ‖Ψ z‖ ^ 2 ≤ (Real.sqrt (max K 0) * ‖Φ z‖) ^ 2 := by
      rw [mul_pow, hs, hnorm]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _)) two_ne_zero).1 h1
  have hdense : DenseRange Φ := by
    have hr : Set.range Φ = (Submodule.span ℂ (Set.range u) : Set Hs) := by
      rw [← LinearMap.coe_range]
      exact congrArg _ (Finsupp.range_linearCombination ℂ)
    rw [DenseRange, hr]
    exact hd
  refine ⟨Ψ.extendOfNorm Φ, fun a => ?_⟩
  have h := LinearMap.extendOfNorm_eq hdense ⟨_, hbound⟩ (Finsupp.single a 1)
  simpa [Φ, Ψ, Finsupp.linearCombination_single] using h
end GlobalTheory
