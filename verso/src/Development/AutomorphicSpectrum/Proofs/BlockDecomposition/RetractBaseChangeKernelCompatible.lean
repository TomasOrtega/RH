import Mathlib

open TensorProduct

namespace GlobalTheory.CompanionTheory.Retract

/- English proof (translation)
Introduce `R R' M A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ _ _ _ i j d₀ d' E₀ E₁ e hji hcomm hfree hker`. Establish `htm : ∀ r : R', r • E₀ (1 ⊗ₜ e) = E₀ (r ⊗ₜ[R] e)`. Introduce `r`. Rewrite using `[← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `hinjR : ∀ r : R', r ⊗ₜ[R] e = 0 → r = 0`.

Introduce `r hr`. Apply `hfree` to reduce the goal to its premises. Rewrite using `[htm, hr, map_zero]`. Establish `hkerR : ∀ y : R' ⊗[R] A₀, d₀.baseChange R' y = 0 → ∃ r : R', r ⊗ₜ[R] e = y`. Introduce `y hy`.

Take `⟨r, hr⟩` from `hker (E₀ y) (by rw [← hcomm, hy, map_zero])`. Conclude with `⟨r, E₀.injective (by rw [← htm, hr])⟩`. Establish `hji' : ∀ m : M, j (i m) = m` using `fun m => by`. Rewrite using `[← LinearMap.comp_apply, hji, LinearMap.id_apply]`. Establish `hret : ∀ x : M ⊗[R] A₀, j.rTensor A₀ (i.rTensor A₀ x) = x`.

Introduce `x`. Rewrite using `[← LinearMap.rTensor_comp_apply, hji, LinearMap.rTensor_id_apply]`. Establish `hnat : ∀ x : M ⊗[R] A₀, d₀.baseChange R' (i.rTensor A₀ x) = i.rTensor A₁ (d₀.lTensor M x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul m a => simp [LinearMap.baseChange_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `m m' h`.

Establish `h0 : m ⊗ₜ[R] e = m' ⊗ₜ[R] e` using `h`. Establish `h1 : (i m - i m') ⊗ₜ[R] e = 0`. Establish `h2` using `congrArg (i.rTensor A₀) h0`. Simplify using `only [LinearMap.rTensor_tmul] at h2`. Rewrite using `[TensorProduct.sub_tmul, h2, sub_self]`.

Establish `h3 : i m = i m'` using `sub_eq_zero.mp (hinjR _ h1)`. Rewrite using `[← hji' m, ← hji' m', h3]`. Introduce `x hx`. Take `⟨r, hr⟩` from `hkerR (i.rTensor A₀ x) (by rw [hnat, hx, map_zero])`. Use `⟨j r, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hret x, ← hr, LinearMap.rTensor_tmul]`.
-/
theorem constants_of_retract :
    ∀ (R R' M A₀ A₁ B₀ B₁ : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup B₀] [Module R' B₀] [AddCommGroup B₁] [Module R' B₁] (i : M →ₗ[R] R') (j : R' →ₗ[R] M) (d₀ : A₀ →ₗ[R] A₁) (d' : B₀ →ₗ[R'] B₁) (E₀ : R' ⊗[R] A₀ ≃ₗ[R'] B₀) (E₁ : R' ⊗[R] A₁ ≃ₗ[R'] B₁) (e : A₀), j ∘ₗ i = LinearMap.id → (∀ x, E₁ (d₀.baseChange R' x) = d' (E₀ x)) → (∀ r : R', r • E₀ (1 ⊗ₜ e) = 0 → r = 0) → (∀ z, d' z = 0 → ∃ r : R', r • E₀ (1 ⊗ₜ e) = z) → Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x := by
  intro R R' M A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ _ _ _ i j d₀ d' E₀ E₁ e hji hcomm hfree hker
  have htm : ∀ r : R', r • E₀ (1 ⊗ₜ e) = E₀ (r ⊗ₜ[R] e) := by
    intro r
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hinjR : ∀ r : R', r ⊗ₜ[R] e = 0 → r = 0 := by
    intro r hr
    apply hfree
    rw [htm, hr, map_zero]
  have hkerR : ∀ y : R' ⊗[R] A₀, d₀.baseChange R' y = 0 → ∃ r : R', r ⊗ₜ[R] e = y := by
    intro y hy
    obtain ⟨r, hr⟩ := hker (E₀ y) (by rw [← hcomm, hy, map_zero])
    exact ⟨r, E₀.injective (by rw [← htm, hr])⟩
  have hji' : ∀ m : M, j (i m) = m := fun m => by
    rw [← LinearMap.comp_apply, hji, LinearMap.id_apply]
  have hret : ∀ x : M ⊗[R] A₀, j.rTensor A₀ (i.rTensor A₀ x) = x := by
    intro x
    rw [← LinearMap.rTensor_comp_apply, hji, LinearMap.rTensor_id_apply]
  have hnat : ∀ x : M ⊗[R] A₀,
      d₀.baseChange R' (i.rTensor A₀ x) = i.rTensor A₁ (d₀.lTensor M x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m a => simp [LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨?_, ?_⟩
  · intro m m' h
    have h0 : m ⊗ₜ[R] e = m' ⊗ₜ[R] e := h
    have h1 : (i m - i m') ⊗ₜ[R] e = 0 := by
      have h2 := congrArg (i.rTensor A₀) h0
      simp only [LinearMap.rTensor_tmul] at h2
      rw [TensorProduct.sub_tmul, h2, sub_self]
    have h3 : i m = i m' := sub_eq_zero.mp (hinjR _ h1)
    rw [← hji' m, ← hji' m', h3]
  · intro x hx
    obtain ⟨r, hr⟩ := hkerR (i.rTensor A₀ x) (by rw [hnat, hx, map_zero])
    refine ⟨j r, ?_⟩
    rw [← hret x, ← hr, LinearMap.rTensor_tmul]

end GlobalTheory.CompanionTheory.Retract
