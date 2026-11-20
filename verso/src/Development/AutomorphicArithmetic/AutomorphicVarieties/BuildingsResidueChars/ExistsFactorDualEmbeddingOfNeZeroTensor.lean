import Mathlib
open scoped TensorProduct

/- English proof (translation)
Introduce `I _ W _ _ _ N _ _ Φ hΦ y`. Use `Fintype.ofFinite I` as an intermediate fact. Establish `hinv` using `PiTensorProduct.dualDistrib_dualDistribInvOfBasis_left_inverse (R := ℂ) (M := W) (fun i => Module.Free.chooseBasis ℂ (W i))`. Establish `hf : ∃ f : ∀ i, Module.Dual ℂ (W i), Φ (PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f)) ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Establish `h0 : Φ ∘ₗ PiTensorProduct.dualDistrib = 0`. Apply `PiTensorProduct.ext` to reduce the goal to its premises. Use extensionality with `f`. Simplify using `using h f`.

Apply `hΦ` to reduce the goal to its premises. Rewrite using `[← LinearMap.comp_id Φ, ← hinv, ← LinearMap.comp_assoc, h0, LinearMap.zero_comp]`. Take `⟨f, hf⟩` from `hf`. Use `⟨PiTensorProduct.dualDistrib ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap f y, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `hf` to reduce the goal to its premises. Use `LinearMap.congr_fun h (f y)` as an intermediate fact. Simplify using `using this`. Introduce `T hT m`. Apply `PiTensorProduct.ext` to reduce the goal to its premises.

Use extensionality with `w`. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod, MultilinearMap.toLinearMap_apply, PiTensorProduct.dualDistrib_apply]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = y`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hi, hT i hi]`.
-/
theorem UpperTheory.exists_factor_dual_embedding_of_ne_zero_tensor :
    ∀ (I : Type) [Finite I] (W : I → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)] (N : Type) [AddCommGroup N] [Module ℂ N] (Φ : Module.Dual ℂ (⨂[ℂ] i, W i) →ₗ[ℂ] N), Φ ≠ 0 → ∀ y : I, ∃ E : Module.Dual ℂ (W y) →ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] i, W i), Φ ∘ₗ E ≠ 0 ∧ ∀ T : ∀ i, W i →ₗ[ℂ] W i, (∀ i, i ≠ y → T i = LinearMap.id) → ∀ m, E m ∘ₗ PiTensorProduct.map T = E (m ∘ₗ T y) := by
  intro I _ W _ _ _ N _ _ Φ hΦ y
  classical
  have := Fintype.ofFinite I
  have hinv := PiTensorProduct.dualDistrib_dualDistribInvOfBasis_left_inverse
    (R := ℂ) (M := W) (fun i => Module.Free.chooseBasis ℂ (W i))
  have hf : ∃ f : ∀ i, Module.Dual ℂ (W i),
      Φ (PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f)) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : Φ ∘ₗ PiTensorProduct.dualDistrib = 0 := by
      apply PiTensorProduct.ext
      ext f
      simpa using h f
    apply hΦ
    rw [← LinearMap.comp_id Φ, ← hinv, ← LinearMap.comp_assoc, h0, LinearMap.zero_comp]
  obtain ⟨f, hf⟩ := hf
  refine ⟨PiTensorProduct.dualDistrib ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap f y, ?_, ?_⟩
  · intro h
    apply hf
    have := LinearMap.congr_fun h (f y)
    simpa using this
  · intro T hT m
    apply PiTensorProduct.ext
    ext w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      PiTensorProduct.map_tprod, MultilinearMap.toLinearMap_apply,
      PiTensorProduct.dualDistrib_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = y
    · subst hi
      simp
    · simp [Function.update_of_ne hi, hT i hi]
