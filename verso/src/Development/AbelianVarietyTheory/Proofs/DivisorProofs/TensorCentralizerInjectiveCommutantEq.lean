import Mathlib
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ C _ _ y`. Use `set Z := Subalgebra.centralizer ℚ ({y} : Set C) with hZ`. Establish `hmap : ∀ w', Algebra.TensorProduct.map (AlgHom.id K K) Z.val w' = LinearMap.lTensor K Z.val.toLinearMap w'`. Introduce `w'`. Proceed by induction on `w' using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Set `ad : C →ₗ[ℚ] C` to `LinearMap.mulRight ℚ y - LinearMap.mulLeft ℚ y`. Establish `hex : Function.Exact Z.val.toLinearMap ad`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨⟨x, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.mem_centralizer_iff]`.

Introduce `g hg`. Rewrite `hg` using `[Set.mem_singleton_iff]`. Substitute `hg` using the available equality. Establish `: x * g - g * x = 0` using `by simpa [ad] using hx`. Conclude with `(sub_eq_zero.mp this).symm`.

Introduce and unpack `⟨z, rfl⟩`. Establish `hz` using `z.2`. Rewrite `hz` using `[Subalgebra.mem_centralizer_iff]`. Use `hz y (Set.mem_singleton y)` as an intermediate fact. Simplify using `[ad, this]`.

Establish `hexK` using `Module.Flat.lTensor_exact K hex`. Establish `hadK : ∀ w : K ⊗[ℚ] C, LinearMap.lTensor K ad w = w * ((1 : K) ⊗ₜ[ℚ] y) - ((1 : K) ⊗ₜ[ℚ] y) * w`. Introduce `w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp [ad, TensorProduct.tmul_sub]`. Consider the case `add a b ha hb => rw [map_add, ha, hb, add_mul, mul_add]`. Normalize the expressions using the abelian group laws. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`.

Rewrite `hab` using `[hmap, hmap]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective hab`. Introduce `w hw`. Establish `h0 : LinearMap.lTensor K ad w = 0`. Rewrite using `[hadK, hw.eq, sub_self]`.

Take `⟨w', hw'⟩` from `(hexK w).mp h0`. Conclude with `⟨w', by rw [hmap]; exact hw'⟩`.
-/
theorem tensor_centralizer_flat : ∀ (K : Type) [Field K] [Algebra ℚ K] (C : Type) [Ring C] [Algebra ℚ C] (y : C),
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val) ∧
    ∀ w : K ⊗[ℚ] C, Commute w ((1 : K) ⊗ₜ[ℚ] y) → ∃ w' : K ⊗[ℚ] (Subalgebra.centralizer ℚ ({y} : Set C)),
      Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val w' = w := by
  intro K _ _ C _ _ y
  set Z := Subalgebra.centralizer ℚ ({y} : Set C) with hZ
  have hmap : ∀ w', Algebra.TensorProduct.map (AlgHom.id K K) Z.val w'
      = LinearMap.lTensor K Z.val.toLinearMap w' := by
    intro w'
    induction w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  let ad : C →ₗ[ℚ] C := LinearMap.mulRight ℚ y - LinearMap.mulLeft ℚ y
  have hex : Function.Exact Z.val.toLinearMap ad := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have : x * g - g * x = 0 := by simpa [ad] using hx
      exact (sub_eq_zero.mp this).symm
    · rintro ⟨z, rfl⟩
      have hz := z.2
      rw [Subalgebra.mem_centralizer_iff] at hz
      have := hz y (Set.mem_singleton y)
      simp [ad, this]
  have hexK := Module.Flat.lTensor_exact K hex
  have hadK : ∀ w : K ⊗[ℚ] C, LinearMap.lTensor K ad w = w * ((1 : K) ⊗ₜ[ℚ] y) - ((1 : K) ⊗ₜ[ℚ] y) * w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ad, TensorProduct.tmul_sub]
    | add a b ha hb => rw [map_add, ha, hb, add_mul, mul_add]; abel
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [hmap, hmap] at hab
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective hab
  · intro w hw
    have h0 : LinearMap.lTensor K ad w = 0 := by
      rw [hadK, hw.eq, sub_self]
    obtain ⟨w', hw'⟩ := (hexK w).mp h0
    exact ⟨w', by rw [hmap]; exact hw'⟩

end GlobalTheory
