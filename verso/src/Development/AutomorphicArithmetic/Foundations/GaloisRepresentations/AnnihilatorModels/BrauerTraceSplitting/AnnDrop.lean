import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts

noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison.Br

/- English proof (translation)
Introduce `F G B C _ _ _ _ _ _ σ φ s ψ e hσ hφ hψ V _ _ V₀ _ _ i act ρ hρ f q n N A T hT hrel x hx`. Rewrite `hx` using `[mem_Dinv]`. Establish `hpow : ∀ (m : ℕ) (b : B), e ((φ.toLinearMap ^ m) b) = (ψ.toLinearMap ^ m) (e b)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro b`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `b`. Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]`.

Conclude with `hφ _`. Set `Φ : V₀ ⊗[F] B ≃ₗ[F] V ⊗[F] C` to `TensorProduct.congr i.symm e.toLinearEquiv`. Establish `hcomm : ∀ (a : End F V₀) (a' : End F V) (b : End F B) (b' : End F C), (∀ v, i.symm (a v) = a' (i.symm v)) → (∀ y, e (b y) = b' (e y)) → ∀ z, Φ (AlgebraTensorModule.map a b z) = TensorProduct.map a' b' (Φ z)`. Introduce `a a' b b' ha hb z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v y`. Simplify using `only [Φ, AlgebraTensorModule.map_tmul, TensorProduct.congr_tmul, TensorProduct.map_tmul]`. Rewrite using `[ha v]`. Use `congr 1`.

Conclude with `hb y`. Consider the case `add u w hu hw => simp only [map_add, hu, hw]`. Establish `hinv : ∀ g, TensorProduct.map (act g) (s g).toLinearMap (Φ x) = Φ x`. Introduce `g`. Rewrite using `[← hcomm (ρ g) (act g) (σ g) (s g).toLinearMap ?_ (hσ g) x, hx g]`.

Introduce `v`. Establish `h` using `hρ g (i.symm v)`. Rewrite `h` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[h, LinearEquiv.symm_apply_apply]`. Establish `hsum` using `hrel (Φ x) hinv`.

Establish `hinj : Function.Injective (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (ψ.toLinearMap ^ (f * N)))`. Establish `h0 : Function.Injective (ψ.toLinearMap ^ (f * N))`. Rewrite using `[Module.End.coe_pow]`. Conclude with `Function.Injective.iterate hψ _`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ h0`.

Establish `hz : ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * (q : ℤ) ^ ((j : ℕ).choose 2)) • TensorProduct.map (A j) (ψ.toLinearMap ^ (f * (n - j))) (Φ x) = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, map_sum, ← hsum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul]`.

Use `congr 1`. Rewrite using `[← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, ← Module.End.mul_eq_comp, ← pow_add]`. Use `congr 3`. Expand and normalize the polynomial expressions, which then agree. Apply `Φ.injective` to reduce the goal to its premises.

Rewrite using `[map_zero, map_sum, Finset.sum_range, ← hz]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul]`. Use `congr 1`. Rewrite using `[hcomm (T j) (A j) ((φ.toLinearMap ^ f) ^ (n - (j : ℕ))) (ψ.toLinearMap ^ (f * (n - j))) ?_ ?_ x]`.

Introduce `v`. Establish `h` using `hT j (i.symm v)`. Rewrite `h` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[h, LinearEquiv.symm_apply_apply]`. Introduce `y`.

Rewrite using `[← pow_mul]`. Conclude with `hpow _ y`.
-/
theorem annDrop : AnnDrop := by
  intro F G B C _ _ _ _ _ _ σ φ s ψ e hσ hφ hψ V _ _ V₀ _ _ i act ρ hρ f q n N A T hT hrel x hx
  rw [mem_Dinv] at hx
  have hpow : ∀ (m : ℕ) (b : B), e ((φ.toLinearMap ^ m) b) = (ψ.toLinearMap ^ m) (e b) := by
    intro m
    induction m with
    | zero => intro b; simp
    | succ m ih =>
      intro b
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
      exact hφ _
  let Φ : V₀ ⊗[F] B ≃ₗ[F] V ⊗[F] C := TensorProduct.congr i.symm e.toLinearEquiv
  have hcomm : ∀ (a : End F V₀) (a' : End F V) (b : End F B) (b' : End F C),
      (∀ v, i.symm (a v) = a' (i.symm v)) → (∀ y, e (b y) = b' (e y)) →
      ∀ z, Φ (AlgebraTensorModule.map a b z) = TensorProduct.map a' b' (Φ z) := by
    intro a a' b b' ha hb z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v y =>
      simp only [Φ, AlgebraTensorModule.map_tmul, TensorProduct.congr_tmul, TensorProduct.map_tmul]
      rw [ha v]
      congr 1
      exact hb y
    | add u w hu hw => simp only [map_add, hu, hw]
  have hinv : ∀ g, TensorProduct.map (act g) (s g).toLinearMap (Φ x) = Φ x := by
    intro g
    rw [← hcomm (ρ g) (act g) (σ g) (s g).toLinearMap ?_ (hσ g) x, hx g]
    intro v
    have h := hρ g (i.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  have hsum := hrel (Φ x) hinv
  have hinj : Function.Injective (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (ψ.toLinearMap ^ (f * N))) := by
    have h0 : Function.Injective (ψ.toLinearMap ^ (f * N)) := by
      rw [Module.End.coe_pow]
      exact Function.Injective.iterate hψ _
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ h0
  have hz : ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * (q : ℤ) ^ ((j : ℕ).choose 2)) •
      TensorProduct.map (A j) (ψ.toLinearMap ^ (f * (n - j))) (Φ x) = 0 := by
    apply hinj
    rw [map_zero, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, ← Module.End.mul_eq_comp,
      ← pow_add]
    congr 3
    ring
  apply Φ.injective
  rw [map_zero, map_sum, Finset.sum_range, ← hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  rw [hcomm (T j) (A j) ((φ.toLinearMap ^ f) ^ (n - (j : ℕ))) (ψ.toLinearMap ^ (f * (n - j))) ?_ ?_ x]
  · intro v
    have h := hT j (i.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  · intro y
    rw [← pow_mul]
    exact hpow _ y

end UpperTheory.Gal.crystallineComparison.Br
