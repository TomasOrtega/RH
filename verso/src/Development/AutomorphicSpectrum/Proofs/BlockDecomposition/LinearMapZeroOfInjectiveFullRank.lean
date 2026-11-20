import Mathlib
open TensorProduct

namespace GlobalTheory.CompanionTheory.Perf

/- English proof (translation)
Introduce `A W N _ _ _ _ _ _ _ _ _ g φ f hg hφ hf`. Set `e : W ≃ₗ[A] (Fin g → A)` to `(Module.finBasisOfFinrankEq A W hg).equivFun`. Set `M : Matrix (Fin g) (Fin g) A` to `LinearMap.toMatrix' (e.toLinearMap ∘ₗ φ)`. Establish `hM : ∀ v, Matrix.mulVec M v = e (φ v)` using `fun v => by`. Express the relevant statement in the definitionally equal form `Matrix.toLin' M v = _`.

Rewrite using `[Matrix.toLin'_toMatrix']`. Both sides reduce to the same expression. Establish `hinj : Function.Injective M.mulVec`. Introduce `v v' h`. Rewrite `h` using `[hM, hM]`.

Conclude with `hφ (e.injective h)`. Establish `hdet : M.det ∈ nonZeroDivisors A` using `Matrix.nonsingular_iff_det_mem_nonZeroDivisors.mp (Matrix.Nonsingular.of_linearIndependent_col (Matrix.mulVec_injective_iff.mp hinj))`. Establish `hkill : ∀ w, M.det • f w = 0`. Introduce `w`. Establish `h1 : φ (M.cramer (e w)) = M.det • w`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[← hM, Matrix.mulVec_cramer, map_smul]`. Rewrite using `[← map_smul, ← h1]`. Conclude with `LinearMap.congr_fun hf _`. Use extensionality with `w`.

Apply `(Module.Free.chooseBasis A N).repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Establish `h2` using `congrArg (fun n => (Module.Free.chooseBasis A N).repr n i) (hkill w)`. Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h2`. Simplify using `using (mul_left_mem_nonZeroDivisors_eq_zero_iff hdet).mp h2`.
-/
theorem map_eq_zero_of_comp_injective_of_finrank_eq :
    ∀ (A W N : Type) [CommRing A] [Nontrivial A] [AddCommGroup W] [Module A W] [AddCommGroup N]
      [Module A N] [Module.Free A W] [Module.Finite A W] [Module.Free A N] (g : ℕ)
      (φ : (Fin g → A) →ₗ[A] W) (f : W →ₗ[A] N),
      Module.finrank A W = g → Function.Injective φ → f ∘ₗ φ = 0 → f = 0 := by
  intro A W N _ _ _ _ _ _ _ _ _ g φ f hg hφ hf
  classical
  let e : W ≃ₗ[A] (Fin g → A) := (Module.finBasisOfFinrankEq A W hg).equivFun
  let M : Matrix (Fin g) (Fin g) A := LinearMap.toMatrix' (e.toLinearMap ∘ₗ φ)
  have hM : ∀ v, Matrix.mulVec M v = e (φ v) := fun v => by
    change Matrix.toLin' M v = _
    rw [Matrix.toLin'_toMatrix']
    rfl
  have hinj : Function.Injective M.mulVec := by
    intro v v' h
    rw [hM, hM] at h
    exact hφ (e.injective h)
  have hdet : M.det ∈ nonZeroDivisors A :=
    Matrix.nonsingular_iff_det_mem_nonZeroDivisors.mp
      (Matrix.Nonsingular.of_linearIndependent_col (Matrix.mulVec_injective_iff.mp hinj))
  have hkill : ∀ w, M.det • f w = 0 := by
    intro w
    have h1 : φ (M.cramer (e w)) = M.det • w := by
      apply e.injective
      rw [← hM, Matrix.mulVec_cramer, map_smul]
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun hf _
  ext w
  apply (Module.Free.chooseBasis A N).repr.injective
  ext i
  have h2 := congrArg (fun n => (Module.Free.chooseBasis A N).repr n i) (hkill w)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply] at h2
  simpa using (mul_left_mem_nonZeroDivisors_eq_zero_iff hdet).mp h2

end GlobalTheory.CompanionTheory.Perf
