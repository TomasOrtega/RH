import Mathlib
open TensorProduct

namespace GlobalTheory.CompanionTheory.PerfectFirstCohomology

/- English proof (translation)
Set `e₁` to `AlgebraTensorModule.cancelBaseChange R A K K Q`. Set `e₂` to `AlgebraTensorModule.cancelBaseChange R A K K P`. Establish `comm : ∀ x, e₂ (((d.baseChange A).baseChange K) x) = (d.baseChange K) (e₁ x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul k y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [tmul_add, map_add, hx, hy]`. Consider the case `tmul a q`. Simplify using `[e₁, e₂, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']`. Use `⟨LinearEquiv.ofSubmodules e₁ _ _ ?_⟩` and prove the remaining obligations. Use extensionality with `y`.

Simplify using `only [Submodule.mem_map, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Use `comm x` as an intermediate fact. Rewrite `this` using `[hx, map_zero]`.

Conclude with `this.symm`. Introduce `hy`. Use `⟨e₁.symm y, ?_, by simp⟩` and prove the remaining obligations. Apply `e₂.injective` to reduce the goal to its premises. Rewrite using `[comm, map_zero]`.

Simplify using `using hy`.
-/
theorem ker_baseChange_tower (R A K Q P : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A]
    [Algebra A K] [Algebra R K] [IsScalarTower R A K] [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P) :
    Nonempty (LinearMap.ker ((d.baseChange A).baseChange K) ≃ₗ[K] LinearMap.ker (d.baseChange K)) := by
  let e₁ := AlgebraTensorModule.cancelBaseChange R A K K Q
  let e₂ := AlgebraTensorModule.cancelBaseChange R A K K P
  have comm : ∀ x, e₂ (((d.baseChange A).baseChange K) x) = (d.baseChange K) (e₁ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul k y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul a q =>
        simp [e₁, e₂, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
  refine ⟨LinearEquiv.ofSubmodules e₁ _ _ ?_⟩
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := comm x
    rw [hx, map_zero] at this
    exact this.symm
  · intro hy
    refine ⟨e₁.symm y, ?_, by simp⟩
    apply e₂.injective
    rw [comm, map_zero]
    simpa using hy

end GlobalTheory.CompanionTheory.PerfectFirstCohomology
