import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `R₀ R _ _ _ N₀ N _ _ _ _ _ _ 𝒩₀ _ 𝒩 _ ψ n θ h hdeg hθ`. Set `p₀ : N₀ →ₗ[R₀] 𝒩₀ n` to `DirectSum.component R₀ ℤ (fun i => 𝒩₀ i) n ∘ₗ (decomposeLinearEquiv 𝒩₀).toLinearMap`. Set `p : N →ₗ[R] 𝒩 n` to `DirectSum.component R ℤ (fun i => 𝒩 i) n ∘ₗ (decomposeLinearEquiv 𝒩).toLinearMap`. Establish `hp₀ : ∀ y, p₀ y = decompose 𝒩₀ y n` using `fun _ => rfl`. Establish `hp : ∀ y, p y = decompose 𝒩 y n` using `fun _ => rfl`.

Establish `hp₀i : ∀ y : 𝒩₀ n, p₀ (y : N₀) = y` using `fun y => by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hp₀]`. Conclude with `decompose_of_mem_same 𝒩₀ y.2`. Establish `hpi : ∀ y : 𝒩 n, p (y : N) = y` using `fun y => by`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hp]`. Conclude with `decompose_of_mem_same 𝒩 y.2`. Establish `hcomm : ∀ y, θ (p₀ y) = p (ψ y)`. Introduce `y`.

Proceed by induction on `y using Decomposition.inductionOn 𝒩₀ with`. Consider the case `zero => simp`. Consider the case `@homogeneous j y`. Distinguish the cases in `hj : j = n`. Substitute `hj` using the available equality.

Rewrite using `[hp₀i, ← hθ, hpi]`. Establish `h1 : p₀ (y : N₀) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hp₀]`. Conclude with `decompose_of_mem_ne 𝒩₀ y.2 hj`.

Establish `h2 : p (ψ y) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hp]`. Conclude with `decompose_of_mem_ne 𝒩 (hdeg j y y.2) hj`. Rewrite using `[h1, h2, map_zero]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Set `L : R ⊗[R₀] 𝒩₀ n →ₗ[R] 𝒩 n` to `LinearMap.liftBaseChange R θ`. Establish `hL1 : ∀ x, L (p₀.baseChange R x) = p (h.equiv x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r y => simp [L, hcomm]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hL2 : ∀ x, (L x : N) = h.equiv ((𝒩₀ n).subtype.baseChange R x)`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r y => simp [L, hθ]`. Consider the case `add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]`. Establish `hret : ∀ x, p₀.baseChange R ((𝒩₀ n).subtype.baseChange R x) = x`.

Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r y => simp [hp₀i]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Establish `hbij : Function.Bijective L`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Establish `h1 : h.equiv ((𝒩₀ n).subtype.baseChange R a) = h.equiv ((𝒩₀ n).subtype.baseChange R b)`. Rewrite using `[← hL2, ← hL2, hab]`.

Rewrite using `[← hret a, h.equiv.injective h1, hret]`. Introduce `z`. Use `⟨p₀.baseChange R (h.equiv.symm z), ?_⟩` and prove the remaining obligations. Rewrite using `[hL1, LinearEquiv.apply_symm_apply, hpi]`. Use `IsBaseChange.of_equiv (LinearEquiv.ofBijective L hbij) fun x => ?_` and prove the remaining obligations.

Simplify using `[L]`.
-/
theorem isBaseChange_gradedPiece : ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ N : Type) [AddCommGroup N₀] [Module R₀ N₀] [AddCommGroup N] [Module R₀ N] [Module R N] [IsScalarTower R₀ R N] (𝒩₀ : ℤ → Submodule R₀ N₀) [Decomposition 𝒩₀] (𝒩 : ℤ → Submodule R N) [Decomposition 𝒩] (ψ : N₀ →ₗ[R₀] N) (n : ℤ) (θ : 𝒩₀ n →ₗ[R₀] 𝒩 n), IsBaseChange R ψ → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → (∀ y, (θ y : N) = ψ y) → IsBaseChange R θ := by
  intro R₀ R _ _ _ N₀ N _ _ _ _ _ _ 𝒩₀ _ 𝒩 _ ψ n θ h hdeg hθ
  let p₀ : N₀ →ₗ[R₀] 𝒩₀ n :=
    DirectSum.component R₀ ℤ (fun i => 𝒩₀ i) n ∘ₗ (decomposeLinearEquiv 𝒩₀).toLinearMap
  let p : N →ₗ[R] 𝒩 n :=
    DirectSum.component R ℤ (fun i => 𝒩 i) n ∘ₗ (decomposeLinearEquiv 𝒩).toLinearMap
  have hp₀ : ∀ y, p₀ y = decompose 𝒩₀ y n := fun _ => rfl
  have hp : ∀ y, p y = decompose 𝒩 y n := fun _ => rfl
  have hp₀i : ∀ y : 𝒩₀ n, p₀ (y : N₀) = y := fun y => by
    apply Subtype.ext
    rw [hp₀]
    exact decompose_of_mem_same 𝒩₀ y.2
  have hpi : ∀ y : 𝒩 n, p (y : N) = y := fun y => by
    apply Subtype.ext
    rw [hp]
    exact decompose_of_mem_same 𝒩 y.2
  have hcomm : ∀ y, θ (p₀ y) = p (ψ y) := by
    intro y
    induction y using Decomposition.inductionOn 𝒩₀ with
    | zero => simp
    | @homogeneous j y =>
      by_cases hj : j = n
      · subst hj
        rw [hp₀i, ← hθ, hpi]
      · have h1 : p₀ (y : N₀) = 0 := by
          apply Subtype.ext
          rw [hp₀]
          exact decompose_of_mem_ne 𝒩₀ y.2 hj
        have h2 : p (ψ y) = 0 := by
          apply Subtype.ext
          rw [hp]
          exact decompose_of_mem_ne 𝒩 (hdeg j y y.2) hj
        rw [h1, h2, map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
  let L : R ⊗[R₀] 𝒩₀ n →ₗ[R] 𝒩 n := LinearMap.liftBaseChange R θ
  have hL1 : ∀ x, L (p₀.baseChange R x) = p (h.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [L, hcomm]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hL2 : ∀ x, (L x : N) = h.equiv ((𝒩₀ n).subtype.baseChange R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [L, hθ]
    | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]
  have hret : ∀ x, p₀.baseChange R ((𝒩₀ n).subtype.baseChange R x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [hp₀i]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hbij : Function.Bijective L := by
    constructor
    · intro a b hab
      have h1 : h.equiv ((𝒩₀ n).subtype.baseChange R a)
          = h.equiv ((𝒩₀ n).subtype.baseChange R b) := by
        rw [← hL2, ← hL2, hab]
      rw [← hret a, h.equiv.injective h1, hret]
    · intro z
      refine ⟨p₀.baseChange R (h.equiv.symm z), ?_⟩
      rw [hL1, LinearEquiv.apply_symm_apply, hpi]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective L hbij) fun x => ?_
  simp [L]

end GlobalTheory
