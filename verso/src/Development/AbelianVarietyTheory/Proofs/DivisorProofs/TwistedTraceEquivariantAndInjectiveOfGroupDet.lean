import Mathlib

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `h : A.det • v = 0`. Use `congrArg (fun w => A.adjugate *ᵥ w) hv` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec]`. Use function extensionality and compare the values at `i`. Establish `hi` using `congrFun h i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi`. Conclude with `(mul_left_mem_nonZeroDivisors_eq_zero_iff hA).1 hi`.
-/
theorem mulVec_eq_zero_of_det_nonZeroDivisor {n R : Type} [Fintype n] [DecidableEq n]
    [CommRing R] (A : Matrix n n R) (hA : A.det ∈ nonZeroDivisors R) (v : n → R)
    (hv : A *ᵥ v = 0) : v = 0 := by
  have h : A.det • v = 0 := by
    have := congrArg (fun w => A.adjugate *ᵥ w) hv
    simpa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec] using this
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hA).1 hi

/- English proof (translation)
Introduce `H K R _ _ _ _ _ _ st h1 hmul χ u hdet`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `F g`. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, ← hmul, Equiv.coe_mulRight, smul_smul, ← Units.val_mul]`. Use `congr 2`. Rewrite using `[map_mul, mul_inv_rev, mul_inv_cancel_left]`. Introduce `f hf`. Establish `h` using `mulVec_eq_zero_of_det_nonZeroDivisor _ hdet (fun g => (((χ g)⁻¹ : Kˣ) : K) • st g f) (by`.

Use function extensionality and compare the values at `h`. Rewrite using `[Pi.zero_apply, ← hf h]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← hmul, mul_smul_comm, mul_comm])`.

Simplify `congrFun h 1` using `[h1]`. Introduce `F hF h0`. Use `mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.of fun h g : H => st (h * g) u)ᵀ (by rwa [Matrix.det_transpose]) F ?_` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Establish `h2` using `congrArg (st g) h0`.

Rewrite `h2` using `[map_sum, map_zero]`. Establish `h3 : ((χ g : Kˣ) : K) • ∑ h, st (h * g) u * F h = 0`. Rewrite using `[← h2, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hF, ← hmul, smul_mul_assoc, mul_comm]`.

Establish `h4` using `congrArg (fun x => (((χ g)⁻¹ : Kˣ) : K) • x) h3`. Simplify using `only [smul_smul, Units.inv_mul, one_smul, smul_zero] at h4`. Simplify `h4` using `[Matrix.mulVec, dotProduct]`.
-/
theorem twistedTrace_equivariant_and_injective_of_groupDet :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R] (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (u : R), (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R → (∀ (F : R) (g : H), st g (∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) = ((χ g : Kˣ) : K) • ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) ∧ (∀ f : R, (∀ h, ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g (f * st h u) = 0) → f = 0) ∧ (∀ F : H → R, (∀ h g, st g (F h) = ((χ g : Kˣ) : K) • F h) → ∑ h, F h * st h u = 0 → F = 0) := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet
  refine ⟨?_, ?_, ?_⟩
  · intro F g
    rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    rw [map_smul, ← hmul, Equiv.coe_mulRight, smul_smul, ← Units.val_mul]
    congr 2
    rw [map_mul, mul_inv_rev, mul_inv_cancel_left]
  · intro f hf
    have h := mulVec_eq_zero_of_det_nonZeroDivisor _ hdet
      (fun g => (((χ g)⁻¹ : Kˣ) : K) • st g f) (by
        funext h
        rw [Pi.zero_apply, ← hf h]
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, ← hmul, mul_smul_comm, mul_comm])
    simpa [h1] using congrFun h 1
  · intro F hF h0
    refine mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.of fun h g : H => st (h * g) u)ᵀ
      (by rwa [Matrix.det_transpose]) F ?_
    funext g
    have h2 := congrArg (st g) h0
    rw [map_sum, map_zero] at h2
    have h3 : ((χ g : Kˣ) : K) • ∑ h, st (h * g) u * F h = 0 := by
      rw [← h2, Finset.smul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [map_mul, hF, ← hmul, smul_mul_assoc, mul_comm]
    have h4 := congrArg (fun x => (((χ g)⁻¹ : Kˣ) : K) • x) h3
    simp only [smul_smul, Units.inv_mul, one_smul, smul_zero] at h4
    simpa [Matrix.mulVec, dotProduct] using h4

end GlobalTheory
