import Mathlib

open scoped BigOperators
open Matrix

namespace GlobalTheory

/- English proof (translation)
Establish `h1` using `((innerSL ℂ (L (UnitAddTorus.mFourier t))).comp L).hasSum h`. Establish `h2 : HasSum (fun s => if s = t then b t else 0) (0 : ℂ)`. Rewrite `h1` using `[map_zero]`. Use `HasSum.congr_fun h1 fun s => ?_` and prove the remaining obligations. Use `orthonormal_iff_ite.mp hL t s` as an intermediate fact.

Simplify using `only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, this, smul_eq_mul]`. Distinguish the cases in `hs : s = t`. Simplify using `[hs]`. Simplify using `[hs, Ne.symm hs]`. Conclude with `(hasSum_ite_eq t (b t)).unique h2`.
-/
theorem coeff_eq_zero_of_hasSum_mFourier_orthonormal_image {J : Type} [Fintype J] {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (L : C(UnitAddTorus J, ℂ) →L[ℂ] E)
    (hL : Orthonormal ℂ (fun n : J → ℤ => L (UnitAddTorus.mFourier n))) (b : (J → ℤ) → ℂ)
    (h : HasSum (fun s => b s • UnitAddTorus.mFourier s) (0 : C(UnitAddTorus J, ℂ)))
    (t : J → ℤ) : b t = 0 := by
  classical
  have h1 := ((innerSL ℂ (L (UnitAddTorus.mFourier t))).comp L).hasSum h
  have h2 : HasSum (fun s => if s = t then b t else 0) (0 : ℂ) := by
    rw [map_zero] at h1
    refine HasSum.congr_fun h1 fun s => ?_
    have := orthonormal_iff_ite.mp hL t s
    simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, this, smul_eq_mul]
    by_cases hs : s = t
    · simp [hs]
    · simp [hs, Ne.symm hs]
  exact (hasSum_ite_eq t (b t)).unique h2

/- English proof (translation)
Simplify using `only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]`. Rewrite using `[Finset.mul_sum, Complex.exp_sum]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mFourier_coe_eq_exp {J : Type} [Fintype J] (s : J → ℤ) (x : J → ℝ) :
    UnitAddTorus.mFourier s (fun j => (x j : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `J _ b hb h0 t`. Establish `hs : Summable (fun s => b s • UnitAddTorus.mFourier s : (J → ℤ) → C(UnitAddTorus J, ℂ))`. Use `Summable.of_norm ?_` and prove the remaining obligations. Simplify `hb` using `only [norm_smul, UnitAddTorus.mFourier_norm, mul_one]`. Establish `hz : (∑' s, b s • UnitAddTorus.mFourier s : C(UnitAddTorus J, ℂ)) = 0`.

Use extensionality with `y`. Use `choose x hx using fun j => QuotientAddGroup.mk_surjective (y j)`. Establish `hy : y = fun j => (x j : UnitAddCircle)` using `funext fun j => (hx j).symm`. Establish `h1` using `((ContinuousMap.evalCLM ℂ y).hasSum hs.hasSum).tsum_eq`. Simplify using `only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul] at h1`.

Rewrite using `[← h1, hy]`. Simplify using `only [mFourier_coe_eq_exp]`. Simplify using `using h0 x`. Establish `hsum` using `hs.hasSum`. Rewrite `hsum` using `[hz]`.

Conclude with `coeff_eq_zero_of_hasSum_mFourier_orthonormal_image _ UnitAddTorus.orthonormal_mFourier b hsum t`.
-/
theorem coeff_eq_zero_of_fourier_series_eq_zero :
    ∀ (J : Type) [Fintype J] (b : (J → ℤ) → ℂ), (Summable fun s => ‖b s‖) →
      (∀ x : J → ℝ, ∑' s, b s *
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) = 0) →
      ∀ s, b s = 0 := by
  intro J _ b hb h0 t
  have hs : Summable (fun s => b s • UnitAddTorus.mFourier s : (J → ℤ) → C(UnitAddTorus J, ℂ)) := by
    refine Summable.of_norm ?_
    simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using hb
  have hz : (∑' s, b s • UnitAddTorus.mFourier s : C(UnitAddTorus J, ℂ)) = 0 := by
    ext y
    choose x hx using fun j => QuotientAddGroup.mk_surjective (y j)
    have hy : y = fun j => (x j : UnitAddCircle) := funext fun j => (hx j).symm
    have h1 := ((ContinuousMap.evalCLM ℂ y).hasSum hs.hasSum).tsum_eq
    simp only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul] at h1
    rw [← h1, hy]
    simp only [mFourier_coe_eq_exp]
    simpa using h0 x
  have hsum := hs.hasSum
  rw [hz] at hsum
  exact coeff_eq_zero_of_hasSum_mFourier_orthonormal_image _ UnitAddTorus.orthonormal_mFourier b hsum t

end GlobalTheory
