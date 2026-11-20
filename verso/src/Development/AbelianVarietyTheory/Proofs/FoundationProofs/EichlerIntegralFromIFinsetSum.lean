import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerSum

/- English proof (translation)
Establish `hd` using `(UpperHalfPlane.mdifferentiable_iff.mp hf).continuousOn`. Apply `ContinuousOn.intervalIntegrable` to reduce the goal to its premises. Establish `hmap : Set.MapsTo (fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (Set.uIcc 0 1) {z : ℂ | 0 < z.im}`. Introduce `t ht`. Rewrite `ht` using `[Set.uIcc_of_le zero_le_one]`.

Take `⟨h0, h1⟩` from `ht`. Establish `hτ` using `τ.im_pos`. Simplify using `only [Set.mem_setOf_eq, Complex.add_im, Complex.I_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.sub_re, Complex.I_re, zero_mul, add_zero]`. Rewrite using `[UpperHalfPlane.coe_im]`. Break down `eq_or_lt_of_le h1 with h | h` into its components or cases.

Substitute `h` using the available equality. Use the polynomial consequences of the given equalities and inequalities. Use polynomial arithmetic with `[mul_nonneg h0 hτ.le]`. Establish `hc : ContinuousOn (fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (Set.uIcc 0 1)` using `by fun_prop`. Use `ContinuousOn.mul (ContinuousOn.mul (hd.comp hc hmap) ?_) continuousOn_const` and prove the remaining obligations.

Use `fun_prop`.
-/
theorem eichler_integrand_intervalIntegrable {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (τ : ℍ) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ k * ((τ : ℂ) - Complex.I)) MeasureTheory.volume 0 1 := by
  have hd := (UpperHalfPlane.mdifferentiable_iff.mp hf).continuousOn
  apply ContinuousOn.intervalIntegrable
  have hmap : Set.MapsTo (fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (Set.uIcc 0 1) {z : ℂ | 0 < z.im} := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    obtain ⟨h0, h1⟩ := ht
    have hτ := τ.im_pos
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.I_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.sub_re, Complex.I_re, zero_mul, add_zero]
    rw [UpperHalfPlane.coe_im]
    rcases eq_or_lt_of_le h1 with h | h
    · subst h; nlinarith
    · nlinarith [mul_nonneg h0 hτ.le]
  have hc : ContinuousOn (fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (Set.uIcc 0 1) := by fun_prop
  refine ContinuousOn.mul (ContinuousOn.mul (hd.comp hc hmap) ?_) continuousOn_const
  fun_prop

/- English proof (translation)
Unfold `eichler`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, ← map_sum, ← Finset.mul_sum, ← intervalIntegral.integral_finset_sum fun i _ => eichler_integrand_intervalIntegrable (hg i) τ (w - j)]`. Use `congr 4`.

Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp_apply, Finset.sum_apply, Finset.sum_mul]`.
-/
theorem eichler_finset_sum (w : ℕ) {ι : Type} [Fintype ι] (g : ι → ℍ → ℂ)
    (hg : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g i)) (τ : ℍ) :
    eichler w (∑ i, g i) τ = ∑ i, eichler w (g i) τ := by
  unfold eichler
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, ← map_sum, ← Finset.mul_sum,
    ← intervalIntegral.integral_finset_sum fun i _ => eichler_integrand_intervalIntegrable (hg i) τ (w - j)]
  congr 4
  funext t
  simp only [Function.comp_apply, Finset.sum_apply, Finset.sum_mul]

end GlobalTheory.EichlerSum
