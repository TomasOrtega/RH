import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

/- English proof (translation)
Introduce `w g p z hp hz`. Establish `hn : p.natDegree < w + 1`. Break down `eq_or_ne p 0 with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Conclude with `(natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)`.

Establish `hs : slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i • ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i * (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i))`. Simplify using `[slP, LinearMap.sum_apply, LinearMap.toSpanSingleton_apply]`. Rewrite using `[hs, eval_finset_sum, eval_eq_sum_range' hn, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ w` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`.

Simplify using `only [eval_smul, eval_mul, eval_pow, eval_add, eval_C, eval_X, smul_eq_mul]`. Rewrite using `[div_pow, ← Nat.sub_add_cancel hi', pow_add]`. Rewrite using `[Nat.sub_add_cancel hi']`. Establish `hD : ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ i ≠ 0` using `pow_ne_zero _ hz`. Establish `e` using `mul_inv_cancel₀ hD`.

Take the linear combination `(-(p.coeff i * ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) ^ i * ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ (w - i))) * e`.
-/
theorem eval_polySlash : ∀ (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (z : ℂ), p ∈ degreeLT ℂ (w + 1) → ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ≠ 0 → (slP w g p).eval z = ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ w * p.eval (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))) := by
  intro w g p z hp hz
  have hn : p.natDegree < w + 1 := by
    rcases eq_or_ne p 0 with rfl | h
    · simp
    · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)
  have hs : slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
    simp [slP, LinearMap.sum_apply, LinearMap.toSpanSingleton_apply]
  rw [hs, eval_finset_sum, eval_eq_sum_range' hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [eval_smul, eval_mul, eval_pow, eval_add, eval_C, eval_X, smul_eq_mul]
  rw [div_pow, ← Nat.sub_add_cancel hi', pow_add]
  rw [Nat.sub_add_cancel hi']
  have hD : ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ i ≠ 0 := pow_ne_zero _ hz
  have e := mul_inv_cancel₀ hD
  linear_combination (-(p.coeff i * ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) ^ i *
    ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ (w - i))) * e

end GlobalTheory.HeckeFamilyMatrices
