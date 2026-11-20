import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LFunctionConj

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Unfold `ramp`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]`. Use `congr 2`.

Conclude with `MulChar.star_apply' χ (n : ZMod N)`.
-/
theorem Gchi_conj_ramp {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (starRingEnd ℂ) (ramp (fun n => χ n) y) = ramp (fun n => χ⁻¹ n) y := by
  unfold ramp
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
  congr 2
  exact MulChar.star_apply' χ (n : ZMod N)

/- English proof (translation)
Use function extensionality and compare the values at `s`. Establish `h` using `LFunction_conj χ ((starRingEnd ℂ) s)`. Rewrite `h` using `[Complex.conj_conj]`. Simplify using `only [Function.comp_apply]`. Conclude with `h`.
-/
theorem Gchi_conj_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.LFunction χ⁻¹ =
      (starRingEnd ℂ) ∘ DirichletCharacter.LFunction χ ∘ (starRingEnd ℂ) := by
  funext s
  have h := LFunction_conj χ ((starRingEnd ℂ) s)
  rw [Complex.conj_conj] at h
  simp only [Function.comp_apply]
  exact h

/- English proof (translation)
Distinguish the cases in `hf : DifferentiableAt ℂ f x`. Conclude with `hf.hasDerivAt.conj_conj.deriv`. Establish `hg : ¬ DifferentiableAt ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) ((starRingEnd ℂ) x)`. Rewrite using `[differentiableAt_conj_conj_iff, Complex.conj_conj]`. Conclude with `hf`.

Rewrite using `[deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hg, map_zero]`.
-/
private theorem deriv_conj_comp_conj (f : ℂ → ℂ) (x : ℂ) :
    deriv ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) ((starRingEnd ℂ) x) =
      (starRingEnd ℂ) (deriv f x) := by
  by_cases hf : DifferentiableAt ℂ f x
  · exact hf.hasDerivAt.conj_conj.deriv
  · have hg : ¬ DifferentiableAt ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) ((starRingEnd ℂ) x) := by
      rw [differentiableAt_conj_conj_iff, Complex.conj_conj]
      exact hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hg, map_zero]

/- English proof (translation)
Distinguish the cases in `h1 : χ = 1`. Substitute `h1` using the available equality. Simplify using `only [Gchi, inv_one, if_true]`. Rewrite using `[map_add, map_sub, Gchi_conj_ramp, inv_one, Complex.conj_ofReal, Complex.conj_ofReal]`. Establish `h2 : χ⁻¹ ≠ 1` using `fun h => h1 (inv_eq_one.mp h)`.

Simplify using `only [Gchi, h1, h2, if_false]`. Establish `hL` using `Gchi_conj_LFunction χ`. Establish `h1c : (starRingEnd ℂ) (1 : ℂ) = 1` using `map_one _`. Rewrite using `[map_add, map_mul, map_div₀, Gchi_conj_ramp, Complex.conj_ofReal, hL]`. Use `congr 2`.

Rewrite using `[← h1c, deriv_conj_comp_conj, h1c]`. Simplify using `only [Function.comp_apply, h1c]`.
-/
theorem Gchi_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (starRingEnd ℂ) (Gchi χ y) = Gchi χ⁻¹ y := by
  by_cases h1 : χ = 1
  · subst h1
    simp only [Gchi, inv_one, if_true]
    rw [map_add, map_sub, Gchi_conj_ramp, inv_one, Complex.conj_ofReal, Complex.conj_ofReal]
  · have h2 : χ⁻¹ ≠ 1 := fun h => h1 (inv_eq_one.mp h)
    simp only [Gchi, h1, h2, if_false]
    have hL := Gchi_conj_LFunction χ
    have h1c : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _
    rw [map_add, map_mul, map_div₀, Gchi_conj_ramp, Complex.conj_ofReal, hL]
    congr 2
    rw [← h1c, deriv_conj_comp_conj, h1c]
    simp only [Function.comp_apply, h1c]

end Deduction

end
