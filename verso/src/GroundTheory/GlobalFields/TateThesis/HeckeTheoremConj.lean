import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeTheoremScaling
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInverse

open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing ComplexConjugate Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

/- English proof (translation)
Rewrite using `[cpow_conj _ _ (by rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne), conj_ofReal]`.
-/
theorem ofReal_cpow_conj {r : ℝ} (hr : 0 < r) (s : ℂ) : (r : ℂ) ^ conj s = conj ((r : ℂ) ^ s) := by
  rw [cpow_conj _ _ (by rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne), conj_ofReal]

/- English proof (translation)
Rewrite using `[Gammaℝ_def, Gammaℝ_def, map_mul, ← ofReal_cpow_conj Real.pi_pos, ← Gamma_conj]`. Apply the tactic sequence `congr 2 <;> simp [map_div₀, map_neg, map_ofNat]`.
-/
theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← ofReal_cpow_conj Real.pi_pos, ← Gamma_conj]
  congr 2 <;> simp [map_div₀, map_neg, map_ofNat]

/- English proof (translation)
Establish `h2π : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[Gammaℂ_def, Gammaℂ_def, map_mul, map_mul, h2π, ← ofReal_cpow_conj (by positivity), ← Gamma_conj, map_ofNat, map_neg]`.
-/
theorem Gammaℂ_conj (s : ℂ) : Gammaℂ (conj s) = conj (Gammaℂ s) := by
  have h2π : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
  rw [Gammaℂ_def, Gammaℂ_def, map_mul, map_mul, h2π, ← ofReal_cpow_conj (by positivity),
    ← Gamma_conj, map_ofNat, map_neg]

/- English proof (translation)
Rewrite using `[Gammaℂ_def]`. Use `mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos hs)` and prove the remaining obligations. Rewrite using `[Ne, cpow_eq_zero_iff, not_and_or]`. Conclude with `Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero))`.
-/
theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos hs)
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero))

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

/- English proof (translation)
Unfold `infiniteGamma`. Use `split_ifs with hw`. Use `Gammaℝ_ne_zero_of_re_pos ?_` and prove the remaining obligations. Use `(χ.infiniteWeight_of_isReal hw).1` as an intermediate fact. Simplify using `only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, intCast_re]`.

Establish `h0 : (0 : ℝ) ≤ (χ.infiniteWeight w : ℝ)` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Gammaℂ_ne_zero_of_re_pos ?_` and prove the remaining obligations. Simplify using `only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, div_ofNat_re, natCast_re]`. Check the signs of the components of the expression.
-/
theorem infiniteGamma_ne_zero (w : InfinitePlace K) {s : ℂ} (hs : 0 < s.re) :
    χ.infiniteGamma w s ≠ 0 := by
  unfold infiniteGamma
  split_ifs with hw
  · refine Gammaℝ_ne_zero_of_re_pos ?_
    have := (χ.infiniteWeight_of_isReal hw).1
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, intCast_re]
    have h0 : (0 : ℝ) ≤ (χ.infiniteWeight w : ℝ) := by exact_mod_cast this
    linarith
  · refine Gammaℂ_ne_zero_of_re_pos ?_
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, div_ofNat_re, natCast_re]
    positivity

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun w _ ↦ χ.infiniteGamma_ne_zero w hs`.
-/
theorem gammaFactor_ne_zero {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ ↦ χ.infiniteGamma_ne_zero w hs

/- English proof (translation)
Establish `h : (fun s ↦ (χ.gammaFactor s)⁻¹) = fun s ↦ ∏ w, (χ.infiniteGamma w s)⁻¹`. Use function extensionality and compare the values at `s`. Rewrite using `[gammaFactor, Finset.prod_inv_distrib]`. Rewrite using `[h]`. Use `Differentiable.fun_finsetProd fun w _ ↦ ?_` and prove the remaining obligations.

Unfold `infiniteGamma`. Use `split_ifs`. Conclude with `differentiable_Gammaℝ_inv.comp ((differentiable_id.add_const _).add_const _)`. Conclude with `differentiable_Gammaℂ_inv.comp ((differentiable_id.add_const _).add_const _)`.
-/
theorem differentiable_gammaFactor_inv : Differentiable ℂ fun s ↦ (χ.gammaFactor s)⁻¹ := by
  have h : (fun s ↦ (χ.gammaFactor s)⁻¹) = fun s ↦ ∏ w, (χ.infiniteGamma w s)⁻¹ := by
    funext s
    rw [gammaFactor, Finset.prod_inv_distrib]
  rw [h]
  refine Differentiable.fun_finsetProd fun w _ ↦ ?_
  unfold infiniteGamma
  split_ifs
  · exact differentiable_Gammaℝ_inv.comp ((differentiable_id.add_const _).add_const _)
  · exact differentiable_Gammaℂ_inv.comp ((differentiable_id.add_const _).add_const _)

end HeckeCharacter

end

end GroundTheory.Global
