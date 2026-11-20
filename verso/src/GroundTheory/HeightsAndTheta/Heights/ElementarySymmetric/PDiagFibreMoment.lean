import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StDiagFibreMoment
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StDiagFibreFubini
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagFibreMoment

/- English proof (translation)
Rewrite using `[momentPoly, coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression.

Rewrite using `[notMem_support_iff.1 h]`. Simplify using the standard rewrite rules.
-/
theorem coeff_momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) (m : Fin 3 →₀ ℕ) :
    coeff m (momentPoly μ w Q) = ∫ p, w p * coeff m Q p ∂μ := by
  rw [momentPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h]
    simp

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_momentPoly, coeff_sum, coeff_sum]`. Simplify using `only [coeff_momentPoly, Finset.sum_apply, Finset.mul_sum]`. Conclude with `integral_finsetSum s fun i hi => hQ i hi m`.
-/
theorem momentPoly_sum {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ) (s : Finset ι)
    (Q : ι → MvPolynomial (Fin 3) (Ω → ℝ)) (hQ : ∀ i ∈ s, ∀ m, Integrable (fun p => w p * coeff m (Q i) p) μ) :
    momentPoly μ w (∑ i ∈ s, Q i) = ∑ i ∈ s, momentPoly μ w (Q i) := by
  ext m
  rw [coeff_momentPoly, coeff_sum, coeff_sum]
  simp only [coeff_momentPoly, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => hQ i hi m

/- English proof (translation)
Use `set φ : C(S2 × S2, ℝ) →ₐ[ℝ] (S2 × S2 → ℝ) := ContinuousMap.coeFnAlgHom (α := S2 × S2) (A := ℝ) ℝ`. Use `set v : Fin 2 → MvPolynomial (Fin 3) C(S2 × S2, ℝ) := ![∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.fst), ∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.snd)]`. Establish `hv : ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] = fun r => mapAlgHom φ (v r)`. Use function extensionality and compare the values at `r`. Use `fin_cases r`.

Simplify using `only [Fin.zero_eta, Matrix.cons_val_zero, v, dotPoly, mapAlgHom_apply, map_sum, map_mul, map_X, map_C]`. Both sides reduce to the same expression. Simplify using `only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, v, dotPoly, mapAlgHom_apply, map_sum, map_mul, map_X, map_C]`. Both sides reduce to the same expression. Rewrite using `[hv, ← comp_aeval, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]`.

Conclude with `(coeff m (aeval v Q)).continuous`.
-/
theorem continuous_coeff_aeval (Q : MvPolynomial (Fin 2) ℝ) (m : Fin 3 →₀ ℕ) :
    Continuous (coeff m (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) := by
  set φ : C(S2 × S2, ℝ) →ₐ[ℝ] (S2 × S2 → ℝ) := ContinuousMap.coeFnAlgHom (α := S2 × S2) (A := ℝ) ℝ
  set v : Fin 2 → MvPolynomial (Fin 3) C(S2 × S2, ℝ) :=
    ![∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.fst),
      ∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.snd)]
  have hv : ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] = fun r => mapAlgHom φ (v r) := by
    funext r
    fin_cases r
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, v, dotPoly, mapAlgHom_apply, map_sum, map_mul, map_X, map_C]
      rfl
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, v, dotPoly, mapAlgHom_apply, map_sum,
        map_mul, map_X, map_C]
      rfl
  rw [hv, ← comp_aeval, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]
  exact (coeff m (aeval v Q)).continuous

/- English proof (translation)
Rewrite using `[FibreLocal.gPoly_eq, FlagBundles.gKernel]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hik` using `Finset.mem_range.1 hi`. Rewrite using `[show 2 * k - 2 * i = (2 * k - 1 - 2 * i) + 1 by omega, pow_succ, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_words (k : ℕ) :
    ∑ i ∈ Finset.range k, ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ) =
      gPoly k := by
  rw [FibreLocal.gPoly_eq, FlagBundles.gKernel]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  rw [show 2 * k - 2 * i = (2 * k - 1 - 2 * i) + 1 by omega, pow_succ, pow_succ]
  ring

/- English proof (translation)
Simplify using `only [diagWordMomentPoly]`. Rewrite using `[← momentPoly_sum _ _ _ _ fun i _ m => FibreLocal.integrable_mul _ (continuous_coeff_aeval _ m)]`. Rewrite using `[← map_sum, ← map_sum, ← map_sum, sum_words]`. Both sides reduce to the same expression.
-/
theorem sum_diagWordMomentPoly (k : ℕ) :
    ∑ i ∈ Finset.range k, diagWordMomentPoly k i = fibreMomentPoly k := by
  simp only [diagWordMomentPoly]
  rw [← momentPoly_sum _ _ _ _ fun i _ m =>
    FibreLocal.integrable_mul _ (continuous_coeff_aeval _ m)]
  rw [← map_sum, ← map_sum, ← map_sum, sum_words]
  rfl

/- English proof (translation)
Establish `h` using `FibreLocal.proof.2.1 k (MvPolynomial (Fin 3) ℝ) X`. Rewrite `h` using `[aeval_X_left_apply, MvPolynomial.algebraMap_eq]`. Then use the resulting hypothesis.
-/
theorem fibreMomentPoly_eq (k : ℕ) :
    fibreMomentPoly k = C (-kappa k) * (∑ i, X i ^ 2) ^ (k - 1) := by
  have h := FibreLocal.proof.2.1 k (MvPolynomial (Fin 3) ℝ) X
  rwa [aeval_X_left_apply, MvPolynomial.algebraMap_eq] at h

/- English proof (translation)
Introduce `D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD`. Take `⟨Λ, hw, hp⟩` from `h D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD`. Rewrite using `[Finset.sum_congr rfl fun i hi => hw i (Finset.mem_range.1 hi), ← Finset.mul_sum, ← map_sum, sum_diagWordMomentPoly, fibreMomentPoly_eq, hp, FibreLocal.pushMomentPoly_eq k hk, C_mul', map_smul, map_neg, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem proof (h : DiagFibreFubini.Statement) : DiagFibreMoment.Statement := by
  intro D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  obtain ⟨Λ, hw, hp⟩ := h D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  rw [Finset.sum_congr rfl fun i hi => hw i (Finset.mem_range.1 hi), ← Finset.mul_sum, ← map_sum,
    sum_diagWordMomentPoly, fibreMomentPoly_eq, hp, FibreLocal.pushMomentPoly_eq k hk, C_mul', map_smul,
    map_neg, smul_eq_mul]
  ring

end DiagFibreMoment

end

end GroundTheory.Heights₂.Heights.Inter
