import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.AssemblyStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Introduce `n ε lam T Ψ hgap hP`. Establish `hv₀ : T.w ≠ 0`. Introduce `h`. Establish `h1` using `T.w_norm`. Rewrite `h1` using `[h, norm_zero]`.

Conclude with `zero_ne_one h1`. Establish `hN0 : ‖uniformisationL2 ε Ψ T.w T.w‖ ≠ 0` using `norm_ne_zero_iff.mpr (datumEmbedding_highest_ne_zero hgap hP hv₀)`. Take `⟨c, hc⟩ : ∃ c : ℂ, c = ((‖uniformisationL2 ε Ψ T.w T.w‖⁻¹ : ℝ) : ℂ)` from `⟨_, rfl⟩`. Establish `h0 : uniformisationL2 ε Ψ T.w 0 = 0` using `by simpa using datumEmbedding_smul hP T.w 0 T.w`. Establish `hmem` using `datumEmbedding_mem_smooth hP T.w (c • T.w)`.

Use `⟨L2 ε, inferInstance, inferInstance, rreg ε, uniformisationL2 ε Ψ T.w (c • T.w), ?_, ?_⟩` and prove the remaining obligations. Use `⟨rreg_isURepOn ε, hmem, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[datumEmbedding_smul hP, norm_smul, hc, Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hN0]`. Prove the components needed by the constructor for the conclusion. Introduce `a`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[rightDerivative_datum_embedding hP T.w (c • T.w) rfl, map_smul, T.w_wt a, Submodule.coe_smul, ← datumEmbedding_smul hP, smul_comm]`. Introduce `a b hab hε`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[rightDerivative_datum_embedding hP T.w (c • T.w) hε, map_smul, T.w_hw a b hab hε, smul_zero, h0]`.

Both sides reduce to the same expression. Conclude with `datumV_casimir hP T.w _ ((mem_datumV_iff hP T.w _).2 ⟨c • T.w, rfl⟩)`. Introduce `g hg`. Establish `key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ c * c) = 1`. Rewrite using `[hc, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]`.

Use `congr 1`. Rewrite using `[pow_two, mul_mul_mul_comm, mul_inv_cancel₀ hN0, one_mul]`. Rewrite using `[formulaF hgap hP hv₀ hg (c • T.w) (c • T.w), map_smul, inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ c), ← mul_assoc, key, one_mul]`.
-/
theorem link : LinkStatement := by
  intro n ε lam T Ψ hgap hP
  have hv₀ : T.w ≠ 0 := by
    intro h
    have h1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hN0 : ‖uniformisationL2 ε Ψ T.w T.w‖ ≠ 0 := norm_ne_zero_iff.mpr (datumEmbedding_highest_ne_zero hgap hP hv₀)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((‖uniformisationL2 ε Ψ T.w T.w‖⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have h0 : uniformisationL2 ε Ψ T.w 0 = 0 := by simpa using datumEmbedding_smul hP T.w 0 T.w
  have hmem := datumEmbedding_mem_smooth hP T.w (c • T.w)
  refine ⟨L2 ε, inferInstance, inferInstance, rreg ε, uniformisationL2 ε Ψ T.w (c • T.w), ?_, ?_⟩
  · refine ⟨rreg_isURepOn ε, hmem, ?_, ?_, ?_⟩
    · rw [datumEmbedding_smul hP, norm_smul, hc, Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hN0]
    · constructor
      · intro a
        apply Subtype.ext
        rw [rightDerivative_datum_embedding hP T.w (c • T.w) rfl, map_smul, T.w_wt a, Submodule.coe_smul, ← datumEmbedding_smul hP,
          smul_comm]
      · intro a b hab hε
        apply Subtype.ext
        rw [rightDerivative_datum_embedding hP T.w (c • T.w) hε, map_smul, T.w_hw a b hab hε, smul_zero, h0]
        rfl
    · exact datumV_casimir hP T.w _ ((mem_datumV_iff hP T.w _).2 ⟨c • T.w, rfl⟩)
  · intro g hg
    have key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ c * c) = 1 := by
      rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
      congr 1
      rw [pow_two, mul_mul_mul_comm, mul_inv_cancel₀ hN0, one_mul]
    rw [formulaF hgap hP hv₀ hg (c • T.w) (c • T.w), map_smul, inner_smul_left, inner_smul_right,
      ← mul_assoc (starRingEnd ℂ c), ← mul_assoc, key, one_mul]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
