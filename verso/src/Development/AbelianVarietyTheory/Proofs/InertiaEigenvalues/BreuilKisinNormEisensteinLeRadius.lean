import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l hl K bk A _ s`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.out.one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `he : (0 : ℝ) < bk.Ep.natDegree` using `by exact_mod_cast bk.deg_pos`. Establish `hρ : ((bk.ρ₀ : ℝ≥0) : ℝ) = (l : ℝ) ^ (-(1 / (bk.Ep.natDegree : ℝ)))`.

Simplify using `[BK.ρ₀, NNReal.coe_rpow]`. Establish `hρpos : 0 < bk.ρ₀`. Rewrite using `[← NNReal.coe_pos, hρ]`. Conclude with `Real.rpow_pos_of_pos hl0 _`. Establish `hρe : ((bk.ρ₀ : ℝ)) ^ bk.Ep.natDegree = (l : ℝ)⁻¹`.

Rewrite using `[hρ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]`. Establish `: -(1 / (bk.Ep.natDegree : ℝ)) * (bk.Ep.natDegree : ℝ) = -1` using `by field_simp`. Rewrite using `[this, Real.rpow_neg_one]`. Use `⟨hρpos, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← NNReal.coe_lt_coe, hρ, NNReal.coe_one]`.

Conclude with `Real.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos (one_div_pos.2 he))`. Rewrite using `[hρ, ← Real.rpow_neg_one]`. Use `Real.rpow_le_rpow_of_exponent_le hl1.le ?_` and prove the remaining obligations. Establish `: 1 / (bk.Ep.natDegree : ℝ) ≤ 1`. Rewrite using `[div_le_one he]`.

Conclude with `bk.deg_pos` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE : bk.E = X ^ bk.Ep.natDegree + ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * X ^ i` using `by show (bk.Ep : (Wq l bk.a)⟦X⟧) = _ conv_lhs => rw [bk.monic.as_sum]`. Simplify using `only [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]`. Use `congr 1`.

Rewrite using `[← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]`. Simplify using the standard rewrite rules. Establish `hmem : algebraMap A (PreDisc l (s X) bk.ρ₀) (s bk.E) ∈ ball l (s X) bk.ρ₀ (l : ℝ)⁻¹`. Rewrite using `[hE, map_add, map_add, map_sum, map_sum]`. Use `add_mem ?_ (Submodule.sum_mem _ fun i hi => ?_)` and prove the remaining obligations.

Use `Submodule.subset_span ⟨0, bk.Ep.natDegree, 0, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hρe]`. Simplify using `[map_pow]`. Take `⟨c, hc⟩` from `bk.dvd_coeff i (Finset.mem_range.1 hi)`. Establish `h2 : algebraMap A (PreDisc l (s X) bk.ρ₀) (s (C (bk.Ep.coeff i) * X ^ i)) = s (C c * X ^ i) • (algebraMap A (PreDisc l (s X) bk.ρ₀) ((l : A) ^ 1 * (s X) ^ 0) * IsLocalization.Away.invSelf (l : A) ^ 0)`.

Rewrite using `[hc, Algebra.smul_def]`. Simplify using `only [map_mul, map_natCast, map_pow, pow_one, pow_zero, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, 0, 0, by simp [hl0.ne'], rfl⟩)`.

Conclude with `(norm_ofPre l (s X) bk.ρ₀ _).trans_le (gauge_le l (s X) bk.ρ₀ (by positivity) hmem)`.
-/
theorem norm_E_le_radius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ ((l : ℝ)⁻¹ ≤ bk.ρ₀) ∧ ‖toDisc l (s X) bk.ρ₀ (s bk.E)‖ ≤ (l : ℝ)⁻¹ := by
  intro l hl K bk A _ s
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  have hρ : ((bk.ρ₀ : ℝ≥0) : ℝ) = (l : ℝ) ^ (-(1 / (bk.Ep.natDegree : ℝ))) := by
    simp [BK.ρ₀, NNReal.coe_rpow]
  have hρpos : 0 < bk.ρ₀ := by
    rw [← NNReal.coe_pos, hρ]; exact Real.rpow_pos_of_pos hl0 _
  have hρe : ((bk.ρ₀ : ℝ)) ^ bk.Ep.natDegree = (l : ℝ)⁻¹ := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
    have : -(1 / (bk.Ep.natDegree : ℝ)) * (bk.Ep.natDegree : ℝ) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]
  refine ⟨hρpos, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, hρ, NNReal.coe_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos (one_div_pos.2 he))
  · rw [hρ, ← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le hl1.le ?_
    have : 1 / (bk.Ep.natDegree : ℝ) ≤ 1 := by
      rw [div_le_one he]; exact_mod_cast bk.deg_pos
    linarith
  · have hE : bk.E = X ^ bk.Ep.natDegree + ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * X ^ i := by
      show (bk.Ep : (Wq l bk.a)⟦X⟧) = _
      conv_lhs => rw [bk.monic.as_sum]
      simp only [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]
      congr 1
      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
      simp
    have hmem : algebraMap A (PreDisc l (s X) bk.ρ₀) (s bk.E) ∈ ball l (s X) bk.ρ₀ (l : ℝ)⁻¹ := by
      rw [hE, map_add, map_add, map_sum, map_sum]
      refine add_mem ?_ (Submodule.sum_mem _ fun i hi => ?_)
      · refine Submodule.subset_span ⟨0, bk.Ep.natDegree, 0, ?_, ?_⟩
        · simp [hρe]
        · simp [map_pow]
      · obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
        have h2 : algebraMap A (PreDisc l (s X) bk.ρ₀) (s (C (bk.Ep.coeff i) * X ^ i)) =
            s (C c * X ^ i) • (algebraMap A (PreDisc l (s X) bk.ρ₀) ((l : A) ^ 1 * (s X) ^ 0) *
              IsLocalization.Away.invSelf (l : A) ^ 0) := by
          rw [hc, Algebra.smul_def]
          simp only [map_mul, map_natCast, map_pow, pow_one, pow_zero, mul_one]
          ring
        rw [h2]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, 0, 0, by simp [hl0.ne'], rfl⟩)
    exact (norm_ofPre l (s X) bk.ρ₀ _).trans_le (gauge_le l (s X) bk.ρ₀ (by positivity) hmem)
end GlobalTheory.BSP
