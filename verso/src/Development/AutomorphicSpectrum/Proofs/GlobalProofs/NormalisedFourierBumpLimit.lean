import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim

/- English proof (translation)
Introduce `F _ _ ψ hψ laminf _ ρ hρ hsupp t`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Establish `hg_cont : Continuous fun x : Ainf F => psiInf F ψ (x * t)`. Establish `h1 : Continuous fun x : Ainf F => pairA F (x * t) 0` using `(continuous_mul_const t).prodMk continuous_const`. Conclude with `hψ.1.comp h1`.

Establish `hg0 : psiInf F ψ (0 * t) = 1`. Establish `h0 : pairA F (0 * t) 0 = 0`. Rewrite using `[zero_mul]`. Both sides reduce to the same expression. Use `show ψ (pairA F (0 * t) 0) = 1`.

Rewrite using `[h0, AddChar.map_zero_eq_one]`. Rewrite using `[Metric.tendsto_nhds]`. Introduce `ε hε`. Establish `hU : (fun x : Ainf F => psiInf F ψ (x * t)) ⁻¹' Metric.ball 1 (ε / 2) ∈ nhds (0 : Ainf F)`. Apply `hg_cont.continuousAt.preimage_mem_nhds` to reduce the goal to its premises.

Rewrite using `[hg0]`. Conclude with `Metric.ball_mem_nhds _ (half_pos hε)`. Use `filter_upwards [Filter.tendsto_smallSets_iff.1 hsupp _ hU] with k hk`. Take `⟨hc, hcs, hnn, hI⟩` from `hρ k`. Establish `hint : Integrable (ρ k) laminf` using `hc.integrable_of_hasCompactSupport hcs`.

Establish `hc1 : Continuous fun x => (ρ k x : ℂ)` using `Complex.continuous_ofReal.comp hc`. Establish `hcs1 : HasCompactSupport fun x => (ρ k x : ℂ)` using `hcs.comp_left Complex.ofReal_zero`. Establish `hi1 : Integrable (fun x => (ρ k x : ℂ)) laminf` using `hc1.integrable_of_hasCompactSupport hcs1`. Establish `hi2 : Integrable (fun x => (ρ k x : ℂ) * psiInf F ψ (x * t)) laminf` using `(hc1.mul hg_cont).integrable_of_hasCompactSupport (hcs1.mul_right (f' := fun x => psiInf F ψ (x * t)))`. Establish `key : fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) = ∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf`.

Unfold `fouInf`. Rewrite using `[← integral_complex_ofReal, ← integral_sub hi2 hi1]`. Use `congr 1`. Use extensionality with `x`. Expand and normalize the polynomial expressions, which then agree.

Establish `hIc : ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hI.ne'`. Establish `hsplit : fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) - 1 = (fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)`. Rewrite using `[sub_div, div_self hIc]`. Establish `hbound : ‖∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf‖ ≤ ∫ x, ρ k x * (ε / 2) ∂laminf`. Apply `norm_integral_le_of_norm_le (hint.mul_const _)` to reduce the goal to its premises.

Use `Filter.Eventually.of_forall fun x => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn x)]`. Distinguish the cases in `hx : x ∈ tsupport (ρ k)`. Establish `h` using `hk hx`. Simplify using `only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h`.

Conclude with `mul_le_mul_of_nonneg_left h.le (hnn x)`. Rewrite using `[image_eq_zero_of_notMem_tsupport hx]`. Simplify using the standard rewrite rules. Rewrite `hbound` using `[integral_mul_const]`. Rewrite using `[dist_eq_norm, hsplit, key, norm_div, Complex.norm_real, Real.norm_of_nonneg hI.le, div_lt_iff₀ hI]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem tendsto_fouInf_div_integral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∀ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets → ∀ t : Ainf F, Filter.Tendsto (fun k => fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) Filter.atTop (nhds 1) := by
  intro F _ _ ψ hψ laminf _ ρ hρ hsupp t
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hg_cont : Continuous fun x : Ainf F => psiInf F ψ (x * t) := by
    have h1 : Continuous fun x : Ainf F => pairA F (x * t) 0 :=
      (continuous_mul_const t).prodMk continuous_const
    exact hψ.1.comp h1
  have hg0 : psiInf F ψ (0 * t) = 1 := by
    have h0 : pairA F (0 * t) 0 = 0 := by
      rw [zero_mul]
      rfl
    show ψ (pairA F (0 * t) 0) = 1
    rw [h0, AddChar.map_zero_eq_one]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hU : (fun x : Ainf F => psiInf F ψ (x * t)) ⁻¹' Metric.ball 1 (ε / 2) ∈ nhds (0 : Ainf F) := by
    apply hg_cont.continuousAt.preimage_mem_nhds
    rw [hg0]
    exact Metric.ball_mem_nhds _ (half_pos hε)
  filter_upwards [Filter.tendsto_smallSets_iff.1 hsupp _ hU] with k hk
  obtain ⟨hc, hcs, hnn, hI⟩ := hρ k
  have hint : Integrable (ρ k) laminf := hc.integrable_of_hasCompactSupport hcs
  have hc1 : Continuous fun x => (ρ k x : ℂ) := Complex.continuous_ofReal.comp hc
  have hcs1 : HasCompactSupport fun x => (ρ k x : ℂ) := hcs.comp_left Complex.ofReal_zero
  have hi1 : Integrable (fun x => (ρ k x : ℂ)) laminf := hc1.integrable_of_hasCompactSupport hcs1
  have hi2 : Integrable (fun x => (ρ k x : ℂ) * psiInf F ψ (x * t)) laminf :=
    (hc1.mul hg_cont).integrable_of_hasCompactSupport
      (hcs1.mul_right (f' := fun x => psiInf F ψ (x * t)))
  have key : fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)
      = ∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf := by
    unfold fouInf
    rw [← integral_complex_ofReal, ← integral_sub hi2 hi1]
    congr 1
    ext x
    ring
  have hIc : ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hI.ne'
  have hsplit : fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) - 1
      = (fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) := by
    rw [sub_div, div_self hIc]
  have hbound : ‖∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf‖ ≤ ∫ x, ρ k x * (ε / 2) ∂laminf := by
    apply norm_integral_le_of_norm_le (hint.mul_const _)
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn x)]
    by_cases hx : x ∈ tsupport (ρ k)
    · have h := hk hx
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
      exact mul_le_mul_of_nonneg_left h.le (hnn x)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [integral_mul_const] at hbound
  rw [dist_eq_norm, hsplit, key, norm_div, Complex.norm_real, Real.norm_of_nonneg hI.le, div_lt_iff₀ hI]
  nlinarith

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim
