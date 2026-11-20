import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.RightBilinearApply
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SigmaFinitePosRealMeasure

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Distinguish the cases in `hf : Summable f`. Establish `hi : Integrable f (Measure.count : Measure (Xi F))`. Rewrite using `[integrable_count_iff]`. Conclude with `summable_norm_iff.mpr hf`. Rewrite using `[integral_countable hi]`.

Simplify using `[count_real_singleton]`. Rewrite using `[tsum_eq_zero_of_not_summable hf, integral_undef]`. Introduce `hi`. Rewrite `hi` using `[integrable_count_iff]`. Conclude with `hf (summable_norm_iff.mp hi)`.
-/
theorem integral_count_Xi (f : Xi F → ℂ) : ∫ ξ, f ξ ∂(Measure.count : Measure (Xi F)) = ∑' ξ, f ξ := by
  by_cases hf : Summable f
  · have hi : Integrable f (Measure.count : Measure (Xi F)) := by
      rw [integrable_count_iff]
      exact summable_norm_iff.mpr hf
    rw [integral_countable hi]
    simp [count_real_singleton]
  · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
    intro hi
    rw [integrable_count_iff] at hi
    exact hf (summable_norm_iff.mp hi)

instance isFiniteMeasure_restrict_fd :
    IsFiniteMeasure ((normOneMeasure F).restrict (normOneFundamentalDomain F)) :=
  isFiniteMeasure_restrict.mpr (normOneMeasure_normOneFundamentalDomain_lt_top (K := F)).ne

/- English proof (translation)
Establish `e1 : ∀ p : Pp F, ∫ ξ, h (p, ξ) ∂(Measure.count : Measure (Xi F)) = ∑' ξ : Xi F, h (p, ξ)` using `fun p => integral_count_Xi _`. Establish `hG : Integrable (fun p : Pp F => ∑' ξ : Xi F, h (p, ξ)) ((posRealMeasure.restrict S).prod ((normOneMeasure F).restrict (normOneFundamentalDomain F)))`. Use `hh.integral_prod_left` as an intermediate fact. Simplify using `only [e1] at this`. Conclude with `this`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hG.integral_prod_left` as an intermediate fact. Conclude with `this`. Rewrite using `[μS, integral_prod _ hh]`. Simplify using `only [e1]`.

Rewrite using `[integral_prod _ hG]`.
-/
theorem integral_iter_eq (S : Set {r : ℝ // 0 < r}) (hS : MeasurableSet S) {h : Pp F × Xi F → ℂ}
    (hh : Integrable h (μS F S)) :
    IntegrableOn (fun t => ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F, h ((t, u), ξ) ∂normOneMeasure F)
        S posRealMeasure ∧
      ∫ t in S, ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F, h ((t, u), ξ) ∂normOneMeasure F
          ∂posRealMeasure = ∫ q, h q ∂μS F S := by
  have e1 : ∀ p : Pp F, ∫ ξ, h (p, ξ) ∂(Measure.count : Measure (Xi F)) = ∑' ξ : Xi F, h (p, ξ) :=
    fun p => integral_count_Xi _
  have hG : Integrable (fun p : Pp F => ∑' ξ : Xi F, h (p, ξ))
      ((posRealMeasure.restrict S).prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))) := by
    have := hh.integral_prod_left
    simp only [e1] at this
    exact this
  refine ⟨?_, ?_⟩
  · have := hG.integral_prod_left
    exact this
  · rw [μS, integral_prod _ hh]
    simp only [e1]
    rw [integral_prod _ hG]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
