import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `α β _ _ _ _ _ _ _ _ μa μb _ _ _ _ _ _ F hF C hC h0 c hpos a₀ b₀ h₀`. Use `set G : α × β → ℂ := Function.uncurry F with hG`. Establish `hsub : Function.support G ⊆ C`. Introduce `p hp`. Assume the negation of the conclusion as `hpC`.

Conclude with `hp (h0 p hpC)`. Take `⟨M, hM⟩` from `hC.exists_bound_of_continuousOn hF.continuousOn`. Establish `hbound : ∀ p, ‖G p‖ ≤ max M 0`. Introduce `p`. Distinguish the cases in `hp : p ∈ C`.

Conclude with `(hM p hp).trans (le_max_left _ _)`. Establish `: G p = 0` using `h0 p hp`. Rewrite using `[this, norm_zero]`. Conclude with `le_max_right _ _`. Establish `hintC : IntegrableOn G C (μa.prod μb)` using `Measure.integrableOn_of_bounded (M := max M 0) hC.measure_lt_top.ne hF.aestronglyMeasurable (Filter.Eventually.of_forall hbound)`.

Establish `hint : Integrable G (μa.prod μb)` using `(integrableOn_iff_integrable_of_support_subset hsub).1 hintC`. Establish `hprod : ∫ p, G p ∂(μa.prod μb) = ∫ a, ∫ b, F a b ∂μb ∂μa` using `integral_prod G hint`. Introduce `hzero`. Establish `hint2 : Integrable (fun p => starRingEnd ℂ c * G p) (μa.prod μb)` using `hint.const_mul _`. Establish `hre : ∫ p, (starRingEnd ℂ c * G p).re ∂(μa.prod μb) = 0`.

Use `integral_re hint2` as an intermediate fact. Rewrite `this` using `[integral_const_mul, hprod, hzero, mul_zero]`. Simplify using `using this`. Establish `hcont : Continuous (fun p : α × β => (starRingEnd ℂ c * G p).re)` using `Complex.continuous_re.comp (continuous_const.mul hF)`. Establish `hnn : 0 ≤ fun p : α × β => (starRingEnd ℂ c * G p).re` using `fun p => hpos p.1 p.2`.

Establish `hpos2 : 0 < ∫ p, (starRingEnd ℂ c * G p).re ∂(μa.prod μb)`. Rewrite using `[integral_pos_iff_support_of_nonneg hnn (Complex.reCLM.integrable_comp hint2)]`. Establish `hopen : IsOpen (Function.support fun p : α × β => (starRingEnd ℂ c * G p).re)` using `hcont.isOpen_support`. Use `hopen.measure_pos _ ⟨(a₀, b₀), ?_⟩` and prove the remaining obligations. Conclude with `ne_of_gt h₀`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bump_iterated_integral_ne_zero : ∀ {α β : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    (μa : Measure α) (μb : Measure β) [IsFiniteMeasureOnCompacts μa] [IsFiniteMeasureOnCompacts μb]
    [μa.IsOpenPosMeasure] [μb.IsOpenPosMeasure] [SFinite μa] [SFinite μb]
    (F : α → β → ℂ) (hF : Continuous (Function.uncurry F)) (C : Set (α × β)) (hC : IsCompact C)
    (h0 : ∀ p ∉ C, F p.1 p.2 = 0) (c : ℂ) (hpos : ∀ a b, 0 ≤ (starRingEnd ℂ c * F a b).re) (a₀ : α) (b₀ : β)
    (h₀ : 0 < (starRingEnd ℂ c * F a₀ b₀).re),
    ∫ a, ∫ b, F a b ∂μb ∂μa ≠ 0 := by
  intro α β _ _ _ _ _ _ _ _ μa μb _ _ _ _ _ _ F hF C hC h0 c hpos a₀ b₀ h₀
  set G : α × β → ℂ := Function.uncurry F with hG
  have hsub : Function.support G ⊆ C := by
    intro p hp
    by_contra hpC
    exact hp (h0 p hpC)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  have hbound : ∀ p, ‖G p‖ ≤ max M 0 := by
    intro p
    by_cases hp : p ∈ C
    · exact (hM p hp).trans (le_max_left _ _)
    · have : G p = 0 := h0 p hp
      rw [this, norm_zero]; exact le_max_right _ _
  have hintC : IntegrableOn G C (μa.prod μb) :=
    Measure.integrableOn_of_bounded (M := max M 0) hC.measure_lt_top.ne
      hF.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hint : Integrable G (μa.prod μb) := (integrableOn_iff_integrable_of_support_subset hsub).1 hintC
  have hprod : ∫ p, G p ∂(μa.prod μb) = ∫ a, ∫ b, F a b ∂μb ∂μa := integral_prod G hint
  intro hzero
  have hint2 : Integrable (fun p => starRingEnd ℂ c * G p) (μa.prod μb) := hint.const_mul _
  have hre : ∫ p, (starRingEnd ℂ c * G p).re ∂(μa.prod μb) = 0 := by
    have := integral_re hint2
    rw [integral_const_mul, hprod, hzero, mul_zero] at this
    simpa using this
  have hcont : Continuous (fun p : α × β => (starRingEnd ℂ c * G p).re) :=
    Complex.continuous_re.comp (continuous_const.mul hF)
  have hnn : 0 ≤ fun p : α × β => (starRingEnd ℂ c * G p).re := fun p => hpos p.1 p.2
  have hpos2 : 0 < ∫ p, (starRingEnd ℂ c * G p).re ∂(μa.prod μb) := by
    rw [integral_pos_iff_support_of_nonneg hnn (Complex.reCLM.integrable_comp hint2)]
    have hopen : IsOpen (Function.support fun p : α × β => (starRingEnd ℂ c * G p).re) :=
      hcont.isOpen_support
    refine hopen.measure_pos _ ⟨(a₀, b₀), ?_⟩
    exact ne_of_gt h₀
  linarith

end GlobalTheory
