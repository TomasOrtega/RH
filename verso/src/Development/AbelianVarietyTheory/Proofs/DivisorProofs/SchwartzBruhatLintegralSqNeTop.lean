import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB

open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.SBNorm

/- English proof (translation)
Introduce `k _ _ _ _ n d μ hμ f hf`. Use `letI : MeasurableSpace (Fin n × Fin d → k) := borel _`. Use `haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩`. Use `haveI := hμ`. Take `⟨_, _⟩` from `GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`.

Establish `hfc : Continuous f` using `hf.1.continuous`. Establish `hint : ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ`. Introduce `g hg`. Establish `hgc : Continuous g` using `hg.1.continuous`. Conclude with `(hfc.mul (Complex.continuous_conj.comp hgc)).integrable_of_hasCompactSupport (hf.2.mul_right (f' := fun y => (starRingEnd ℂ) (g y)))`.

Establish `hpt : ∀ y, ‖f y * (starRingEnd ℂ) (f y)‖ₑ = ‖f y‖ₑ ^ 2`. Introduce `y`. Rewrite using `[enorm_mul, pow_two]`. Use `congr 1`. Simplify using `[enorm_eq_nnnorm]`.

Establish `hfin : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤`. Use `(hint f hf).2` as an intermediate fact. Unfold `HasFiniteIntegral at this`. Rewrite `this` using `[hpt]`. Conclude with `this.ne`.

Use `⟨hfin, ?_, ?_, hint⟩` and prove the remaining obligations. Establish `h1 : ∀ y, f y * (starRingEnd ℂ) (f y) = (((‖f y‖ ^ 2 : ℝ)) : ℂ)`. Introduce `y`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Repeatedly rewrite using `[h1]`.

Rewrite using `[integral_complex_ofReal]`. Use `congr 1`. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (f := fun y => ‖f y‖ ^ 2) (Filter.Eventually.of_forall fun y => by positivity) ((hfc.norm.pow 2).aestronglyMeasurable)]`. Use `congr 1`. Apply `lintegral_congr` to reduce the goal to its premises.

Introduce `y`. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`. Introduce `hne`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, f x ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne (funext h)`. Establish `hmeas : Measurable fun y => ‖f y‖ₑ ^ 2` using `(hfc.measurable.enorm).pow_const 2`. Rewrite using `[← pos_iff_ne_zero, lintegral_pos_iff_support hmeas]`. Establish `hsupp : Function.support (fun y => ‖f y‖ₑ ^ 2) = f ⁻¹' {0}ᶜ`.

Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite using `[hsupp]`. Conclude with `(hf.1 ({0}ᶜ)).measure_pos μ ⟨x, hx⟩`.
-/
theorem schwartzBruhat_memL2_inner_self : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : @Measure (Fin n × Fin d → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k),
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ ∧
      ∫ y, f y * (starRingEnd ℂ) (f y) ∂μ = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧
      (f ≠ 0 → ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0) ∧
      ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  intro k _ _ _ _ n d μ hμ f hf
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hfc : Continuous f := hf.1.continuous
  have hint : ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
    intro g hg
    have hgc : Continuous g := hg.1.continuous
    exact (hfc.mul (Complex.continuous_conj.comp hgc)).integrable_of_hasCompactSupport
      (hf.2.mul_right (f' := fun y => (starRingEnd ℂ) (g y)))
  have hpt : ∀ y, ‖f y * (starRingEnd ℂ) (f y)‖ₑ = ‖f y‖ₑ ^ 2 := by
    intro y
    rw [enorm_mul, pow_two]
    congr 1
    simp [enorm_eq_nnnorm]
  have hfin : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have := (hint f hf).2
    unfold HasFiniteIntegral at this
    simp_rw [hpt] at this
    exact this.ne
  refine ⟨hfin, ?_, ?_, hint⟩
  · have h1 : ∀ y, f y * (starRingEnd ℂ) (f y) = (((‖f y‖ ^ 2 : ℝ)) : ℂ) := by
      intro y
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => ‖f y‖ ^ 2)
      (Filter.Eventually.of_forall fun y => by positivity)
      ((hfc.norm.pow 2).aestronglyMeasurable)]
    congr 1
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  · intro hne
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hmeas : Measurable fun y => ‖f y‖ₑ ^ 2 := (hfc.measurable.enorm).pow_const 2
    rw [← pos_iff_ne_zero, lintegral_pos_iff_support hmeas]
    have hsupp : Function.support (fun y => ‖f y‖ₑ ^ 2) = f ⁻¹' {0}ᶜ := by
      ext y
      simp
    rw [hsupp]
    exact (hf.1 ({0}ᶜ)).measure_pos μ ⟨x, hx⟩

end GlobalTheory.SBNorm
