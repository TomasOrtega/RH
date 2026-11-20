import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
open scoped ContDiff

namespace GlobalTheory

open MeasureTheory in

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ K hK hcov f hf hf0 hinv`. Establish `: Countable Γ` using `countable_of_discrete_addSubgroup Γ`. Take `⟨hex, h⟩` from `meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov`. Take `⟨N, hN⟩` from `h f hf hinv`. Use `⟨hex, ?_⟩` and prove the remaining obligations.

Establish `hN0 : N ≠ 0`. Introduce `h0`. Take `⟨μ, F, hμ, hF, h1⟩` from `hex`. Establish `h2` using `(hN μ F hμ hF).2.2.1`. Rewrite `h2` using `[h0, ENNReal.coe_zero, mul_zero]`.

Establish `h3 : ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ = 0`. Rewrite using `[hF.lintegral_eq_tsum'']`. Establish `e : ∀ (g : Γ) (x : G), ‖f (g +ᵥ x)‖ₑ = ‖f x‖ₑ` using `fun g x => by`. Use `hinv g g.2 x` as an intermediate fact. Rewrite using `[← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← this]`.

Both sides reduce to the same expression. Simplify using `only [e, h2, tsum_zero]`. Rewrite `h3` using `[lintegral_eq_zero_iff (hf.enorm.measurable.pow_const 2)]`. Apply `hf0` to reduce the goal to its premises. Rewrite using `[← hf.ae_eq_iff_eq μ continuous_zero]`.

Use `filter_upwards [h3] with w hw`. Simplify using `using hw`. Establish `hpos : (0 : ℝ) < N` using `by positivity`. Use `⟨((√(N : ℝ))⁻¹ : ℝ), fun μ F hμ hF h1 => ?_⟩` and prove the remaining obligations. Establish `h2` using `(hN μ F hμ hF).2.2.2`.

Rewrite `h2` using `[h1, ENNReal.toReal_one, one_mul]`. Simplify using `only [norm_mul, mul_pow]`. Rewrite using `[integral_const_mul, h2, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']`.
-/
theorem exists_normalise_meanSquare_of_cocompact : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x : G, ∃ g ∈ Γ, g + x ∈ K) → ∀ f : G → ℂ, Continuous f → f ≠ 0 → (∀ g ∈ Γ, ∀ w, ‖f (g + w)‖ = ‖f w‖) → (∃ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1) ∧ ∃ c : ℂ, ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∫ w in 𝓕, ‖c * f w‖ ^ 2 ∂μ = 1 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov f hf hf0 hinv
  have : Countable Γ := countable_of_discrete_addSubgroup Γ
  obtain ⟨hex, h⟩ := meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov
  obtain ⟨N, hN⟩ := h f hf hinv
  refine ⟨hex, ?_⟩
  have hN0 : N ≠ 0 := by
    intro h0
    obtain ⟨μ, F, hμ, hF, h1⟩ := hex
    have h2 := (hN μ F hμ hF).2.2.1
    rw [h0, ENNReal.coe_zero, mul_zero] at h2
    have h3 : ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ = 0 := by
      rw [hF.lintegral_eq_tsum'']
      have e : ∀ (g : Γ) (x : G), ‖f (g +ᵥ x)‖ₑ = ‖f x‖ₑ := fun g x => by
        have := hinv g g.2 x
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← this]
        rfl
      simp only [e, h2, tsum_zero]
    rw [lintegral_eq_zero_iff (hf.enorm.measurable.pow_const 2)] at h3
    apply hf0
    rw [← hf.ae_eq_iff_eq μ continuous_zero]
    filter_upwards [h3] with w hw
    simpa using hw
  have hpos : (0 : ℝ) < N := by positivity
  refine ⟨((√(N : ℝ))⁻¹ : ℝ), fun μ F hμ hF h1 => ?_⟩
  have h2 := (hN μ F hμ hF).2.2.2
  rw [h1, ENNReal.toReal_one, one_mul] at h2
  simp only [norm_mul, mul_pow]
  rw [integral_const_mul, h2, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

end GlobalTheory
