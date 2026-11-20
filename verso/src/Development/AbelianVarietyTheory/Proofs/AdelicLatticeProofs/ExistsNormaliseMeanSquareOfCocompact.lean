import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
open scoped ContDiff

namespace GlobalTheory

open MeasureTheory in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
