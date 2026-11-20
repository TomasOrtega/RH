import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory PositivityTheory.Rg.Tf.Loc in
/- English proof (translation)
Introduce `hI G _ _ _ _ _ _ _ _ μG hμG H μ hs hinv c hc F hF hFH`. Establish `hc0 : (c : ENNReal) ≠ 0` using `ENNReal.coe_ne_zero.mpr hc`. Establish `hct : (c : ENNReal) ≠ ⊤` using `ENNReal.coe_ne_top`. Establish `hsm : (c • μ : Measure H) = (c : ENNReal) • μ` using `rfl`. Distinguish the cases in `hex : ∃ ρ, IsQuotNormaliser H μ ρ`.

Take `⟨ρ, hρ⟩` from `hex`. Establish `hρ' : IsQuotNormaliser H (c • μ) (fun g => (c : ENNReal)⁻¹ * ρ g)`. Use `⟨hρ.1.const_mul _, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hsm, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0), hρ.2 g, mul_one, smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]`. Establish `hs' : SFinite (c • μ)` using `by rw [hsm]; infer_instance`.

Establish `hinv' : (c • μ).IsInvInvariant`. Prove the components needed by the constructor for the conclusion. Establish `h1 : μ.inv = μ` using `Measure.inv_eq_self μ`. Rewrite `h1`, the goal using `[Measure.inv]`. Rewrite using `[hsm, Measure.map_smul, h1]`.

Rewrite using `[hI G μG hμG H μ hs hinv F hF hFH ρ hρ, hI G μG hμG H (c • μ) hs' hinv' F hF hFH _ hρ', ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.coe_toReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hex' : ¬ ∃ ρ, IsQuotNormaliser H (c • μ) ρ`. Introduce and unpack `⟨ρ, hρ⟩`. Use `hex ⟨fun g => (c : ENNReal) * ρ g, hρ.1.const_mul _, fun g => ?_⟩` and prove the remaining obligations. Establish `h2` using `hρ.2 g`. Rewrite `h2` using `[hsm, lintegral_smul_measure, smul_eq_mul]`.

Rewrite using `[lintegral_const_mul' _ _ hct, h2]`. Simplify using `only [quotIntegral, dif_neg hex, dif_neg hex', mul_zero]`.
-/
theorem UpperTheory.V.Z.Tf.Orb.quotScale :
    UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotScale := by
  intro hI G _ _ _ _ _ _ _ _ μG hμG H μ hs hinv c hc F hF hFH
  have hc0 : (c : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hc
  have hct : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsm : (c • μ : Measure H) = (c : ENNReal) • μ := rfl
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H (c • μ) (fun g => (c : ENNReal)⁻¹ * ρ g) := by
      refine ⟨hρ.1.const_mul _, fun g => ?_⟩
      rw [hsm, lintegral_smul_measure,
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0), hρ.2 g, mul_one, smul_eq_mul,
        ENNReal.mul_inv_cancel hc0 hct]
    have hs' : SFinite (c • μ) := by rw [hsm]; infer_instance
    have hinv' : (c • μ).IsInvInvariant := by
      constructor
      have h1 : μ.inv = μ := Measure.inv_eq_self μ
      rw [Measure.inv] at h1 ⊢
      rw [hsm, Measure.map_smul, h1]
    rw [hI G μG hμG H μ hs hinv F hF hFH ρ hρ,
      hI G μG hμG H (c • μ) hs' hinv' F hF hFH _ hρ', ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.coe_toReal]
    push_cast
    ring
  · have hex' : ¬ ∃ ρ, IsQuotNormaliser H (c • μ) ρ := by
      rintro ⟨ρ, hρ⟩
      refine hex ⟨fun g => (c : ENNReal) * ρ g, hρ.1.const_mul _, fun g => ?_⟩
      have h2 := hρ.2 g
      rw [hsm, lintegral_smul_measure, smul_eq_mul] at h2
      rw [lintegral_const_mul' _ _ hct, h2]
    simp only [quotIntegral, dif_neg hex, dif_neg hex', mul_zero]
