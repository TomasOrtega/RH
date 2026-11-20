import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

/- English proof (translation)
Introduce `hM G _ _ _ _ _ _ _ _ μG hμ H hH μ hh hi F hF hFH ⟨C, hC, hs⟩ ρ hρ`. Take `⟨hf, hm⟩` from `hM G μG hμ H hH μ hh hi ρ hρ`. Take `⟨hcl, hfin⟩` from `hm C hC`. Take `⟨M, hM⟩` from `hC.exists_bound_of_continuousOn hF.continuousOn`. Establish `h1 : IntegrableOn (fun g => (ρ g).toReal) {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} μG` using `integrable_toReal_of_lintegral_ne_top hρ.1.aemeasurable hfin`.

Establish `h2` using `((integrable_indicator_iff hcl.measurableSet).2 h1).const_mul M`. Use `h2.mono' (hF.measurable.mul (Complex.measurable_ofReal.comp hρ.1.ennreal_toReal)).aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}`. Rewrite using `[Set.indicator_of_mem hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]`. Take `⟨h, hh, c, hc, rfl⟩` from `hg`.

Rewrite using `[hFH h hh]`. Conclude with `mul_le_mul_of_nonneg_right (hM c hc) ENNReal.toReal_nonneg`. Establish `: F g = 0`. Assume the negation of the conclusion as `h0`. Conclude with `hg (hs g h0)`.

Simplify using `[this, Set.indicator_of_notMem hg]`.
-/
theorem UpperTheory.V.Z.Tf.Orb.quotInt :
    UpperTheory.V.Z.Tf.Orb.QuotMass → UpperTheory.V.Z.Tf.Orb.QuotInt := by
  intro hM G _ _ _ _ _ _ _ _ μG hμ H hH μ hh hi F hF hFH ⟨C, hC, hs⟩ ρ hρ
  obtain ⟨hf, hm⟩ := hM G μG hμ H hH μ hh hi ρ hρ
  obtain ⟨hcl, hfin⟩ := hm C hC
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  have h1 : IntegrableOn (fun g => (ρ g).toReal) {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} μG :=
    integrable_toReal_of_lintegral_ne_top hρ.1.aemeasurable hfin
  have h2 := ((integrable_indicator_iff hcl.measurableSet).2 h1).const_mul M
  refine h2.mono' (hF.measurable.mul (Complex.measurable_ofReal.comp hρ.1.ennreal_toReal)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  by_cases hg : g ∈ {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}
  · rw [Set.indicator_of_mem hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    obtain ⟨h, hh, c, hc, rfl⟩ := hg
    rw [hFH h hh]
    exact mul_le_mul_of_nonneg_right (hM c hc) ENNReal.toReal_nonneg
  · have : F g = 0 := by
      by_contra h0
      exact hg (hs g h0)
    simp [this, Set.indicator_of_notMem hg]
