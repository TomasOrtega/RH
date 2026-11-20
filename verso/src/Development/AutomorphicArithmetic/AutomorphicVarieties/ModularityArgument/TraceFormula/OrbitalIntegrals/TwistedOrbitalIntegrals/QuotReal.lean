import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

/- English proof (translation)
Establish `hmul : Measurable fun p : G × H => (p.2 : G) * p.1` using `(measurable_subtype_coe.comp measurable_snd).mul measurable_fst`. Establish `hset : MeasurableSet {p : G × H | ρ ((p.2 : G) * p.1) < ∞}` using `measurableSet_lt (hρ.1.comp hmul) measurable_const`. Establish `h1 : ∀ᵐ g ∂μG, ∀ᵐ h : H ∂μ, ρ ((h : G) * g) < ∞`. Use `Filter.Eventually.of_forall fun g => ?_` and prove the remaining obligations. Use `ae_lt_top (hρ.1.comp (measurable_subtype_coe.mul_const g)) ?_` and prove the remaining obligations.

Rewrite using `[hρ.2 g]`. Conclude with `ENNReal.one_ne_top`. Establish `h2 : ∀ᵐ h : H ∂μ, ∀ᵐ g ∂μG, ρ ((h : G) * g) < ∞` using `(Measure.ae_ae_comm (p := fun (g : G) (h : H) => ρ ((h : G) * g) < ∞) hset).1 h1`. Establish `hne : μ ≠ 0`. Introduce `h0`.

Use `hρ.2 1` as an intermediate fact. Rewrite `this` using `[h0, lintegral_zero_measure]`. Conclude with `zero_ne_one this`. Use `haveI : (ae μ).NeBot := ae_neBot.2 hne`. Take `⟨h, hh⟩` from `h2.exists`.

Establish `h3` using `(measurePreserving_mul_left μG ((h : G)⁻¹)).quasiMeasurePreserving.ae hh`. Simplify using `using h3`.
-/
private theorem UpperTheory.V.Z.Tf.Orb.quotReal_ae_fin {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μG : Measure G) [μG.IsMulLeftInvariant] [SFinite μG]
    (H : Subgroup G) (μ : Measure H) [SFinite μ] {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μ ρ) :
    ∀ᵐ g ∂μG, ρ g < ∞ := by
  have hmul : Measurable fun p : G × H => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hset : MeasurableSet {p : G × H | ρ ((p.2 : G) * p.1) < ∞} :=
    measurableSet_lt (hρ.1.comp hmul) measurable_const
  have h1 : ∀ᵐ g ∂μG, ∀ᵐ h : H ∂μ, ρ ((h : G) * g) < ∞ := by
    refine Filter.Eventually.of_forall fun g => ?_
    refine ae_lt_top (hρ.1.comp (measurable_subtype_coe.mul_const g)) ?_
    rw [hρ.2 g]; exact ENNReal.one_ne_top
  have h2 : ∀ᵐ h : H ∂μ, ∀ᵐ g ∂μG, ρ ((h : G) * g) < ∞ :=
    (Measure.ae_ae_comm (p := fun (g : G) (h : H) => ρ ((h : G) * g) < ∞) hset).1 h1
  have hne : μ ≠ 0 := by
    intro h0
    have := hρ.2 1
    rw [h0, lintegral_zero_measure] at this
    exact zero_ne_one this
  haveI : (ae μ).NeBot := ae_neBot.2 hne
  obtain ⟨h, hh⟩ := h2.exists
  have h3 := (measurePreserving_mul_left μG ((h : G)⁻¹)).quasiMeasurePreserving.ae hh
  simpa using h3

/- English proof (translation)
Introduce `G _ _ _ _ μG _ _ H μ _ A hA`. Unfold `quotIntegral quotLIntegral`. Use `split_ifs with hex`. Establish `hρ` using `hex.choose_spec set ρ := hex.choose`. Establish `hfin` using `UpperTheory.V.Z.Tf.Orb.quotReal_ae_fin μG H μ hρ`.

Establish `hm : Measurable fun g => A.indicator (1 : G → ℝ≥0∞) g * ρ g` using `(measurable_one.indicator hA).mul hρ.1`. Rewrite using `[← integral_toReal hm.aemeasurable, ← integral_complex_ofReal]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases hg : g ∈ A <;> simp [hg]`. Use `filter_upwards [hfin] with g hg`.

Apply the tactic sequence `by_cases hgA : g ∈ A <;> simp [hgA, hg]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Z.Tf.Orb.quotReal :
    UpperTheory.V.Z.Tf.Orb.QuotReal := by
  intro G _ _ _ _ μG _ _ H μ _ A hA
  unfold quotIntegral quotLIntegral
  split_ifs with hex
  · have hρ := hex.choose_spec
    set ρ := hex.choose
    have hfin := UpperTheory.V.Z.Tf.Orb.quotReal_ae_fin μG H μ hρ
    have hm : Measurable fun g => A.indicator (1 : G → ℝ≥0∞) g * ρ g :=
      (measurable_one.indicator hA).mul hρ.1
    rw [← integral_toReal hm.aemeasurable, ← integral_complex_ofReal]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      by_cases hg : g ∈ A <;> simp [hg]
    · filter_upwards [hfin] with g hg
      by_cases hgA : g ∈ A <;> simp [hgA, hg]
  · simp
