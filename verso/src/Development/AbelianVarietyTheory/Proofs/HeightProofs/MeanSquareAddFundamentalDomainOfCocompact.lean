import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory

open Pointwise in

/- English proof (translation)
Establish `hsub : F ⊆ ⋃ γ : Γ, ((γ +ᵥ K) ∩ F)`. Introduce `g hg`. Take `⟨γ, hγ, hk⟩` from `hcov g`. Use `Set.mem_iUnion.2 ⟨-(⟨γ, hγ⟩ : Γ), ?_, hg⟩` and prove the remaining obligations. Rewrite using `[Set.mem_neg_vadd_set_iff]`.

Conclude with `hk`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem measure_addFundamentalDomain_lt_top_of_cocompact {G : Type} [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}
    (hF : IsAddFundamentalDomain Γ F μ) : μ F < ⊤ := by
  have hsub : F ⊆ ⋃ γ : Γ, ((γ +ᵥ K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, hk⟩ := hcov g
    refine Set.mem_iUnion.2 ⟨-(⟨γ, hγ⟩ : Γ), ?_, hg⟩
    rw [Set.mem_neg_vadd_set_iff]
    exact hk
  calc μ F ≤ μ (⋃ γ : Γ, ((γ +ᵥ K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ +ᵥ K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ K hK hcov`. Establish `: Countable Γ` using `countable_of_discrete_addSubgroup Γ`. Establish `hne : ∀ (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}, IsAddFundamentalDomain Γ F μ → μ F ≠ 0` using `fun μ _ F hF => hF.measure_ne_zero (NeZero.ne μ)`. Establish `hfin : ∀ (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}, IsAddFundamentalDomain Γ F μ → μ F ≠ ⊤` using `fun μ _ F hF => (measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ hF).ne`. Establish `hex : ∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1`.

Take `⟨D, -, -, hD⟩` from `exists_isAddFundamentalDomain_addSubgroup Γ`. Establish `h0` using `hne Measure.addHaar (hD _)`. Establish `h1` using `hfin Measure.addHaar (hD _)`. Use `⟨(Measure.addHaar D)⁻¹ • Measure.addHaar, D, Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0), hD _, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]`.

Use `⟨hex, fun f hf hinv => ?_⟩` and prove the remaining obligations. Take `⟨μ₀, F₀, hμ₀, hF₀, h1⟩` from `hex`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hf.continuousOn`. Establish `hb : ∀ w, ‖f w‖ₑ ^ 2 ≤ ENNReal.ofReal C ^ 2` using `fun w => by`. Take `⟨γ, hγ, hk⟩` from `hcov w`.

Use `hC _ hk` as an intermediate fact. Rewrite `this` using `[hinv γ hγ]`. Rewrite using `[← ofReal_norm_eq_enorm]`. Use `gcongr`. Establish `hN : ∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀ ≠ ⊤`.

Use `ne_top_of_le_ne_top ?_ (lintegral_mono hb)` and prove the remaining obligations. Rewrite using `[setLIntegral_const, h1, mul_one]`. Conclude with `ENNReal.pow_ne_top ENNReal.ofReal_ne_top`. Use `⟨(∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀).toNNReal, fun μ F hμ hF => ?_⟩` and prove the remaining obligations. Establish `key : ∫⁻ w in F, ‖f w‖ₑ ^ 2 ∂μ = μ F * ((∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀).toNNReal : ENNReal)`.

Rewrite using `[ENNReal.coe_toNNReal hN]`. Take `⟨c, hc⟩ : ∃ c : NNReal, μ = c • μ₀` from `⟨_, Measure.isAddLeftInvariant_eq_smul μ μ₀⟩`. Establish `hac : μ ≪ μ₀` using `hc ▸ Measure.smul_absolutelyContinuous`. Establish `hF₀' : IsAddFundamentalDomain Γ F₀ μ` using `hF₀.mono hac`. Establish `e1 : μ F = μ F₀` using `hF.measure_eq hF₀'`.

Establish `e2 : ∫⁻ w in F, ‖f w‖ₑ ^ 2 ∂μ = ∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ` using `hF.setLIntegral_eq hF₀' _ fun g x => by`. Use `hinv g g.2 x` as an intermediate fact. Rewrite using `[← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← this]`. Both sides reduce to the same expression. Rewrite using `[e1, e2, hc, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply, h1]`.

Simplify using `[ENNReal.smul_def]`. Use `⟨hne μ hF, hfin μ hF, key, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖f w‖ ^ 2) (Filter.Eventually.of_forall fun w => by positivity) (hf.norm.pow 2).aestronglyMeasurable]`. Establish `: ∀ w, ENNReal.ofReal (‖f w‖ ^ 2) = ‖f w‖ₑ ^ 2` using `fun w => by`. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`.

Simplify using `only [this]`. Rewrite using `[key, ENNReal.toReal_mul, ENNReal.coe_toReal]`.
-/
theorem meanSquare_addFundamentalDomain_of_cocompact : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) → (∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1) ∧ ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖) → ∃ N : NNReal, ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = μ 𝓕 * N ∧ ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ = (μ 𝓕).toReal * N := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov
  have : Countable Γ := countable_of_discrete_addSubgroup Γ
  have hne : ∀ (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G},
      IsAddFundamentalDomain Γ F μ → μ F ≠ 0 := fun μ _ F hF =>
    hF.measure_ne_zero (NeZero.ne μ)
  have hfin : ∀ (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G},
      IsAddFundamentalDomain Γ F μ → μ F ≠ ⊤ := fun μ _ F hF =>
    (measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ hF).ne
  have hex : ∃ (μ : Measure G) (𝓕 : Set G),
      μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
    obtain ⟨D, -, -, hD⟩ := exists_isAddFundamentalDomain_addSubgroup Γ
    have h0 := hne Measure.addHaar (hD _)
    have h1 := hfin Measure.addHaar (hD _)
    refine ⟨(Measure.addHaar D)⁻¹ • Measure.addHaar, D,
      Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0),
      hD _, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]
  refine ⟨hex, fun f hf hinv => ?_⟩
  obtain ⟨μ₀, F₀, hμ₀, hF₀, h1⟩ := hex
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ w, ‖f w‖ₑ ^ 2 ≤ ENNReal.ofReal C ^ 2 := fun w => by
    obtain ⟨γ, hγ, hk⟩ := hcov w
    have := hC _ hk
    rw [hinv γ hγ] at this
    rw [← ofReal_norm_eq_enorm]
    gcongr
  have hN : ∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hb)
    rw [setLIntegral_const, h1, mul_one]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨(∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀).toNNReal, fun μ F hμ hF => ?_⟩
  have key : ∫⁻ w in F, ‖f w‖ₑ ^ 2 ∂μ =
      μ F * ((∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀).toNNReal : ENNReal) := by
    rw [ENNReal.coe_toNNReal hN]
    obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul μ μ₀⟩
    have hac : μ ≪ μ₀ := hc ▸ Measure.smul_absolutelyContinuous
    have hF₀' : IsAddFundamentalDomain Γ F₀ μ := hF₀.mono hac
    have e1 : μ F = μ F₀ := hF.measure_eq hF₀'
    have e2 : ∫⁻ w in F, ‖f w‖ₑ ^ 2 ∂μ = ∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ :=
      hF.setLIntegral_eq hF₀' _ fun g x => by
        have := hinv g g.2 x
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← this]
        rfl
    rw [e1, e2, hc, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply, h1]
    simp [ENNReal.smul_def]
  refine ⟨hne μ hF, hfin μ hF, key, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖f w‖ ^ 2)
    (Filter.Eventually.of_forall fun w => by positivity)
    (hf.norm.pow 2).aestronglyMeasurable]
  have : ∀ w, ENNReal.ofReal (‖f w‖ ^ 2) = ‖f w‖ₑ ^ 2 := fun w => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  simp only [this]
  rw [key, ENNReal.toReal_mul, ENNReal.coe_toReal]

end GlobalTheory
