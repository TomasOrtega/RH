import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableSetOrbitExistsMeasurableSection

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeWeil

/- English proof (translation)
Establish `hc : b⁻¹ * a ∈ MulAction.stabilizer G x₀`. Rewrite using `[MulAction.mem_stabilizer_iff, mul_smul, hab, inv_smul_smul]`. Rewrite using `[← lintegral_mul_left_eq_self (μ := μ') (fun h => f (b * (h : G))) ⟨_, hc⟩]`. Simplify using `[← mul_assoc]`.
-/
theorem inner_eq {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [MulAction G X] (x₀ : X)
    (μ' : Measure (MulAction.stabilizer G x₀)) [μ'.IsMulLeftInvariant] (f : G → ℝ≥0∞) (a b : G)
    (hab : a • x₀ = b • x₀) :
    ∫⁻ h, f (a * (h : G)) ∂μ' = ∫⁻ h, f (b * (h : G)) ∂μ' := by
  have hc : b⁻¹ * a ∈ MulAction.stabilizer G x₀ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hab, inv_smul_smul]
  rw [← lintegral_mul_left_eq_self (μ := μ') (fun h => f (b * (h : G))) ⟨_, hc⟩]
  simp [← mul_assoc]

/- English proof (translation)
Introduce `G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀ μ' ν hμ' hνc hν0 hinv hnull`. Take `⟨-, s₀, hs₀m, hs₀⟩` from `GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section G X x₀`. Establish `hcont : Continuous fun g : G => g • x₀` using `continuous_id.smul continuous_const`. Establish `hclosed : IsClosed ((MulAction.stabilizer G x₀ : Subgroup G) : Set G)` using `isClosed_eq hcont continuous_const`. Establish `hemb : IsClosedEmbedding (Subtype.val : MulAction.stabilizer G x₀ → G)` using `hclosed.isClosedEmbedding_subtypeVal`.

Establish `: LocallyCompactSpace (MulAction.stabilizer G x₀)` using `hemb.locallyCompactSpace`. Establish `: SecondCountableTopology (MulAction.stabilizer G x₀)` using `hemb.isEmbedding.secondCountableTopology`. Establish `: SigmaCompactSpace (MulAction.stabilizer G x₀)` using `inferInstance`. Establish `: IsLocallyFiniteMeasure μ'` using `inferInstance`. Establish `: SigmaFinite μ'` using `inferInstance`.

Establish `hae : ∀ᵐ y ∂ν, ∃ g : G, g • x₀ = y` using `hnull`. Establish `hΦ : Measurable fun p : X × MulAction.stabilizer G x₀ => s₀ p.1 * (p.2 : G)` using `(hs₀m.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)`. Use `set μ : Measure G := (ν.prod μ').map (fun p : X × MulAction.stabilizer G x₀ => s₀ p.1 * (p.2 : G)) with hμ`. Establish `key0 : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s₀ y * (h : G)) ∂μ' ∂ν`. Introduce `f hf`.

Rewrite using `[hμ, lintegral_map hf hΦ]`. Conclude with `lintegral_prod _ (hf.comp hΦ).aemeasurable`. Establish `hleft : μ.IsMulLeftInvariant`. Use `⟨fun g => Measure.ext_of_lintegral _ fun f hf => ?_⟩` and prove the remaining obligations. Establish `hF : Measurable fun y => ∫⁻ h, f (s₀ y * (h : G)) ∂μ'` using `(hf.comp hΦ).lintegral_prod_right'`.

Rewrite using `[lintegral_map hf (measurable_const_mul g), key0 (fun a => f (g * a)) (hf.comp (measurable_const_mul g)), key0 f hf]`. Use `conv_rhs => rw [← hinv g, lintegral_map hF (continuous_const_smul g).measurable]`. Use `lintegral_congr_ae (hae.mono fun y hy => ?_)` and prove the remaining obligations. Establish `h2 : ∃ k : G, k • x₀ = g • y`. Take `⟨k, rfl⟩` from `hy`.

Conclude with `⟨g * k, mul_smul _ _ _⟩`. Use `inner_eq x₀ μ' f (g * s₀ y) (s₀ (g • y)) (by rw [mul_smul, hs₀ y hy, hs₀ _ h2])` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `hfin : IsFiniteMeasureOnCompacts μ`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations.

Establish `hKm : MeasurableSet K` using `hK.measurableSet`. Establish `hL : IsCompact ((fun g : G => g • x₀) '' K)` using `hK.image hcont`. Establish `hM : IsCompact ((Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K))` using `hemb.isCompact_preimage (hK.inv.mul hK)`. Rewrite using `[← lintegral_indicator_one hKm, key0 _ (measurable_one.indicator hKm)]`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_mono_ae (hae.mono fun y hy => ?_)` and prove the remaining obligations. Distinguish the cases in `hyK : y ∈ (fun g : G => g • x₀) '' K`. Rewrite using `[Set.indicator_of_mem hyK]`. Take `⟨k, hk, hky⟩` from `hyK`. Rewrite using `[inner_eq x₀ μ' _ (s₀ y) k (by rw [hs₀ y hy]; exact hky.symm), ← lintegral_indicator_one hM.measurableSet]`.

Use `lintegral_mono fun h => ?_` and prove the remaining obligations. Distinguish the cases in `hh : k * (h : G) ∈ K`. Establish `: h ∈ (Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K)` using `⟨k⁻¹, by simpa using hk, k * h, hh, by simp⟩`. Simplify using `[Set.indicator_of_mem hh, Set.indicator_of_mem this]`. Simplify using `[Set.indicator_of_notMem hh]`.

Rewrite using `[Set.indicator_of_notMem hyK]`. Establish `: ∀ h : MulAction.stabilizer G x₀, s₀ y * (h : G) ∉ K` using `fun h hh => hyK ⟨_, hh, by`. Establish `h1 : (h : G) • x₀ = x₀` using `h.2`. Simplify using `only [mul_smul, h1, hs₀ y hy]⟩`. Simplify using `[Set.indicator_of_notMem (this _)]`.

Use `_ < ⊤ := by`. Rewrite using `[lintegral_indicator_const hL.measurableSet]`. Conclude with `ENNReal.mul_lt_top hM.measure_lt_top hL.measure_lt_top`. Establish `hne : μ Set.univ ≠ 0`. Rewrite using `[← lintegral_one, key0 _ measurable_const]`.

Simplify using `only [lintegral_const, one_mul]`. Conclude with `mul_ne_zero (isOpen_univ.measure_ne_zero μ' Set.univ_nonempty) (by simpa using hν0)`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, μ (compactCovering G n) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← iUnion_compactCovering G]`. Conclude with `measure_iUnion_null hcon`. Establish `hpos : μ.IsOpenPosMeasure` using `isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering G n) hn`. Use `⟨μ, ⟨⟩, fun f hf s hs => ?_⟩` and prove the remaining obligations.

Rewrite using `[key0 f hf]`. Conclude with `lintegral_congr_ae (hae.mono fun y hy => inner_eq x₀ μ' f _ _ (by rw [hs y hy, hs₀ y hy]))`.
-/
theorem weil_formula : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), ∀ (μ' : Measure (MulAction.stabilizer G x₀)) (ν : Measure X), μ'.IsHaarMeasure → IsFiniteMeasureOnCompacts ν → ν ≠ 0 → (∀ g : G, ν.map (fun y => g • y) = ν) → ν {y | ¬ ∃ g : G, g • x₀ = y} = 0 → ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s y * (h : G)) ∂μ' ∂ν := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀ μ' ν hμ' hνc hν0 hinv hnull
  obtain ⟨-, s₀, hs₀m, hs₀⟩ := GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section G X x₀
  have hcont : Continuous fun g : G => g • x₀ := continuous_id.smul continuous_const
  have hclosed : IsClosed ((MulAction.stabilizer G x₀ : Subgroup G) : Set G) :=
    isClosed_eq hcont continuous_const
  have hemb : IsClosedEmbedding (Subtype.val : MulAction.stabilizer G x₀ → G) :=
    hclosed.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace (MulAction.stabilizer G x₀) := hemb.locallyCompactSpace
  have : SecondCountableTopology (MulAction.stabilizer G x₀) :=
    hemb.isEmbedding.secondCountableTopology
  have : SigmaCompactSpace (MulAction.stabilizer G x₀) := inferInstance
  have : IsLocallyFiniteMeasure μ' := inferInstance
  have : SigmaFinite μ' := inferInstance
  have hae : ∀ᵐ y ∂ν, ∃ g : G, g • x₀ = y := hnull
  have hΦ : Measurable fun p : X × MulAction.stabilizer G x₀ => s₀ p.1 * (p.2 : G) :=
    (hs₀m.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  set μ : Measure G := (ν.prod μ').map
    (fun p : X × MulAction.stabilizer G x₀ => s₀ p.1 * (p.2 : G)) with hμ
  have key0 : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s₀ y * (h : G)) ∂μ' ∂ν := by
    intro f hf
    rw [hμ, lintegral_map hf hΦ]
    exact lintegral_prod _ (hf.comp hΦ).aemeasurable
  have hleft : μ.IsMulLeftInvariant := by
    refine ⟨fun g => Measure.ext_of_lintegral _ fun f hf => ?_⟩
    have hF : Measurable fun y => ∫⁻ h, f (s₀ y * (h : G)) ∂μ' :=
      (hf.comp hΦ).lintegral_prod_right'
    rw [lintegral_map hf (measurable_const_mul g), key0 (fun a => f (g * a)) (hf.comp (measurable_const_mul g)),
      key0 f hf]
    conv_rhs => rw [← hinv g, lintegral_map hF (continuous_const_smul g).measurable]
    refine lintegral_congr_ae (hae.mono fun y hy => ?_)
    have h2 : ∃ k : G, k • x₀ = g • y := by
      obtain ⟨k, rfl⟩ := hy
      exact ⟨g * k, mul_smul _ _ _⟩
    have := inner_eq x₀ μ' f (g * s₀ y) (s₀ (g • y)) (by rw [mul_smul, hs₀ y hy, hs₀ _ h2])
    simpa [mul_assoc] using this
  have hfin : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.measurableSet
    have hL : IsCompact ((fun g : G => g • x₀) '' K) := hK.image hcont
    have hM : IsCompact ((Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K)) :=
      hemb.isCompact_preimage (hK.inv.mul hK)
    rw [← lintegral_indicator_one hKm, key0 _ (measurable_one.indicator hKm)]
    calc _ ≤ ∫⁻ y, ((fun g : G => g • x₀) '' K).indicator
            (fun _ => μ' ((Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K))) y ∂ν := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          by_cases hyK : y ∈ (fun g : G => g • x₀) '' K
          · rw [Set.indicator_of_mem hyK]
            obtain ⟨k, hk, hky⟩ := hyK
            rw [inner_eq x₀ μ' _ (s₀ y) k (by rw [hs₀ y hy]; exact hky.symm),
              ← lintegral_indicator_one hM.measurableSet]
            refine lintegral_mono fun h => ?_
            by_cases hh : k * (h : G) ∈ K
            · have : h ∈ (Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K) :=
                ⟨k⁻¹, by simpa using hk, k * h, hh, by simp⟩
              simp [Set.indicator_of_mem hh, Set.indicator_of_mem this]
            · simp [Set.indicator_of_notMem hh]
          · rw [Set.indicator_of_notMem hyK]
            have : ∀ h : MulAction.stabilizer G x₀, s₀ y * (h : G) ∉ K := fun h hh =>
              hyK ⟨_, hh, by
                have h1 : (h : G) • x₀ = x₀ := h.2
                simp only [mul_smul, h1, hs₀ y hy]⟩
            simp [Set.indicator_of_notMem (this _)]
      _ < ⊤ := by
          rw [lintegral_indicator_const hL.measurableSet]
          exact ENNReal.mul_lt_top hM.measure_lt_top hL.measure_lt_top
  have hne : μ Set.univ ≠ 0 := by
    rw [← lintegral_one, key0 _ measurable_const]
    simp only [lintegral_const, one_mul]
    exact mul_ne_zero (isOpen_univ.measure_ne_zero μ' Set.univ_nonempty)
      (by simpa using hν0)
  obtain ⟨n, hn⟩ : ∃ n, μ (compactCovering G n) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← iUnion_compactCovering G]
    exact measure_iUnion_null hcon
  have hpos : μ.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering G n) hn
  refine ⟨μ, ⟨⟩, fun f hf s hs => ?_⟩
  rw [key0 f hf]
  exact lintegral_congr_ae (hae.mono fun y hy =>
    inner_eq x₀ μ' f _ _ (by rw [hs y hy, hs₀ y hy]))

end GlobalTheory.GaugeWeil
