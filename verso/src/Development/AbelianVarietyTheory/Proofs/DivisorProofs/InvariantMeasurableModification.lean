import Mathlib
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ _ _ _ _ _ _ M μK hM hμ φ hφ hinv`. Use `haveI := hμ`. Use `haveI : CompactSpace M := isCompact_iff_compactSpace.mp hM.isCompact`. Use `haveI : BorelSpace M := Subtype.borelSpace _`. Take `⟨μM, hH, h1⟩ : ∃ μM : Measure M, μM.IsHaarMeasure ∧ μM Set.univ = 1` from `⟨Measure.haarMeasure ⊤, inferInstance, by simpa using Measure.haarMeasure_self (G := M) (K₀ := ⊤)⟩`.

Use `haveI := hH`. Use `haveI : IsProbabilityMeasure μM := ⟨h1⟩`. Establish `hφ'm : Measurable (hφ.mk φ)` using `hφ.measurable_mk`. Establish `hN₀m : MeasurableSet (toMeasurable μK {x | φ x ≠ hφ.mk φ x})` using `measurableSet_toMeasurable _ _`. Establish `hN₀0 : μK (toMeasurable μK {x | φ x ≠ hφ.mk φ x}) = 0`.

Rewrite using `[measure_toMeasurable]`. Conclude with `ae_iff.mp hφ.ae_eq_mk`. Establish `hsub : {x | φ x ≠ hφ.mk φ x} ⊆ toMeasurable μK {x | φ x ≠ hφ.mk φ x}` using `subset_toMeasurable _ _`. Generalize the expression as in `toMeasurable μK {x | φ x ≠ hφ.mk φ x} = N₀ at hN₀m hN₀0 hsub`. Generalize the expression as in `hφ.mk φ = φ' at hφ'm hsub`.

Establish `hmul : Measurable (fun p : K × M => ((p.2 : K))⁻¹ * p.1)` using `((measurable_subtype_coe.comp measurable_snd).inv).mul measurable_fst`. Establish `hind : Measurable (N₀.indicator (1 : K → ℝ≥0∞))` using `measurable_one.indicator hN₀m`. Establish `hψm : Measurable (fun k : K => ∫⁻ m : M, φ' ((m : K)⁻¹ * k) ∂μM)` using `(hφ'm.comp hmul).lintegral_prod_right'`. Establish `hhm : Measurable (fun k : K => ∫⁻ m : M, N₀.indicator 1 ((m : K)⁻¹ * k) ∂μM)` using `(hind.comp hmul).lintegral_prod_right'`. Establish `inv_avg : ∀ g : K → ℝ≥0∞, ∀ m₀ ∈ M, ∀ k, ∫⁻ m : M, g ((m : K)⁻¹ * (m₀ * k)) ∂μM = ∫⁻ m : M, g ((m : K)⁻¹ * k) ∂μM`.

Introduce `g m₀ hm₀ k`. Rewrite using `[← lintegral_mul_left_eq_self _ (⟨m₀, hm₀⟩ : M)]`. Use `congr 1`. Use extensionality with `m`. Simplify using `[mul_assoc]`.

Use `⟨fun k => ∫⁻ m : M, φ' ((m : K)⁻¹ * k) ∂μM, {k | ∫⁻ m : M, N₀.indicator 1 ((m : K)⁻¹ * k) ∂μM ≠ 0}, hψm, hhm (measurableSet_singleton 0).compl, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hint : ∫⁻ k, ∫⁻ m : M, N₀.indicator 1 ((m : K)⁻¹ * k) ∂μM ∂μK = 0`. Rewrite using `[lintegral_lintegral_swap (f := fun k (m : M) => N₀.indicator (1 : K → ℝ≥0∞) ((m : K)⁻¹ * k)) (hind.comp hmul).aemeasurable]`. Establish `: ∀ m : M, ∫⁻ k, N₀.indicator (1 : K → ℝ≥0∞) ((m : K)⁻¹ * k) ∂μK = 0`. Introduce `m`.

Rewrite using `[lintegral_mul_left_eq_self (fun k => N₀.indicator (1 : K → ℝ≥0∞) k), lintegral_indicator_one hN₀m, hN₀0]`. Simplify using `[this]`. Use `(lintegral_eq_zero_iff hhm).mp hint` as an intermediate fact. Rewrite `this` using `[Filter.EventuallyEq, ae_iff]`. Simplify using `using this`.

Introduce `m hm k`. Simplify using `only [Set.mem_setOf_eq, inv_avg _ m hm k]`. Introduce `m hm k`. Conclude with `inv_avg _ m hm k`. Introduce `k hk`.

Establish `hk0 : ∫⁻ m : M, N₀.indicator 1 ((m : K)⁻¹ * k) ∂μM = 0` using `by simpa using hk`. Establish `hmk : Measurable (fun m : M => N₀.indicator (1 : K → ℝ≥0∞) ((m : K)⁻¹ * k))` using `hind.comp (measurable_subtype_coe.inv.mul_const k)`. Establish `hae` using `(lintegral_eq_zero_iff hmk).mp hk0`. Establish `: ∫⁻ m : M, φ' ((m : K)⁻¹ * k) ∂μM = ∫⁻ _m : M, φ k ∂μM`. Apply `lintegral_congr_ae` to reduce the goal to its premises.

Use `filter_upwards [hae] with m hm`. Establish `hnot : (m : K)⁻¹ * k ∉ N₀`. Introduce `hmem`. Simplify using `[Set.indicator_of_mem hmem] at hm`. Establish `he : φ ((m : K)⁻¹ * k) = φ' ((m : K)⁻¹ * k)`.

Assume the negation of the conclusion as `hne`. Conclude with `hnot (hsub hne)`. Rewrite using `[← he, hinv _ (M.inv_mem m.2) k]`. Use `show φ k = ∫⁻ m : M, φ' ((m : K)⁻¹ * k) ∂μM`. Rewrite using `[this, lintegral_const, h1, mul_one]`.
-/
theorem exists_measurable_invariant_modification_of_closedSubgroup :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K] (M : Subgroup K) (μK : Measure K),
    IsClosed (M : Set K) → μK.IsHaarMeasure → ∀ φ : K → ℝ≥0∞, AEMeasurable φ μK → (∀ m ∈ M, ∀ k : K, φ (m * k) = φ k) →
    ∃ ψ : K → ℝ≥0∞, ∃ N : Set K, Measurable ψ ∧ MeasurableSet N ∧ μK N = 0 ∧ (∀ m ∈ M, ∀ k : K, m * k ∈ N ↔ k ∈ N) ∧
      (∀ m ∈ M, ∀ k : K, ψ (m * k) = ψ k) ∧ ∀ k, k ∉ N → φ k = ψ k := by
  intro K _ _ _ _ _ _ _ _ M μK hM hμ φ hφ hinv
  haveI := hμ
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hM.isCompact
  haveI : BorelSpace M := Subtype.borelSpace _
  obtain ⟨μM, hH, h1⟩ : ∃ μM : Measure M, μM.IsHaarMeasure ∧ μM Set.univ = 1 :=
    ⟨Measure.haarMeasure ⊤, inferInstance, by simpa using Measure.haarMeasure_self (G := M) (K₀ := ⊤)⟩
  haveI := hH
  haveI : IsProbabilityMeasure μM := ⟨h1⟩
  have hφ'm : Measurable (hφ.mk φ) := hφ.measurable_mk
  have hN₀m : MeasurableSet (toMeasurable μK {x | φ x ≠ hφ.mk φ x}) := measurableSet_toMeasurable _ _
  have hN₀0 : μK (toMeasurable μK {x | φ x ≠ hφ.mk φ x}) = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hφ.ae_eq_mk
  have hsub : {x | φ x ≠ hφ.mk φ x} ⊆ toMeasurable μK {x | φ x ≠ hφ.mk φ x} := subset_toMeasurable _ _
  generalize toMeasurable μK {x | φ x ≠ hφ.mk φ x} = N₀ at hN₀m hN₀0 hsub
  generalize hφ.mk φ = φ' at hφ'm hsub
  have hmul : Measurable (fun p : K × M => ((p.2 : K))⁻¹ * p.1) :=
    ((measurable_subtype_coe.comp measurable_snd).inv).mul measurable_fst
  have hind : Measurable (N₀.indicator (1 : K → ℝ≥0∞)) := measurable_one.indicator hN₀m
  have hψm : Measurable (fun k : K => ∫⁻ m : M, φ' ((m : K)⁻¹ * k) ∂μM) :=
    (hφ'm.comp hmul).lintegral_prod_right'
  have hhm : Measurable (fun k : K => ∫⁻ m : M, N₀.indicator 1 ((m : K)⁻¹ * k) ∂μM) :=
    (hind.comp hmul).lintegral_prod_right'
  have inv_avg : ∀ g : K → ℝ≥0∞, ∀ m₀ ∈ M, ∀ k,
      ∫⁻ m : M, g ((m : K)⁻¹ * (m₀ * k)) ∂μM = ∫⁻ m : M, g ((m : K)⁻¹ * k) ∂μM := by
    intro g m₀ hm₀ k
    rw [← lintegral_mul_left_eq_self _ (⟨m₀, hm₀⟩ : M)]
    congr 1; ext m
    simp [mul_assoc]
  refine ⟨fun k => ∫⁻ m : M, φ' ((m : K)⁻¹ * k) ∂μM,
    {k | ∫⁻ m : M, N₀.indicator 1 ((m : K)⁻¹ * k) ∂μM ≠ 0}, hψm,
    hhm (measurableSet_singleton 0).compl, ?_, ?_, ?_, ?_⟩
  · have hint : ∫⁻ k, ∫⁻ m : M, N₀.indicator 1 ((m : K)⁻¹ * k) ∂μM ∂μK = 0 := by
      rw [lintegral_lintegral_swap (f := fun k (m : M) => N₀.indicator (1 : K → ℝ≥0∞) ((m : K)⁻¹ * k))
        (hind.comp hmul).aemeasurable]
      have : ∀ m : M, ∫⁻ k, N₀.indicator (1 : K → ℝ≥0∞) ((m : K)⁻¹ * k) ∂μK = 0 := by
        intro m
        rw [lintegral_mul_left_eq_self (fun k => N₀.indicator (1 : K → ℝ≥0∞) k), lintegral_indicator_one hN₀m, hN₀0]
      simp [this]
    have := (lintegral_eq_zero_iff hhm).mp hint
    rw [Filter.EventuallyEq, ae_iff] at this
    simpa using this
  · intro m hm k
    simp only [Set.mem_setOf_eq, inv_avg _ m hm k]
  · intro m hm k
    exact inv_avg _ m hm k
  · intro k hk
    have hk0 : ∫⁻ m : M, N₀.indicator 1 ((m : K)⁻¹ * k) ∂μM = 0 := by simpa using hk
    have hmk : Measurable (fun m : M => N₀.indicator (1 : K → ℝ≥0∞) ((m : K)⁻¹ * k)) :=
      hind.comp (measurable_subtype_coe.inv.mul_const k)
    have hae := (lintegral_eq_zero_iff hmk).mp hk0
    have : ∫⁻ m : M, φ' ((m : K)⁻¹ * k) ∂μM = ∫⁻ _m : M, φ k ∂μM := by
      apply lintegral_congr_ae
      filter_upwards [hae] with m hm
      have hnot : (m : K)⁻¹ * k ∉ N₀ := by
        intro hmem
        simp [Set.indicator_of_mem hmem] at hm
      have he : φ ((m : K)⁻¹ * k) = φ' ((m : K)⁻¹ * k) := by
        by_contra hne
        exact hnot (hsub hne)
      rw [← he, hinv _ (M.inv_mem m.2) k]
    show φ k = ∫⁻ m : M, φ' ((m : K)⁻¹ * k) ∂μM
    rw [this, lintegral_const, h1, mul_one]

end GlobalTheory
