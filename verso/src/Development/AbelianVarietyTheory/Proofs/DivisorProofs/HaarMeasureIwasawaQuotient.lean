import Mathlib
import GroundTheory.AutomorphicForms.HaarSK
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PSemidirectHaar

open MeasureTheory Measure Topology Set Function TopologicalSpace GroundTheory.Automorphic.HaarSK
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.NAK

/- English proof (translation)
Take `⟨A, hA, hA1⟩` from `exists_compact_mem_nhds (1 : G)`. Use `set B : Set G := A * (K : Set G) with hB`. Establish `hBc : IsCompact B` using `hA.mul hK`. Establish `hAB : A ⊆ B` using `fun a ha => ⟨a, ha, 1, K.one_mem, mul_one a⟩`. Establish `hpos : μ B ≠ 0` using `(measure_pos_of_mem_nhds μ (Filter.mem_of_superset hA1 hAB)).ne'`.

Establish `hfin : μ B ≠ ∞` using `hBc.measure_lt_top.ne`. Establish `hpre : (fun x => x * k) ⁻¹' B = B`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, hB, Set.mem_mul, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, k', hk', he⟩`. Conclude with `⟨a, ha, k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), by rw [← mul_assoc, he, mul_inv_cancel_right]⟩`. Introduce and unpack `⟨a, ha, k', hk', he⟩`. Conclude with `⟨a, ha, k' * k, K.mul_mem hk' hk, by rw [← mul_assoc, he]⟩`. Establish `h` using `map_right_mul_eq_modularCharacterFun_smul μ k`.

Establish `h2` using `congrArg (fun m : Measure G => m B) h`. Simplify using `only [coe_nnreal_smul_apply] at h2`. Rewrite `h2` using `[map_apply (measurable_mul_const k) hBc.measurableSet, hpre]`. Establish `h3 : modularCharacterFun k = 1`. Establish `: (modularCharacterFun k : ℝ≥0∞) * μ B = 1 * μ B` using `by rw [one_mul]; exact h2.symm`.

Conclude with `(ENNReal.mul_left_inj hpos hfin).1 this` after adjusting the coercions. Rewrite using `[h, h3, one_smul]`.
-/
theorem map_mul_right_eq_of_mem_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hK : IsCompact (K : Set G)) (k : G) (hk : k ∈ K) :
    μ.map (· * k) = μ := by
  obtain ⟨A, hA, hA1⟩ := exists_compact_mem_nhds (1 : G)
  set B : Set G := A * (K : Set G) with hB
  have hBc : IsCompact B := hA.mul hK
  have hAB : A ⊆ B := fun a ha => ⟨a, ha, 1, K.one_mem, mul_one a⟩
  have hpos : μ B ≠ 0 := (measure_pos_of_mem_nhds μ (Filter.mem_of_superset hA1 hAB)).ne'
  have hfin : μ B ≠ ∞ := hBc.measure_lt_top.ne
  have hpre : (fun x => x * k) ⁻¹' B = B := by
    ext x
    simp only [Set.mem_preimage, hB, Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, k', hk', he⟩
      exact ⟨a, ha, k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), by rw [← mul_assoc, he, mul_inv_cancel_right]⟩
    · rintro ⟨a, ha, k', hk', he⟩
      exact ⟨a, ha, k' * k, K.mul_mem hk' hk, by rw [← mul_assoc, he]⟩
  have h := map_right_mul_eq_modularCharacterFun_smul μ k
  have h2 := congrArg (fun m : Measure G => m B) h
  simp only [coe_nnreal_smul_apply] at h2
  rw [map_apply (measurable_mul_const k) hBc.measurableSet, hpre] at h2
  have h3 : modularCharacterFun k = 1 := by
    have : (modularCharacterFun k : ℝ≥0∞) * μ B = 1 * μ B := by rw [one_mul]; exact h2.symm
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 this
  rw [h, h3, one_smul]

/- English proof (translation)
Establish `: LocallyCompactSpace S` using `hS.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: SecondCountableTopology S` using `TopologicalSpace.Subtype.secondCountableTopology _`. Establish `: CompactSpace K` using `isCompact_iff_compactSpace.mp hK`. Establish `hLc : IsCompact ((inter S K : Subgroup S) : Set S)`. Rewrite using `[Subgroup.coe_subgroupOf]`.

Conclude with `hS.isClosedEmbedding_subtypeVal.isCompact_preimage hK`. Establish `: CompactSpace (inter S K)` using `isCompact_iff_compactSpace.mp hLc`. Use `set mL : Measure (inter S K) := haarMeasure ⊤ with hmL`. Establish `: IsProbabilityMeasure mL` using `⟨by simpa using haarMeasure_self (K₀ := (⊤ : PositiveCompacts (inter S K)))⟩`. Establish `: (rmk mL hS hK hSK μ).IsMulLeftInvariant` using `isMulLeftInvariant_rmk mL hS hK hSK μ`.

Use `set c₀ := haarScalarFactor (rmk mL hS hK hSK μ) μS`. Establish `hc₀ : rmk mL hS hK hSK μ = c₀ • μS` using `isMulLeftInvariant_eq_smul _ _`. Establish `: IsFiniteMeasure μK` using `inferInstance`. Establish `hKpos : 0 < (μK univ).toReal` using `ENNReal.toReal_pos (IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty) (measure_ne_top _ _)`. Establish `hfin : IsFiniteMeasureOnCompacts (map (mulMap S K) (μS.prod μK))` using `⟨fun C hC => by`.

Rewrite using `[map_apply continuous_mulMap.measurable hC.measurableSet]`. Conclude with `(isCompact_preimage_mulMap hS hK hC).measure_lt_top⟩`. Establish `key : ∀ φ : CompactlySupportedContinuousMap G ℝ, (μK univ).toReal * ∫ g, φ g ∂μ = (c₀ : ℝ) * ∫ p, φ (mulMap S K p) ∂(μS.prod μK)`. Introduce `φ`. Use `set φK : G → ℝ := fun g => ∫ k, φ (g * k) ∂μK with hφK`.

Establish `hφKc : Continuous φK`. Use `continuous_parametric_integral_of_continuous (μ := μK) (f := fun (g : G) (k : K) => φ (g * k)) (φ.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))) isCompact_univ` as an intermediate fact. Simplify using `using this`. Establish `hφKinv : ∀ g (k : K), φK (g * k) = φK g`. Introduce `g k`.

Simplify using `only [hφK]`. Use `integral_mul_left_eq_self (μ := μK) (fun k' : K => φ (g * k')) k` as an intermediate fact. Simplify `this` using `only [Subgroup.coe_mul, mul_assoc]`. Establish `hφKcs : HasCompactSupport φK`. Use `HasCompactSupport.intro ((IsCompact.prod φ.hasCompactSupport hK).image (f := fun q : G × G => q.1 * q.2⁻¹) (by fun_prop)) ?_` and prove the remaining obligations.

Introduce `g hg`. Establish `h0 : ∀ k : K, φ (g * k) = 0` using `fun k => by`. Assume the negation of the conclusion as `h`. Conclude with `hg ⟨(g * k, k), ⟨subset_tsupport _ h, k.2⟩, by simp⟩`. Simplify using `[hφK, h0]`.

Establish `hint : ∫ g, φK g ∂μ = (μK univ).toReal * ∫ g, φ g ∂μ`. Establish `hF : Integrable (fun q : G × K => φ (q.1 * q.2)) (μ.prod μK)`. Use `(φ.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))).integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Use `HasCompactSupport.intro (((IsCompact.prod φ.hasCompactSupport hK).image (f := fun q : G × G => q.1 * q.2⁻¹) (by fun_prop)).prod (isCompact_univ (X := K))) ?_` and prove the remaining obligations. Introduce and unpack `⟨g, k⟩ hq`.

Assume the negation of the conclusion as `h`. Conclude with `hq ⟨⟨(g * k, k), ⟨subset_tsupport _ h, k.2⟩, by simp⟩, mem_univ _⟩`. Rewrite using `[hφK, integral_integral_swap hF]`. Establish `hri : ∀ k : K, ∫ g, φ (g * (k : G)) ∂μ = ∫ g, φ g ∂μ` using `fun k => by conv_rhs => rw [← hright (k : G) k.2]`. Rewrite using `[integral_map (measurable_mul_const _).aemeasurable (map_continuous φ).aestronglyMeasurable]`.

Repeatedly rewrite using `[hri]`. Rewrite using `[integral_const, smul_eq_mul, measureReal_def]`. Establish `hu : ∀ s, ∀ m ∈ inter S K, (fun s : S => φK s) (s * m) = (fun s : S => φK s) s`. Introduce `s m hm`. Simplify using `using hφKinv (s : G) ⟨(m : G), (GroundTheory.Automorphic.HaarSK.mem_inter_iff).1 hm⟩`.

Use `set uCc : CompactlySupportedContinuousMap S ℝ := { toFun := fun s => φK s continuous_toFun := hφKc.comp continuous_subtype_val hasCompactSupport' := hφKcs.comp_isClosedEmbedding hS.isClosedEmbedding_subtypeVal }`. Establish `hflat : flat mL uCc = fun s : S => φK (s : G)` using `flat_eq_self (u := fun s : S => φK (s : G)) hu`. Establish `hlift : lift hSK (flat mL uCc) = φK`. Rewrite using `[hflat]`. Use function extensionality and compare the values at `g`.

Take `⟨p, rfl⟩` from `hSK g`. Rewrite using `[lift_mulMap hu]`. Conclude with `(hφKinv _ _).symm`. Establish `h1` using `integral_rmk mL hS hK hSK μ uCc`. Rewrite `h1` using `[funcL_apply, hlift, hint, hc₀, integral_smul_nnreal_measure]`.

Rewrite using `[← h1]`. Establish `hFS : Integrable (fun p : S × K => φ (mulMap S K p)) (μS.prod μK)` using `(φ.continuous.comp continuous_mulMap).integrable_of_hasCompactSupport (isCompact_preimage_mulMap hS hK φ.hasCompactSupport |>.of_isClosed_subset (isClosed_tsupport _) (by`. Introduce `p hp`. Conclude with `(tsupport_comp_subset_preimage φ continuous_mulMap) hp))`. Rewrite using `[integral_prod _ hFS]`.

Both sides reduce to the same expression. Use `set c : ℝ≥0 := ⟨c₀ / (μK univ).toReal, div_nonneg c₀.2 hKpos.le⟩ with hc`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hreg : (map (mulMap S K) (μS.prod μK)).Regular` using `inferInstance`. Establish `: (c • map (mulMap S K) (μS.prod μK)).Regular`.

Rewrite using `[ENNReal.smul_def]`. Conclude with `Measure.Regular.smul ENNReal.coe_ne_top`. Apply `Measure.ext_of_integral_eq_on_compactlySupported` to reduce the goal to its premises. Introduce `φ`. Rewrite using `[integral_smul_nnreal_measure, integral_map continuous_mulMap.aemeasurable (map_continuous φ).aestronglyMeasurable, NNReal.smul_def, smul_eq_mul]`.

Use `show _ = ((c₀ : ℝ) / (μK univ).toReal) * _`. Rewrite using `[div_mul_eq_mul_div, ← key, mul_div_cancel_left₀ _ hKpos.ne']`.
-/
theorem exists_eq_smul_map_mulMap_of_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (S K : Subgroup G)
    (μ : Measure G) [μ.IsHaarMeasure] (hright : ∀ k ∈ K, μ.map (· * k) = μ)
    (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G)) (hSK : Surjective (mulMap S K))
    (μS : Measure S) [μS.IsHaarMeasure] (μK : Measure K) [μK.IsHaarMeasure] :
    ∃ c : ℝ≥0, μ = c • map (mulMap S K) (μS.prod μK) := by
  have : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hLc : IsCompact ((inter S K : Subgroup S) : Set S) := by
    rw [Subgroup.coe_subgroupOf]
    exact hS.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have : CompactSpace (inter S K) := isCompact_iff_compactSpace.mp hLc
  set mL : Measure (inter S K) := haarMeasure ⊤ with hmL
  have : IsProbabilityMeasure mL := ⟨by simpa using haarMeasure_self (K₀ := (⊤ : PositiveCompacts (inter S K)))⟩
  have : (rmk mL hS hK hSK μ).IsMulLeftInvariant := isMulLeftInvariant_rmk mL hS hK hSK μ
  set c₀ := haarScalarFactor (rmk mL hS hK hSK μ) μS
  have hc₀ : rmk mL hS hK hSK μ = c₀ • μS := isMulLeftInvariant_eq_smul _ _
  have : IsFiniteMeasure μK := inferInstance
  have hKpos : 0 < (μK univ).toReal :=
    ENNReal.toReal_pos (IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty)
      (measure_ne_top _ _)

  have hfin : IsFiniteMeasureOnCompacts (map (mulMap S K) (μS.prod μK)) := ⟨fun C hC => by
    rw [map_apply continuous_mulMap.measurable hC.measurableSet]
    exact (isCompact_preimage_mulMap hS hK hC).measure_lt_top⟩
  have key : ∀ φ : CompactlySupportedContinuousMap G ℝ,
      (μK univ).toReal * ∫ g, φ g ∂μ = (c₀ : ℝ) * ∫ p, φ (mulMap S K p) ∂(μS.prod μK) := by
    intro φ
    set φK : G → ℝ := fun g => ∫ k, φ (g * k) ∂μK with hφK
    have hφKc : Continuous φK := by
      have := continuous_parametric_integral_of_continuous (μ := μK)
        (f := fun (g : G) (k : K) => φ (g * k))
        (φ.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
        isCompact_univ
      simpa using this
    have hφKinv : ∀ g (k : K), φK (g * k) = φK g := by
      intro g k
      simp only [hφK]
      have := integral_mul_left_eq_self (μ := μK) (fun k' : K => φ (g * k')) k
      simpa only [Subgroup.coe_mul, mul_assoc] using this
    have hφKcs : HasCompactSupport φK := by
      refine HasCompactSupport.intro ((IsCompact.prod φ.hasCompactSupport hK).image
        (f := fun q : G × G => q.1 * q.2⁻¹) (by fun_prop)) ?_
      intro g hg
      have h0 : ∀ k : K, φ (g * k) = 0 := fun k => by
        by_contra h
        exact hg ⟨(g * k, k), ⟨subset_tsupport _ h, k.2⟩, by simp⟩
      simp [hφK, h0]

    have hint : ∫ g, φK g ∂μ = (μK univ).toReal * ∫ g, φ g ∂μ := by
      have hF : Integrable (fun q : G × K => φ (q.1 * q.2)) (μ.prod μK) := by
        refine (φ.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp
          continuous_snd))).integrable_of_hasCompactSupport ?_
        refine HasCompactSupport.intro (((IsCompact.prod φ.hasCompactSupport hK).image
          (f := fun q : G × G => q.1 * q.2⁻¹) (by fun_prop)).prod (isCompact_univ (X := K))) ?_
        rintro ⟨g, k⟩ hq
        by_contra h
        exact hq ⟨⟨(g * k, k), ⟨subset_tsupport _ h, k.2⟩, by simp⟩, mem_univ _⟩
      rw [hφK, integral_integral_swap hF]
      have hri : ∀ k : K, ∫ g, φ (g * (k : G)) ∂μ = ∫ g, φ g ∂μ := fun k => by
        conv_rhs => rw [← hright (k : G) k.2]
        rw [integral_map (measurable_mul_const _).aemeasurable (map_continuous φ).aestronglyMeasurable]
      simp_rw [hri]
      rw [integral_const, smul_eq_mul, measureReal_def]

    have hu : ∀ s, ∀ m ∈ inter S K, (fun s : S => φK s) (s * m) = (fun s : S => φK s) s := by
      intro s m hm
      simpa using hφKinv (s : G) ⟨(m : G), (GroundTheory.Automorphic.HaarSK.mem_inter_iff).1 hm⟩
    set uCc : CompactlySupportedContinuousMap S ℝ :=
      { toFun := fun s => φK s
        continuous_toFun := hφKc.comp continuous_subtype_val
        hasCompactSupport' := hφKcs.comp_isClosedEmbedding hS.isClosedEmbedding_subtypeVal }
    have hflat : flat mL uCc = fun s : S => φK (s : G) := flat_eq_self (u := fun s : S => φK (s : G)) hu
    have hlift : lift hSK (flat mL uCc) = φK := by
      rw [hflat]
      funext g
      obtain ⟨p, rfl⟩ := hSK g
      rw [lift_mulMap hu]
      exact (hφKinv _ _).symm
    have h1 := integral_rmk mL hS hK hSK μ uCc
    rw [funcL_apply, hlift, hint, hc₀, integral_smul_nnreal_measure] at h1
    rw [← h1]
    have hFS : Integrable (fun p : S × K => φ (mulMap S K p)) (μS.prod μK) :=
      (φ.continuous.comp continuous_mulMap).integrable_of_hasCompactSupport
        (isCompact_preimage_mulMap hS hK φ.hasCompactSupport |>.of_isClosed_subset
          (isClosed_tsupport _) (by
            intro p hp
            exact (tsupport_comp_subset_preimage φ continuous_mulMap) hp))
    rw [integral_prod _ hFS]
    rfl
  set c : ℝ≥0 := ⟨c₀ / (μK univ).toReal, div_nonneg c₀.2 hKpos.le⟩ with hc
  refine ⟨c, ?_⟩
  have hreg : (map (mulMap S K) (μS.prod μK)).Regular := inferInstance
  have : (c • map (mulMap S K) (μS.prod μK)).Regular := by
    rw [ENNReal.smul_def]
    exact Measure.Regular.smul ENNReal.coe_ne_top
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_smul_nnreal_measure, integral_map continuous_mulMap.aemeasurable
    (map_continuous φ).aestronglyMeasurable, NNReal.smul_def, smul_eq_mul]
  show _ = ((c₀ : ℝ) / (μK univ).toReal) * _
  rw [div_mul_eq_mul_div, ← key, mul_div_cancel_left₀ _ hKpos.ne']

/- English proof (translation)
Introduce `G Λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N K j δ μG μN μK μΛ hG hN hK hΛ hKc hj hδ hconj hemb hmod hdec`. Use `set f : N × Λ → G := fun p => (p.1 : G) * j p.2 with hf`. Set `P : Subgroup G` to `{ carrier := Set.range f mul_mem' := by`. Introduce and unpack `_ _ ⟨⟨n, x⟩, rfl⟩ ⟨⟨n', x'⟩, rfl⟩`. Use `⟨(⟨(n : G) * (j x * n' * (j x)⁻¹), N.mul_mem n.2 (hconj x n' n'.2)⟩, x * x'), ?_⟩` and prove the remaining obligations.

Simplify using `only [hf, map_mul]`. Use `group`. Use the proof step `one_mem' := ⟨(1, 1), by simp [hf]⟩`. Use the proof step `inv_mem' := by`. Introduce and unpack `_ ⟨⟨n, x⟩, rfl⟩`.

Use `⟨(⟨j x⁻¹ * (n : G)⁻¹ * (j x⁻¹)⁻¹, hconj x⁻¹ _ (N.inv_mem n.2)⟩, x⁻¹), ?_⟩` and prove the remaining obligations. Simplify using `only [hf, map_inv]`. Use `group }`. Establish `hmemP : ∀ g, g ∈ P ↔ g ∈ Set.range f` using `fun g => Iff.rfl`. Establish `hPc : IsClosed (P : Set G)` using `hemb.isClosed_range`.

Establish `hNc : IsClosed (N : Set G)`. Establish `h` using `hemb.isClosedMap _ (isClosed_univ.prod (isClosed_singleton (x := (1 : Λ))))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Conclude with `⟨(⟨g, hg⟩, 1), ⟨trivial, rfl⟩, by simp [hf]⟩`. Introduce and unpack `⟨⟨n, x⟩, ⟨-, hx⟩, rfl⟩`. Simplify using `only [Set.mem_singleton_iff] at hx`. Substitute `hx` using the available equality.

Simplify using `[hf]`. Establish `hNP : N ≤ P` using `fun n hn => (hmemP n).2 ⟨(⟨n, hn⟩, 1), by simp [hf]⟩`. Establish `hjP : ∀ x, j x ∈ P` using `fun x => (hmemP _).2 ⟨(1, x), by simp [hf]⟩`. Set `e : N × Λ ≃ₜ Set.range f` to `hemb.isEmbedding.toHomeomorph`. Establish `he : ∀ q : Set.range f, f (e.symm q) = q` using `fun q => congrArg Subtype.val (e.apply_symm_apply q)`.

Set `β : P → Λ` to `fun p => (e.symm ⟨p.1, (hmemP p.1).1 p.2⟩).2`. Establish `hβc : Continuous β` using `continuous_snd.comp (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))`. Establish `hβ : ∀ p : P, (p : G) * (j (β p))⁻¹ ∈ N`. Introduce `p`. Establish `h1 : f (e.symm ⟨p.1, (hmemP p.1).1 p.2⟩) = p` using `he _`.

Establish `h2 : (p : G) * (j (β p))⁻¹ = ((e.symm ⟨p.1, (hmemP p.1).1 p.2⟩).1 : G)` using `by conv_lhs => rw [← h1]`. Simplify using `[hf, β]`. Rewrite using `[h2]`. Conclude with `(e.symm ⟨p.1, (hmemP p.1).1 p.2⟩).1.2`. Establish `hτH : ∀ t, j t ∈ N → t = 1`.

Introduce `t ht`. Use `hemb.injective (show f (⟨j t, ht⟩, 1) = f (1, t) by simp [hf])` as an intermediate fact. Conclude with `(congrArg Prod.snd this).symm`. Establish `hδmul : ∀ x, δ x * δ x⁻¹ = 1` using `fun x => by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `hδ0 : ∀ x, δ x ≠ 0` using `fun x h => by simpa [h] using hδmul x`.

Establish `hδinv : ∀ x, (δ x)⁻¹ = δ x⁻¹` using `fun x => inv_eq_of_mul_eq_one_right (hδmul x)`. Use `set δF : Λ → ℝ≥0 := fun x => δ x⁻¹ with hδF`. Establish `hδFc : Continuous δF` using `hδ.comp continuous_inv`. Establish `hδF' : ∀ x, ((δF x : ℝ≥0) : ℝ≥0∞) = ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹` using `fun x => by`. Rewrite using `[hδF]`.

Simplify using `only`. Rewrite using `[← hδinv, ENNReal.coe_inv (hδ0 x)]`. Establish `hmodF : ∀ (t : Λ) (g : G → ℝ≥0∞), Measurable g → ∫⁻ x, g (j t * x * (j t)⁻¹) ∂μN = δF t * ∫⁻ x, g x ∂μN` using `fun t g hg => by`. Rewrite using `[hmod t g hg, hδF']`. Use `haveI : LocallyCompactSpace P := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Use `haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology P := inferInstanceAs (SecondCountableTopology (P : Set G))`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc`. Set `μP : Measure P` to `Measure.haar`. Take `⟨c1, hc1, hP⟩` from `GroundTheory.Heights₂.Heights.FiniteCovolume.SemidirectHaar.proof G Λ P N hPc hNc hNP j β δF hj hβc hδFc hjP hconj hτH hβ μP μN μΛ hmodF`.

Establish `hright : ∀ k ∈ K, μG.map (· * k) = μG` using `fun k hk => map_mul_right_eq_of_mem_compact μG K hKc k hk`. Establish `hsurj : Surjective (mulMap P K)`. Introduce `g`. Take `⟨n, hn, x, k, hk, rfl⟩` from `hdec g`. Conclude with `⟨(⟨(n : G) * j x, (hmemP _).2 ⟨(⟨n, hn⟩, x), rfl⟩⟩, ⟨k, hk⟩), rfl⟩`.

Take `⟨c2, hc2⟩` from `exists_eq_smul_map_mulMap_of_right P K μG hright hPc hKc hsurj μP μK`. Establish `hc2ne : c2 ≠ 0`. Introduce and unpack `rfl`. Establish `h0` using `(isOpen_univ (X := G)).measure_pos μG univ_nonempty`. Rewrite `h0` using `[hc2]`.

Simplify using `at h0`. Use `⟨(c2 : ℝ≥0∞) * c1, mul_ne_zero (by exact_mod_cast hc2ne) (by exact_mod_cast hc1), ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top, ?_⟩` and prove the remaining obligations. Introduce `φ hφ`. Establish `hm : Measurable (mulMap P K)` using `(measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)`. Rewrite using `[hc2, lintegral_smul_measure, lintegral_map hφ hm, lintegral_prod_symm (fun q => φ (mulMap P K q)) (hφ.comp hm).aemeasurable, ENNReal.smul_def, smul_eq_mul, mul_assoc]`.

Use `congr 1`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.coe_ne_top]`. Use `lintegral_congr fun k => ?_` and prove the remaining obligations. Establish `h` using `hP (fun g => φ (g * k)) (hφ.comp (measurable_mul_const _))`. Use `show ∫⁻ p, φ ((p : G) * k) ∂μP = _`.

Rewrite using `[h]`. Use `congr 1`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Rewrite using `[lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (by exact_mod_cast hδ0 t)), hδF', mul_comm]`.
-/
theorem lintegral_eq_nak : ∀ (G Λ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [Group Λ] [TopologicalSpace Λ] [IsTopologicalGroup Λ] [LocallyCompactSpace Λ]
    [SecondCountableTopology Λ] [T2Space Λ] [MeasurableSpace Λ] [BorelSpace Λ]
    (N K : Subgroup G) (j : Λ →* G) (δ : Λ →* ℝ≥0) (μG : Measure G) (μN : Measure N) (μK : Measure K) (μΛ : Measure Λ),
    μG.IsHaarMeasure → μN.IsHaarMeasure → μK.IsHaarMeasure → μΛ.IsHaarMeasure →
    IsCompact (K : Set G) → Continuous j → Continuous δ →
    (∀ x, ∀ n ∈ N, j x * n * (j x)⁻¹ ∈ N) →
    IsClosedEmbedding (fun p : N × Λ => (p.1 : G) * j p.2) →
    (∀ x (f : G → ℝ≥0∞), Measurable f → ∫⁻ n, f (j x * n.1 * (j x)⁻¹) ∂μN = ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹ * ∫⁻ n, f n.1 ∂μN) →
    (∀ g, ∃ n ∈ N, ∃ x, ∃ k ∈ K, g = n * j x * k) →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μG = c * ∫⁻ k, ∫⁻ x, ∫⁻ n, φ (n.1 * j x * k.1) * ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹ ∂μN ∂μΛ ∂μK := by
  intro G Λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N K j δ μG μN μK μΛ hG hN hK hΛ hKc hj hδ hconj hemb hmod hdec
  classical
  set f : N × Λ → G := fun p => (p.1 : G) * j p.2 with hf

  let P : Subgroup G :=
    { carrier := Set.range f
      mul_mem' := by
        rintro _ _ ⟨⟨n, x⟩, rfl⟩ ⟨⟨n', x'⟩, rfl⟩
        refine ⟨(⟨(n : G) * (j x * n' * (j x)⁻¹), N.mul_mem n.2 (hconj x n' n'.2)⟩, x * x'), ?_⟩
        simp only [hf, map_mul]
        group
      one_mem' := ⟨(1, 1), by simp [hf]⟩
      inv_mem' := by
        rintro _ ⟨⟨n, x⟩, rfl⟩
        refine ⟨(⟨j x⁻¹ * (n : G)⁻¹ * (j x⁻¹)⁻¹, hconj x⁻¹ _ (N.inv_mem n.2)⟩, x⁻¹), ?_⟩
        simp only [hf, map_inv]
        group }
  have hmemP : ∀ g, g ∈ P ↔ g ∈ Set.range f := fun g => Iff.rfl
  have hPc : IsClosed (P : Set G) := hemb.isClosed_range
  have hNc : IsClosed (N : Set G) := by
    have h := hemb.isClosedMap _ (isClosed_univ.prod (isClosed_singleton (x := (1 : Λ))))
    convert h using 1
    ext g
    constructor
    · intro hg
      exact ⟨(⟨g, hg⟩, 1), ⟨trivial, rfl⟩, by simp [hf]⟩
    · rintro ⟨⟨n, x⟩, ⟨-, hx⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp [hf]
  have hNP : N ≤ P := fun n hn => (hmemP n).2 ⟨(⟨n, hn⟩, 1), by simp [hf]⟩
  have hjP : ∀ x, j x ∈ P := fun x => (hmemP _).2 ⟨(1, x), by simp [hf]⟩

  let e : N × Λ ≃ₜ Set.range f := hemb.isEmbedding.toHomeomorph
  have he : ∀ q : Set.range f, f (e.symm q) = q := fun q => congrArg Subtype.val (e.apply_symm_apply q)
  let β : P → Λ := fun p => (e.symm ⟨p.1, (hmemP p.1).1 p.2⟩).2
  have hβc : Continuous β :=
    continuous_snd.comp (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hβ : ∀ p : P, (p : G) * (j (β p))⁻¹ ∈ N := by
    intro p
    have h1 : f (e.symm ⟨p.1, (hmemP p.1).1 p.2⟩) = p := he _
    have h2 : (p : G) * (j (β p))⁻¹ = ((e.symm ⟨p.1, (hmemP p.1).1 p.2⟩).1 : G) := by
      conv_lhs => rw [← h1]
      simp [hf, β]
    rw [h2]
    exact (e.symm ⟨p.1, (hmemP p.1).1 p.2⟩).1.2
  have hτH : ∀ t, j t ∈ N → t = 1 := by
    intro t ht
    have := hemb.injective (show f (⟨j t, ht⟩, 1) = f (1, t) by simp [hf])
    exact (congrArg Prod.snd this).symm

  have hδmul : ∀ x, δ x * δ x⁻¹ = 1 := fun x => by rw [← map_mul, mul_inv_cancel, map_one]
  have hδ0 : ∀ x, δ x ≠ 0 := fun x h => by simpa [h] using hδmul x
  have hδinv : ∀ x, (δ x)⁻¹ = δ x⁻¹ := fun x => inv_eq_of_mul_eq_one_right (hδmul x)
  set δF : Λ → ℝ≥0 := fun x => δ x⁻¹ with hδF
  have hδFc : Continuous δF := hδ.comp continuous_inv
  have hδF' : ∀ x, ((δF x : ℝ≥0) : ℝ≥0∞) = ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹ := fun x => by
    rw [hδF]
    dsimp only
    rw [← hδinv, ENNReal.coe_inv (hδ0 x)]
  have hmodF : ∀ (t : Λ) (g : G → ℝ≥0∞), Measurable g →
      ∫⁻ x, g (j t * x * (j t)⁻¹) ∂μN = δF t * ∫⁻ x, g x ∂μN := fun t g hg => by
    rw [hmod t g hg, hδF']

  haveI : LocallyCompactSpace P := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology P := inferInstanceAs (SecondCountableTopology (P : Set G))
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let μP : Measure P := Measure.haar
  obtain ⟨c1, hc1, hP⟩ := GroundTheory.Heights₂.Heights.FiniteCovolume.SemidirectHaar.proof G Λ P N hPc hNc hNP j β δF
    hj hβc hδFc hjP hconj hτH hβ μP μN μΛ hmodF

  have hright : ∀ k ∈ K, μG.map (· * k) = μG := fun k hk =>
    map_mul_right_eq_of_mem_compact μG K hKc k hk
  have hsurj : Surjective (mulMap P K) := by
    intro g
    obtain ⟨n, hn, x, k, hk, rfl⟩ := hdec g
    exact ⟨(⟨(n : G) * j x, (hmemP _).2 ⟨(⟨n, hn⟩, x), rfl⟩⟩, ⟨k, hk⟩), rfl⟩
  obtain ⟨c2, hc2⟩ := exists_eq_smul_map_mulMap_of_right P K μG hright hPc hKc hsurj μP μK
  have hc2ne : c2 ≠ 0 := by
    rintro rfl
    have h0 := (isOpen_univ (X := G)).measure_pos μG univ_nonempty
    rw [hc2] at h0
    simp at h0
  refine ⟨(c2 : ℝ≥0∞) * c1, mul_ne_zero (by exact_mod_cast hc2ne) (by exact_mod_cast hc1),
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top, ?_⟩
  intro φ hφ
  have hm : Measurable (mulMap P K) :=
    (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  rw [hc2, lintegral_smul_measure, lintegral_map hφ hm, lintegral_prod_symm (fun q => φ (mulMap P K q)) (hφ.comp hm).aemeasurable,
    ENNReal.smul_def, smul_eq_mul, mul_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun k => ?_
  have h := hP (fun g => φ (g * k)) (hφ.comp (measurable_mul_const _))
  show ∫⁻ p, φ ((p : G) * k) ∂μP = _
  rw [h]
  congr 1
  refine lintegral_congr fun t => ?_
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (by exact_mod_cast hδ0 t)), hδF', mul_comm]

end GlobalTheory.NAK
