import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.CutOff

/- English proof (translation)
Establish `h : ∀ z : R, ∃ V : Set R, IsClopen V ∧ IsCompact V ∧ z ∈ V`. Introduce `z`. Take `⟨K, hK, hKz⟩` from `exists_compact_mem_nhds z`. Take `⟨V, hV, hzV, hVK⟩` from `loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hKz`. Conclude with `⟨V, hV, hK.of_isClosed_subset hV.isClosed hVK, hzV⟩`.

Use `choose V hVc hVk hzV using h`. Take `⟨t, -, ht⟩` from `hZ.elim_nhds_subcover V (fun z _ => (hVc z).isOpen.mem_nhds (hzV z))`. Conclude with `⟨⋃ z ∈ t, V z, isClopen_biUnion_finset fun z _ => hVc z, t.isCompact_biUnion fun z _ => hVk z, ht⟩`.
-/
theorem exists_isClopen_isCompact_superset {R : Type} [TopologicalSpace R] [LocallyCompactSpace R]
    [T2Space R] [TotallyDisconnectedSpace R] {Z : Set R} (hZ : IsCompact Z) :
    ∃ U : Set R, IsClopen U ∧ IsCompact U ∧ Z ⊆ U := by
  classical
  have h : ∀ z : R, ∃ V : Set R, IsClopen V ∧ IsCompact V ∧ z ∈ V := by
    intro z
    obtain ⟨K, hK, hKz⟩ := exists_compact_mem_nhds z
    obtain ⟨V, hV, hzV, hVK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hKz
    exact ⟨V, hV, hK.of_isClosed_subset hV.isClosed hVK, hzV⟩
  choose V hVc hVk hzV using h
  obtain ⟨t, -, ht⟩ := hZ.elim_nhds_subcover V (fun z _ => (hVc z).isOpen.mem_nhds (hzV z))
  exact ⟨⋃ z ∈ t, V z, isClopen_biUnion_finset fun z _ => hVc z,
    t.isCompact_biUnion fun z _ => hVk z, ht⟩

/- English proof (translation)
Take `⟨V, hV, hVU⟩` from `compact_open_separated_mul_left hUk hUo subset_rfl`. Use `⟨V ∩ V⁻¹, inter_mem hV (inv_mem_nhds_one R hV), ?_⟩` and prove the remaining obligations. Introduce and unpack `w ⟨hw, hw'⟩ x`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `: w⁻¹ * (w * x) ∈ U` using `hVU (Set.mul_mem_mul (Set.mem_inv.1 hw') h)`. Simplify using `using this`. Introduce `h`. Conclude with `hVU (Set.mul_mem_mul hw h)`.
-/
theorem exists_nhds_one_mul_mem_iff {R : Type} [Group R] [TopologicalSpace R]
    [IsTopologicalGroup R] {U : Set R} (hUo : IsOpen U) (hUk : IsCompact U) :
    ∃ W ∈ 𝓝 (1 : R), ∀ w ∈ W, ∀ x, w * x ∈ U ↔ x ∈ U := by
  obtain ⟨V, hV, hVU⟩ := compact_open_separated_mul_left hUk hUo subset_rfl
  refine ⟨V ∩ V⁻¹, inter_mem hV (inv_mem_nhds_one R hV), ?_⟩
  rintro w ⟨hw, hw'⟩ x
  constructor
  · intro h
    have : w⁻¹ * (w * x) ∈ U := hVU (Set.mul_mem_mul (Set.mem_inv.1 hw') h)
    simpa using this
  · intro h
    exact hVU (Set.mul_mem_mul hw h)

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ U`. Use `filter_upwards [hU.isOpen.mem_nhds hx] with y hy`. Simplify using `[hx, hy]`.

Use `filter_upwards [hU.isClosed.isOpen_compl.mem_nhds hx] with y hy`. Simplify `hy)]` using `[hx, Set.notMem_compl_iff.not.1 (by simpa`.
-/
theorem isLocallyConstant_indicator_one {R : Type} [TopologicalSpace R] {U : Set R}
    (hU : IsClopen U) : IsLocallyConstant (U.indicator (fun _ => (1 : ℝ))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx] with y hy
    simp [hx, hy]
  · filter_upwards [hU.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [hx, Set.notMem_compl_iff.not.1 (by simpa using hy)]

/- English proof (translation)
Introduce `R S _ _ _ _ _ _ _ _ _ _ _ i hi ν _ Z hZ`. Take `⟨U, hUc, hUk, hZU⟩` from `exists_isClopen_isCompact_superset hZ`. Take `⟨W, hW, hWU⟩` from `exists_nhds_one_mul_mem_iff hUc.isOpen hUk`. Use `set β : R → ℝ := U.indicator (fun _ => (1 : ℝ)) with hβ`. Establish `hβlc : IsLocallyConstant β` using `isLocallyConstant_indicator_one hUc`.

Establish `hβc : Continuous β` using `hβlc.continuous`. Establish `hβ0 : ∀ x, 0 ≤ β x` using `fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x`. Use `set F : R → ℝ := fun g => ∫ s, β (g * i s) ∂ν with hF`. Establish `hFinv : ∀ g t, F (g * i t) = F g`. Introduce `g t`.

Use `integral_mul_left_eq_self (μ := ν) (fun s => β (g * i s)) t` as an intermediate fact. Simplify `this` using `[hF, mul_assoc, map_mul]`. Establish `hβmul : ∀ w ∈ W, ∀ x, β (w * x) = β x`. Introduce `w hw x`. Simplify using `[hβ, Set.indicator, hWU w hw x]`.

Establish `hFW : ∀ w ∈ W, ∀ g, F (w * g) = F g`. Introduce `w hw g`. Simplify using `only [hF, mul_assoc, hβmul w hw]`. Establish `hFlc : IsLocallyConstant F`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`.

Introduce `g`. Establish `hc : Tendsto (fun y => y * g⁻¹) (𝓝 g) (𝓝 1)`. Simplify using `using (continuous_mul_right g⁻¹).tendsto g`. Use `filter_upwards [hc hW] with y hy`. Use `hFW _ hy g` as an intermediate fact.

Rewrite `this` using `[inv_mul_cancel_right]`. Then use the resulting hypothesis. Establish `hFpos : ∀ g ∈ U, 0 < F g`. Introduce `g hg`. Establish `hcont : Continuous (fun s => β (g * i s))` using `hβc.comp (continuous_const.mul hi.continuous)`. Establish `hKc : IsCompact (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U))` using `hi.isCompact_preimage ((Homeomorph.mulLeft g).isCompact_preimage.2 hUk)`.

Establish `hKcl : IsClosed (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U))` using `(hUc.isClosed.preimage (Homeomorph.mulLeft g).continuous).preimage hi.continuous`. Establish `hsupp : HasCompactSupport (fun s => β (g * i s))`. Use `HasCompactSupport.intro' hKc hKcl fun x hx => ?_` and prove the remaining obligations. Establish `hx' : g * i x ∉ U` using `hx`. Simplify using `[hβ, hx']`.

Conclude with `hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hsupp (fun s => hβ0 _) (by simp [hβ, hg])`. Use `⟨fun g => β g / F g, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `IsLocallyConstant.comp₂ hβlc hFlc (· / ·)`. Use `HasCompactSupport.intro hUk fun x hx => ?_` and prove the remaining obligations. Simplify using `[hβ, hx]`.

Introduce `g`. Conclude with `div_nonneg (hβ0 g) (integral_nonneg fun s => hβ0 _)`. Introduce `z hz s₀`. Establish `h1 : ∫ s, β (z * i s₀ * i s) / F (z * i s₀ * i s) ∂ν = ∫ s, β (z * i s) / F (z * i s) ∂ν`. Use `integral_mul_left_eq_self (μ := ν) (fun s => β (z * i s) / F (z * i s)) s₀` as an intermediate fact.

Simplify `this` using `[mul_assoc, map_mul]`. Rewrite using `[h1]`. Establish `h2 : ∀ s, β (z * i s) / F (z * i s) = β (z * i s) / F z` using `fun s => by rw [hFinv]`. Repeatedly rewrite using `[h2]`. Rewrite using `[integral_div]`.

Conclude with `div_self (hFpos z (hZU hz)).ne'`.
-/
theorem exists_cutoff : ∀ (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S] (i : S →* R), Topology.IsClosedEmbedding i → ∀ (ν : Measure S) [ν.IsHaarMeasure] (Z : Set R), IsCompact Z → ∃ α : R → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ z ∈ Z, ∀ s₀ : S, ∫ s, α (z * i s₀ * i s) ∂ν = 1 := by
  intro R S _ _ _ _ _ _ _ _ _ _ _ i hi ν _ Z hZ
  classical
  obtain ⟨U, hUc, hUk, hZU⟩ := exists_isClopen_isCompact_superset hZ
  obtain ⟨W, hW, hWU⟩ := exists_nhds_one_mul_mem_iff hUc.isOpen hUk
  set β : R → ℝ := U.indicator (fun _ => (1 : ℝ)) with hβ
  have hβlc : IsLocallyConstant β := isLocallyConstant_indicator_one hUc
  have hβc : Continuous β := hβlc.continuous
  have hβ0 : ∀ x, 0 ≤ β x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  set F : R → ℝ := fun g => ∫ s, β (g * i s) ∂ν with hF
  have hFinv : ∀ g t, F (g * i t) = F g := by
    intro g t
    have := integral_mul_left_eq_self (μ := ν) (fun s => β (g * i s)) t
    simpa [hF, mul_assoc, map_mul] using this
  have hβmul : ∀ w ∈ W, ∀ x, β (w * x) = β x := by
    intro w hw x
    simp [hβ, Set.indicator, hWU w hw x]
  have hFW : ∀ w ∈ W, ∀ g, F (w * g) = F g := by
    intro w hw g
    simp only [hF, mul_assoc, hβmul w hw]
  have hFlc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have hc : Tendsto (fun y => y * g⁻¹) (𝓝 g) (𝓝 1) := by
      simpa using (continuous_mul_right g⁻¹).tendsto g
    filter_upwards [hc hW] with y hy
    have := hFW _ hy g
    rwa [inv_mul_cancel_right] at this
  have hFpos : ∀ g ∈ U, 0 < F g := by
    intro g hg
    have hcont : Continuous (fun s => β (g * i s)) :=
      hβc.comp (continuous_const.mul hi.continuous)
    have hKc : IsCompact (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U)) :=
      hi.isCompact_preimage ((Homeomorph.mulLeft g).isCompact_preimage.2 hUk)
    have hKcl : IsClosed (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U)) :=
      (hUc.isClosed.preimage (Homeomorph.mulLeft g).continuous).preimage hi.continuous
    have hsupp : HasCompactSupport (fun s => β (g * i s)) := by
      refine HasCompactSupport.intro' hKc hKcl fun x hx => ?_
      have hx' : g * i x ∉ U := hx
      simp [hβ, hx']
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hsupp
      (fun s => hβ0 _) (by simp [hβ, hg])
  refine ⟨fun g => β g / F g, ?_, ?_, ?_, ?_⟩
  · exact IsLocallyConstant.comp₂ hβlc hFlc (· / ·)
  · refine HasCompactSupport.intro hUk fun x hx => ?_
    simp [hβ, hx]
  · intro g
    exact div_nonneg (hβ0 g) (integral_nonneg fun s => hβ0 _)
  · intro z hz s₀
    have h1 : ∫ s, β (z * i s₀ * i s) / F (z * i s₀ * i s) ∂ν
        = ∫ s, β (z * i s) / F (z * i s) ∂ν := by
      have := integral_mul_left_eq_self (μ := ν) (fun s => β (z * i s) / F (z * i s)) s₀
      simpa [mul_assoc, map_mul] using this
    rw [h1]
    have h2 : ∀ s, β (z * i s) / F (z * i s) = β (z * i s) / F z := fun s => by rw [hFinv]
    simp_rw [h2]
    rw [integral_div]
    exact div_self (hFpos z (hZU hz)).ne'

end GlobalTheory.CutOff
