import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj

open MeasureTheory

namespace GlobalTheory.Cusp.SemidirectConst

/- English proof (translation)
Introduce `N N₁ _ _ _ _ _ _ _ _ _ _ Δ _ μ _ _ D hD s π hπ hπs hπΔ`. Use `⟨fun u₀ => ?_⟩` and prove the remaining obligations. Use extensionality with `B hB`. Establish `hP : MeasurableSet (π ⁻¹' B)` using `hπ.measurable hB`. Rewrite using `[Measure.map_apply (measurable_mul_const u₀) hB, Measure.map_apply hπ.measurable hB, Measure.map_apply hπ.measurable (measurable_mul_const u₀ hB), Measure.restrict_apply hP, Measure.restrict_apply (hπ.measurable (measurable_mul_const u₀ hB))]`.

Establish `e1 : π ⁻¹' ((· * u₀) ⁻¹' B) ∩ D = (· * s u₀) ⁻¹' (π ⁻¹' B ∩ (· * (s u₀)⁻¹) ⁻¹' D)`. Use extensionality with `v`. Simplify using `[map_mul, hπs]`. Establish `hD' : IsFundamentalDomain Δ ((· * (s u₀)⁻¹) ⁻¹' D) μ` using `hD.preimage_of_equiv (measurePreserving_mul_right μ (s u₀)⁻¹).quasiMeasurePreserving Function.bijective_id fun γ x => mul_assoc _ _ _`. Rewrite using `[e1, measure_preimage_mul_right]`.

Conclude with `hD'.measure_set_eq hD hP fun δ => by`. Use extensionality with `v`. Simplify using `[Subgroup.smul_def, map_mul, hπΔ δ δ.2]`.
-/
theorem map_restrict_isMulRightInvariant : ∀ (N N₁ : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
    [Group N₁] [TopologicalSpace N₁] [IsTopologicalGroup N₁] [MeasurableSpace N₁] [BorelSpace N₁]
    (Δ : Subgroup N) [Countable Δ] (μ : Measure N) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (D : Set N),
    IsFundamentalDomain Δ D μ → ∀ (s : N₁ →* N) (π : N →* N₁), Continuous π → (∀ u, π (s u) = u) →
    (∀ δ ∈ Δ, π δ = 1) → ((μ.restrict D).map π).IsMulRightInvariant := by
  intro N N₁ _ _ _ _ _ _ _ _ _ _ Δ _ μ _ _ D hD s π hπ hπs hπΔ
  refine ⟨fun u₀ => ?_⟩
  ext B hB
  have hP : MeasurableSet (π ⁻¹' B) := hπ.measurable hB
  rw [Measure.map_apply (measurable_mul_const u₀) hB, Measure.map_apply hπ.measurable hB,
    Measure.map_apply hπ.measurable (measurable_mul_const u₀ hB), Measure.restrict_apply hP,
    Measure.restrict_apply (hπ.measurable (measurable_mul_const u₀ hB))]
  have e1 : π ⁻¹' ((· * u₀) ⁻¹' B) ∩ D = (· * s u₀) ⁻¹' (π ⁻¹' B ∩ (· * (s u₀)⁻¹) ⁻¹' D) := by
    ext v; simp [map_mul, hπs]
  have hD' : IsFundamentalDomain Δ ((· * (s u₀)⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv (measurePreserving_mul_right μ (s u₀)⁻¹).quasiMeasurePreserving Function.bijective_id
      fun γ x => mul_assoc _ _ _
  rw [e1, measure_preimage_mul_right]
  exact hD'.measure_set_eq hD hP fun δ => by
    ext v; simp [Subgroup.smul_def, map_mul, hπΔ δ δ.2]

open scoped Pointwise in

/- English proof (translation)
Introduce `N N₁ _ _ _ _ _ _ _ _ _ _ _ Δ _ μ _ D hD s π hs hπ hπs hK`. Take `⟨K, hK, hKs⟩` from `hK`. Use `⟨fun C hC => ?_⟩` and prove the remaining obligations. Establish `hm : MeasurableSet (π ⁻¹' C)` using `hπ.measurable hC.measurableSet`. Rewrite using `[Measure.map_apply hπ.measurable hC.measurableSet, Measure.restrict_apply hm]`.

Establish `hL : IsCompact ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C))` using `(hK.prod hC).image (by fun_prop)`. Establish `hsub : π ⁻¹' C ∩ D ⊆ ⋃ g : Δ, (g • ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) ∩ D)`. Introduce and unpack `v ⟨hv, hvD⟩`. Take `⟨δ, hδ, hδK⟩` from `hKs (v * (s (π v))⁻¹) (by rw [map_mul, map_inv, hπs, mul_inv_cancel])`. Use `Set.mem_iUnion.2 ⟨⟨δ, hδ⟩⁻¹, Set.mem_smul_set.2 ⟨δ * v, ⟨(δ * (v * (s (π v))⁻¹), π v), ⟨hδK, hv⟩, ?_⟩, ?_⟩, hvD⟩` and prove the remaining obligations.

Simplify using `[mul_assoc]`. Simplify using `[Subgroup.smul_def]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem map_restrict_isFiniteMeasureOnCompacts : ∀ (N N₁ : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
    [Group N₁] [TopologicalSpace N₁] [IsTopologicalGroup N₁] [T2Space N₁] [MeasurableSpace N₁] [BorelSpace N₁]
    (Δ : Subgroup N) [Countable Δ] (μ : Measure N) [μ.IsHaarMeasure] (D : Set N),
    IsFundamentalDomain Δ D μ → ∀ (s : N₁ →* N) (π : N →* N₁), Continuous s → Continuous π → (∀ u, π (s u) = u) →
    (∃ K : Set N, IsCompact K ∧ ∀ v, π v = 1 → ∃ δ ∈ Δ, δ * v ∈ K) →
    IsFiniteMeasureOnCompacts ((μ.restrict D).map π) := by
  intro N N₁ _ _ _ _ _ _ _ _ _ _ _ Δ _ μ _ D hD s π hs hπ hπs hK
  obtain ⟨K, hK, hKs⟩ := hK
  refine ⟨fun C hC => ?_⟩
  have hm : MeasurableSet (π ⁻¹' C) := hπ.measurable hC.measurableSet
  rw [Measure.map_apply hπ.measurable hC.measurableSet, Measure.restrict_apply hm]
  have hL : IsCompact ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) := (hK.prod hC).image (by fun_prop)
  have hsub : π ⁻¹' C ∩ D ⊆ ⋃ g : Δ, (g • ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) ∩ D) := by
    rintro v ⟨hv, hvD⟩
    obtain ⟨δ, hδ, hδK⟩ := hKs (v * (s (π v))⁻¹) (by rw [map_mul, map_inv, hπs, mul_inv_cancel])
    refine Set.mem_iUnion.2 ⟨⟨δ, hδ⟩⁻¹, Set.mem_smul_set.2 ⟨δ * v, ⟨(δ * (v * (s (π v))⁻¹), π v), ⟨hδK, hv⟩, ?_⟩, ?_⟩, hvD⟩
    · simp [mul_assoc]
    · simp [Subgroup.smul_def]
  calc μ (π ⁻¹' C ∩ D) ≤ μ (⋃ g : Δ, (g • ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) ∩ D)) := measure_mono hsub
    _ ≤ ∑' g : Δ, μ (g • ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) ∩ D) := measure_iUnion_le _
    _ = μ ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) := (hD.measure_eq_tsum _).symm
    _ < ⊤ := hL.measure_lt_top

/- English proof (translation)
Introduce `G G₁ _ _ Γ N N' Γ₁ N₁ s π hπs hker hsΓ hπΓ A B hA hB v`. Take `⟨γ₁, hγ₁, hγ₁u⟩` from `hB (π v)`. Take `⟨δ, hδ, hδu⟩` from `hA (s γ₁ * v)`. Establish `hδΓ : ((δ : N) : G) ∈ Γ` using `(Subgroup.mem_subgroupOf.1 δ.2).1`. Establish `hδ1 : π δ = 1` using `(hker _).2 (Subgroup.mem_subgroupOf.1 δ.2).2`.

Establish `hsγ : ((s γ₁ : N) : G) ∈ Γ` using `hsΓ _ (Subgroup.mem_subgroupOf.1 γ₁.2)`. Use `⟨⟨δ * s γ₁, Subgroup.mem_subgroupOf.2 (by simpa using mul_mem hδΓ hsγ)⟩, ⟨?_, ?_⟩, fun γ hγ => ?_⟩` and prove the remaining obligations. Simplify `hδ` using `[mul_assoc]`. Express the relevant statement in the definitionally equal form `π (δ * s γ₁ * v) ∈ B`. Rewrite using `[map_mul, map_mul, hδ1, hπs, one_mul]` and apply the resulting hypothesis.

Establish `hγΓ : (((γ : N)) : G) ∈ Γ` using `Subgroup.mem_subgroupOf.1 γ.2`. Establish `hπγ : (⟨π γ, Subgroup.mem_subgroupOf.2 (hπΓ _ hγΓ)⟩ : Γ₁.subgroupOf N₁) = γ₁` using `hγ₁u _ (by simpa [map_mul] using hγ.2)`. Establish `hπγ' : π γ = γ₁` using `congrArg Subtype.val hπγ`. Establish `hmem : (γ : N) * (s γ₁)⁻¹ ∈ (Γ ⊓ N').subgroupOf N` using `Subgroup.mem_subgroupOf.2 ⟨by simpa using mul_mem hγΓ (inv_mem hsγ), (hker _).1 (by rw [map_mul, map_inv, hπs, hπγ', mul_inv_cancel])⟩`. Establish `e : (⟨_, hmem⟩ : (Γ ⊓ N').subgroupOf N) = δ` using `hδu _ (by simpa [mul_assoc] using hγ.1)`.

Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(γ : N) = δ * s γ₁`. Rewrite using `[← e]`. Simplify using the standard rewrite rules.
-/
theorem existsUnique_inter_preimage : ∀ (G G₁ : Type) [Group G] [Group G₁] (Γ N N' : Subgroup G) (Γ₁ N₁ : Subgroup G₁) (s : N₁ →* N) (π : N →* N₁),
    (∀ u, π (s u) = u) → (∀ v, π v = 1 ↔ (v : G) ∈ N') →
    (∀ u : N₁, (u : G₁) ∈ Γ₁ → (s u : G) ∈ Γ) → (∀ v : N, (v : G) ∈ Γ → (π v : G₁) ∈ Γ₁) →
    ∀ (A : Set N) (B : Set N₁), (∀ v : N, ∃! δ : (Γ ⊓ N').subgroupOf N, (δ : N) * v ∈ A) →
    (∀ u : N₁, ∃! γ : Γ₁.subgroupOf N₁, (γ : N₁) * u ∈ B) →
    ∀ v : N, ∃! γ : Γ.subgroupOf N, (γ : N) * v ∈ A ∩ π ⁻¹' B := by
  intro G G₁ _ _ Γ N N' Γ₁ N₁ s π hπs hker hsΓ hπΓ A B hA hB v
  obtain ⟨γ₁, hγ₁, hγ₁u⟩ := hB (π v)
  obtain ⟨δ, hδ, hδu⟩ := hA (s γ₁ * v)
  have hδΓ : ((δ : N) : G) ∈ Γ := (Subgroup.mem_subgroupOf.1 δ.2).1
  have hδ1 : π δ = 1 := (hker _).2 (Subgroup.mem_subgroupOf.1 δ.2).2
  have hsγ : ((s γ₁ : N) : G) ∈ Γ := hsΓ _ (Subgroup.mem_subgroupOf.1 γ₁.2)
  refine ⟨⟨δ * s γ₁, Subgroup.mem_subgroupOf.2 (by simpa using mul_mem hδΓ hsγ)⟩, ⟨?_, ?_⟩, fun γ hγ => ?_⟩
  · simpa [mul_assoc] using hδ
  · change π (δ * s γ₁ * v) ∈ B
    rwa [map_mul, map_mul, hδ1, hπs, one_mul]
  · have hγΓ : (((γ : N)) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
    have hπγ : (⟨π γ, Subgroup.mem_subgroupOf.2 (hπΓ _ hγΓ)⟩ : Γ₁.subgroupOf N₁) = γ₁ :=
      hγ₁u _ (by simpa [map_mul] using hγ.2)
    have hπγ' : π γ = γ₁ := congrArg Subtype.val hπγ
    have hmem : (γ : N) * (s γ₁)⁻¹ ∈ (Γ ⊓ N').subgroupOf N := Subgroup.mem_subgroupOf.2
      ⟨by simpa using mul_mem hγΓ (inv_mem hsγ), (hker _).1 (by rw [map_mul, map_inv, hπs, hπγ', mul_inv_cancel])⟩
    have e : (⟨_, hmem⟩ : (Γ ⊓ N').subgroupOf N) = δ := hδu _ (by simpa [mul_assoc] using hγ.1)
    refine Subtype.ext ?_
    change (γ : N) = δ * s γ₁
    rw [← e]; simp

end GlobalTheory.Cusp.SemidirectConst

open GlobalTheory.Cusp.SemidirectConst

open GlobalTheory.AutomorphicL2Unitary in

/- English proof (translation)
Introduce `G G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Γ N N' Γ₁ N₁ _ _ _ _ hle hc hc' hc₁ s π hs hπ hπs hker hsΓ hπΓ ψ hψc hψN' hψΓ μ₁ 𝓕₁ hμ₁ h𝓕₁ h1 x`. Use `haveI := hμ₁`. Establish `: Countable Γ` using `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Establish `: DiscreteTopology (Γ ⊓ N' : Subgroup G)` using `.of_continuous_injective (f := Subgroup.inclusion (inf_le_left : Γ ⊓ N' ≤ Γ)) (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)`. Take `⟨Δ, hΔ⟩ : ∃ Δ : Subgroup N, Δ = (Γ ⊓ N').subgroupOf N` from `⟨_, rfl⟩`.

Substitute `hΔ` using the available equality. Establish `: Countable ((Γ ⊓ N').subgroupOf N)` using `Function.Injective.countable (f := fun δ : (Γ ⊓ N').subgroupOf N => (⟨δ.1.1, (Subgroup.mem_subgroupOf.1 δ.2).1⟩ : Γ)) fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => z.1) h))`. Set `μ : Measure N` to `Measure.haar`. Use `hc.isMulRightInvariant μ` as an intermediate fact. Use `hc₁.isMulRightInvariant μ₁` as an intermediate fact.

Establish `hD'` using `isFundamentalDomain_stdDom ((Γ ⊓ N').subgroupOf N) μ`. Establish `hπΔ : ∀ δ ∈ (Γ ⊓ N').subgroupOf N, π δ = 1` using `fun δ hδ => (hker δ).2 (Subgroup.mem_subgroupOf.1 hδ).2`. Take `⟨ν, hν⟩ : ∃ ν, ν = (μ.restrict (stdDom ((Γ ⊓ N').subgroupOf N))).map π` from `⟨_, rfl⟩`. Establish `: ν.IsMulRightInvariant` using `hν ▸ map_restrict_isMulRightInvariant N N₁ _ μ _ hD' s π hπ hπs hπΔ`. Establish `: IsFiniteMeasureOnCompacts ν` using `hν ▸ map_restrict_isFiniteMeasureOnCompacts N N₁ _ μ _ hD' s π hs hπ hπs (by`.

Take `⟨K, hK, hKs⟩` from `hc'`. Use `⟨Subgroup.inclusion hle '' K, hK.image (continuous_subtype_val.subtype_mk _), fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hγK⟩` from `hKs ⟨v, (hker v).1 hv⟩`. Use `⟨Subgroup.inclusion hle γ, Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 hγ, γ.2⟩, ⟨_, hγK, ?_⟩⟩` and prove the remaining obligations. Conclude with `Subtype.ext (by simp))`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hνc⟩ : ∃ c : NNReal, ν = c • μ₁ := by`. Take `⟨a, e1⟩ : ∃ a : NNReal, ν.inv = a • μ₁` from `⟨_, Measure.isMulLeftInvariant_eq_smul ν.inv μ₁⟩`. Take `⟨b, e2⟩ : ∃ b : NNReal, μ₁.inv = b • μ₁` from `⟨_, Measure.isMulLeftInvariant_eq_smul μ₁.inv μ₁⟩`. Use `⟨a * b, ?_⟩` and prove the remaining obligations. Rewrite using `[← Measure.inv_inv ν, e1, Measure.inv_def, Measure.map_smul, ← Measure.inv_def, e2, smul_smul]`.

Establish `hD₁` using `isFundamentalDomain_stdDom (Γ₁.subgroupOf N₁) μ₁`. Establish `hmD₁` using `measurableSet_stdDom (Γ₁.subgroupOf N₁)`. Establish `hm𝓕 : MeasurableSet (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁))` using `(measurableSet_stdDom _).inter (hπ.measurable hmD₁)`. Establish `h𝓕 : IsFundamentalDomain (Γ.subgroupOf N) (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) μ` using `.mk' hm𝓕.nullMeasurableSet (existsUnique_inter_preimage G G₁ Γ N N' Γ₁ N₁ s π hπs hker hsΓ hπΓ _ _ (existsUnique_stdDom _) (existsUnique_stdDom _))`. Establish `hg : ∀ v : N, ψ (v * x) = ψ (s (π v) * x)` using `fun v => by`.

Establish `hm : ((v * (s (π v))⁻¹ : N) : G) ∈ N'` using `(hker _).1 (by rw [map_mul, map_inv, hπs, mul_inv_cancel])`. Use `hψN' _ hm ((s (π v) : G) * x)` as an intermediate fact. Rewrite using `[← this, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]`. Establish `hgc : Continuous fun u : N₁ => ψ (s u * x)` using `by fun_prop`. Establish `hint : ∫ v in stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁), ψ (v * x) ∂μ = ∫ u in stdDom (Γ₁.subgroupOf N₁), ψ (s u * x) ∂ν`.

Rewrite using `[hν, setIntegral_map hmD₁ hgc.aestronglyMeasurable hπ.aemeasurable, Measure.restrict_restrict (hπ.measurable hmD₁), Set.inter_comm (π ⁻¹' _)]`. Conclude with `integral_congr_ae (.of_forall hg)`. Establish `hmeas : μ (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) = ν (stdDom (Γ₁.subgroupOf N₁))`. Rewrite using `[hν, Measure.map_apply hπ.measurable hmD₁, Measure.restrict_apply (hπ.measurable hmD₁), Set.inter_comm]`. Establish `hinv1 : ∀ (γ : Γ₁.subgroupOf N₁) (u : N₁), ψ (s (γ • u) * x) = ψ (s u * x)` using `fun γ u => by`.

Rewrite using `[Subgroup.smul_def, smul_eq_mul, map_mul]`. Simplify using `only [Subgroup.coe_mul, mul_assoc]`. Conclude with `hψΓ _ (hsΓ _ (Subgroup.mem_subgroupOf.1 γ.2)) (s γ).2 _`. Establish `hDe : μ₁ (stdDom (Γ₁.subgroupOf N₁)) = 1` using `(hD₁.measure_eq h𝓕₁).trans h1`. Rewrite using `[GlobalTheory.Cusp.Stages.constTermOn_eq' h𝓕 (fun γ hγ n => by`.

Simplify using `only [Subgroup.coe_mul, mul_assoc]`. Conclude with `hψΓ _ (Subgroup.mem_subgroupOf.1 hγ) γ.2 _),`. Use the proof step `hint, measureReal_def, hmeas, hνc, Measure.smul_apply, hDe, Measure.restrict_smul, integral_smul_nnreal_measure,`. Use the proof step `hD₁.setIntegral_eq h𝓕₁ hinv1]`. Establish `hc0 : c ≠ 0`.

Use `h𝓕.measure_ne_zero (NeZero.ne μ)` as an intermediate fact. Rewrite `this` using `[hmeas, hνc, Measure.smul_apply, hDe]`. Introduce and unpack `rfl`. Simplify using `at this`. Use `first`.

Consider the case `(rw [ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal, NNReal.smul_def, smul_smul, inv_mul_cancel₀ (NNReal.coe_ne_zero.2 hc0), one_smul]; done)`. Consider the case `(simp [hc0, NNReal.smul_def, smul_smul]; done)`. Consider the case `(field_simp; done)`.
-/
theorem GlobalTheory.Cusp.constTermOn_eq_integral_semidirect : ∀ (G G₁ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (Γ N N' : Subgroup G) (Γ₁ N₁ : Subgroup G₁) [DiscreteTopology Γ] [DiscreteTopology Γ₁] [LocallyCompactSpace N] [LocallyCompactSpace N₁],
    N' ≤ N → GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' → GlobalTheory.Cusp.Cocompact Γ₁ N₁ →
    ∀ (s : N₁ →* N) (π : N →* N₁), Continuous s → Continuous π → (∀ u, π (s u) = u) → (∀ v, π v = 1 ↔ (v : G) ∈ N') →
    (∀ u : N₁, (u : G₁) ∈ Γ₁ → (s u : G) ∈ Γ) → (∀ v : N, (v : G) ∈ Γ → (π v : G₁) ∈ Γ₁) →
    ∀ ψ : G → ℂ, Continuous ψ → (∀ a ∈ N', ∀ y, ψ (a * y) = ψ y) → (∀ γ ∈ Γ, γ ∈ N → ∀ y, ψ (γ * y) = ψ y) →
    ∀ (μ₁ : Measure N₁) (𝓕₁ : Set N₁), μ₁.IsHaarMeasure → IsFundamentalDomain (Γ₁.subgroupOf N₁) 𝓕₁ μ₁ → μ₁ 𝓕₁ = 1 →
    ∀ x : G, GlobalTheory.Cusp.constTermOn Γ N ψ x = ∫ u in 𝓕₁, ψ ((s u : G) * x) ∂μ₁ := by
  intro G G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Γ N N' Γ₁ N₁ _ _ _ _ hle hc hc' hc₁ s π hs hπ hπs hker hsΓ hπΓ ψ hψc hψN' hψΓ
    μ₁ 𝓕₁ hμ₁ h𝓕₁ h1 x
  haveI := hμ₁
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : DiscreteTopology (Γ ⊓ N' : Subgroup G) :=
    .of_continuous_injective (f := Subgroup.inclusion (inf_le_left : Γ ⊓ N' ≤ Γ))
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Subgroup N, Δ = (Γ ⊓ N').subgroupOf N := ⟨_, rfl⟩
  subst hΔ
  have : Countable ((Γ ⊓ N').subgroupOf N) := Function.Injective.countable
    (f := fun δ : (Γ ⊓ N').subgroupOf N => (⟨δ.1.1, (Subgroup.mem_subgroupOf.1 δ.2).1⟩ : Γ))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => z.1) h))
  let μ : Measure N := Measure.haar
  have := hc.isMulRightInvariant μ
  have := hc₁.isMulRightInvariant μ₁
  have hD' := isFundamentalDomain_stdDom ((Γ ⊓ N').subgroupOf N) μ
  have hπΔ : ∀ δ ∈ (Γ ⊓ N').subgroupOf N, π δ = 1 := fun δ hδ => (hker δ).2 (Subgroup.mem_subgroupOf.1 hδ).2
  obtain ⟨ν, hν⟩ : ∃ ν, ν = (μ.restrict (stdDom ((Γ ⊓ N').subgroupOf N))).map π := ⟨_, rfl⟩
  have : ν.IsMulRightInvariant := hν ▸ map_restrict_isMulRightInvariant N N₁ _ μ _ hD' s π hπ hπs hπΔ
  have : IsFiniteMeasureOnCompacts ν := hν ▸ map_restrict_isFiniteMeasureOnCompacts N N₁ _ μ _ hD' s π hs hπ hπs (by
    obtain ⟨K, hK, hKs⟩ := hc'
    refine ⟨Subgroup.inclusion hle '' K, hK.image (continuous_subtype_val.subtype_mk _), fun v hv => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKs ⟨v, (hker v).1 hv⟩
    refine ⟨Subgroup.inclusion hle γ, Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 hγ, γ.2⟩, ⟨_, hγK, ?_⟩⟩
    exact Subtype.ext (by simp))
  obtain ⟨c, hνc⟩ : ∃ c : NNReal, ν = c • μ₁ := by
    obtain ⟨a, e1⟩ : ∃ a : NNReal, ν.inv = a • μ₁ := ⟨_, Measure.isMulLeftInvariant_eq_smul ν.inv μ₁⟩
    obtain ⟨b, e2⟩ : ∃ b : NNReal, μ₁.inv = b • μ₁ := ⟨_, Measure.isMulLeftInvariant_eq_smul μ₁.inv μ₁⟩
    refine ⟨a * b, ?_⟩
    rw [← Measure.inv_inv ν, e1, Measure.inv_def, Measure.map_smul, ← Measure.inv_def, e2, smul_smul]
  have hD₁ := isFundamentalDomain_stdDom (Γ₁.subgroupOf N₁) μ₁
  have hmD₁ := measurableSet_stdDom (Γ₁.subgroupOf N₁)
  have hm𝓕 : MeasurableSet (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) :=
    (measurableSet_stdDom _).inter (hπ.measurable hmD₁)
  have h𝓕 : IsFundamentalDomain (Γ.subgroupOf N) (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) μ :=
    .mk' hm𝓕.nullMeasurableSet (existsUnique_inter_preimage G G₁ Γ N N' Γ₁ N₁ s π hπs hker hsΓ hπΓ _ _ (existsUnique_stdDom _) (existsUnique_stdDom _))
  have hg : ∀ v : N, ψ (v * x) = ψ (s (π v) * x) := fun v => by
    have hm : ((v * (s (π v))⁻¹ : N) : G) ∈ N' := (hker _).1 (by rw [map_mul, map_inv, hπs, mul_inv_cancel])
    have := hψN' _ hm ((s (π v) : G) * x)
    rw [← this, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]
  have hgc : Continuous fun u : N₁ => ψ (s u * x) := by fun_prop
  have hint : ∫ v in stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁), ψ (v * x) ∂μ =
      ∫ u in stdDom (Γ₁.subgroupOf N₁), ψ (s u * x) ∂ν := by
    rw [hν, setIntegral_map hmD₁ hgc.aestronglyMeasurable hπ.aemeasurable, Measure.restrict_restrict (hπ.measurable hmD₁),
      Set.inter_comm (π ⁻¹' _)]
    exact integral_congr_ae (.of_forall hg)
  have hmeas : μ (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) = ν (stdDom (Γ₁.subgroupOf N₁)) := by
    rw [hν, Measure.map_apply hπ.measurable hmD₁, Measure.restrict_apply (hπ.measurable hmD₁), Set.inter_comm]
  have hinv1 : ∀ (γ : Γ₁.subgroupOf N₁) (u : N₁), ψ (s (γ • u) * x) = ψ (s u * x) := fun γ u => by
    rw [Subgroup.smul_def, smul_eq_mul, map_mul]
    simp only [Subgroup.coe_mul, mul_assoc]
    exact hψΓ _ (hsΓ _ (Subgroup.mem_subgroupOf.1 γ.2)) (s γ).2 _
  have hDe : μ₁ (stdDom (Γ₁.subgroupOf N₁)) = 1 := (hD₁.measure_eq h𝓕₁).trans h1
  rw [GlobalTheory.Cusp.Stages.constTermOn_eq' h𝓕 (fun γ hγ n => by
      simp only [Subgroup.coe_mul, mul_assoc]
      exact hψΓ _ (Subgroup.mem_subgroupOf.1 hγ) γ.2 _),
    hint, measureReal_def, hmeas, hνc, Measure.smul_apply, hDe, Measure.restrict_smul, integral_smul_nnreal_measure,
    hD₁.setIntegral_eq h𝓕₁ hinv1]
  have hc0 : c ≠ 0 := by
    have := h𝓕.measure_ne_zero (NeZero.ne μ)
    rw [hmeas, hνc, Measure.smul_apply, hDe] at this
    rintro rfl; simp at this
  first
  | (rw [ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal, NNReal.smul_def, smul_smul,
      inv_mul_cancel₀ (NNReal.coe_ne_zero.2 hc0), one_smul]; done)
  | (simp [hc0, NNReal.smul_def, smul_smul]; done)
  | (field_simp; done)
