import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomainStatement

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

namespace GlobalTheory.UnipQuot

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Take `⟨ψ, hψm, hψi⟩` from `MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated G`. Establish `he` using `measurableEmbedding_embeddingReal (ℕ → Bool)`. Use `set φ : G → ℝ := fun x => embeddingReal (ℕ → Bool) (ψ x) with hφ`. Establish `hφm : Measurable φ` using `he.measurable.comp hψm`. Establish `hφi : Function.Injective φ` using `he.injective.comp hψi`.

Establish `hCm : MeasurableSet C` using `hC.measurableSet`. Use `⟨C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)}, ?_, Set.inter_subset_left, ?_⟩` and prove the remaining obligations. Use `hCm.inter (MeasurableSet.iInter fun γ => ?_)` and prove the remaining obligations. Establish `h1 : MeasurableSet {y : G | (γ : G) * y ∈ C}` using `(measurable_const_mul (γ : G)) hCm`. Establish `h2 : MeasurableSet {y : G | φ y ≤ φ ((γ : G) * y)}` using `measurableSet_le hφm (hφm.comp (measurable_const_mul (γ : G)))`.

Establish `: {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} = {y : G | (γ : G) * y ∈ C}ᶜ ∪ {y : G | φ y ≤ φ ((γ : G) * y)}`. Use extensionality with `y`. Simplify using `[imp_iff_not_or]`. Rewrite using `[this]`. Conclude with `h1.compl.union h2`.

Introduce `x`. Establish `hK : IsCompact ((fun y => y * x⁻¹) '' C)` using `hC.image (continuous_mul_const _)`. Establish `hF` using `hfin _ hK`. Take `⟨γ₀, hγ₀, hγ₀C⟩` from `hcov x`. Establish `hne : ((fun y => y * x⁻¹) '' C ∩ (Γ : Set G)).Nonempty` using `⟨γ₀, ⟨γ₀ * x, hγ₀C, by simp⟩, hγ₀⟩`.

Take `⟨γ, ⟨⟨y, hy, hyγ⟩, hγΓ⟩, hmin⟩` from `Set.exists_min_image _ (fun g => φ (g * x)) hF hne`. Establish `hγx : γ * x ∈ C` using `by rw [← hyγ]; simpa using hy`. Establish `hmem : (⟨γ, hγΓ⟩ : Γ) • x ∈ C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)}`. Use `⟨hγx, Set.mem_iInter.2 fun δ hδ => ?_⟩` and prove the remaining obligations. Establish `hδ' : (δ : G) * (γ * x) ∈ C` using `hδ`.

Use `hmin ((δ : G) * γ) ⟨⟨_, hδ', by simp [mul_assoc]⟩, Γ.mul_mem δ.2 hγΓ⟩` as an intermediate fact. Use `show φ (γ * x) ≤ φ ((δ : G) * (γ * x))`. Simplify `this` using `[mul_assoc]`. Use `⟨⟨γ, hγΓ⟩, hmem, fun δ hδ => ?_⟩` and prove the remaining obligations. Establish `hδC : (δ : G) * x ∈ C` using `hδ.1`.

Establish `h1 : φ ((δ : G) * x) ≤ φ (γ * x)`. Use `Set.mem_iInter.1 hδ.2 ⟨γ * (δ : G)⁻¹, Γ.mul_mem hγΓ (Γ.inv_mem δ.2)⟩` as an intermediate fact. Establish `e : γ * (δ : G)⁻¹ * (δ • x) = γ * x` using `by show γ * (δ : G)⁻¹ * ((δ : G) * x) = γ * x`. Simplify using `[mul_assoc]`. Simplify using `only [Set.mem_ofPred_eq, e] at this`.

Conclude with `this hγx`. Establish `h2 : φ (γ * x) ≤ φ ((δ : G) * x)` using `hmin δ ⟨⟨_, hδC, by simp⟩, δ.2⟩`. Conclude with `Subtype.ext (mul_right_cancel (hφi (le_antisymm h1 h2)))`.
-/
theorem exists_domain (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m : G, ∃ γ ∈ Γ, γ * m ∈ C) :
    ∃ D : Set G, MeasurableSet D ∧ D ⊆ C ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ D := by
  obtain ⟨ψ, hψm, hψi⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated G
  have he := measurableEmbedding_embeddingReal (ℕ → Bool)
  set φ : G → ℝ := fun x => embeddingReal (ℕ → Bool) (ψ x) with hφ
  have hφm : Measurable φ := he.measurable.comp hψm
  have hφi : Function.Injective φ := he.injective.comp hψi
  have hCm : MeasurableSet C := hC.measurableSet
  refine ⟨C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)}, ?_, Set.inter_subset_left, ?_⟩
  · refine hCm.inter (MeasurableSet.iInter fun γ => ?_)
    have h1 : MeasurableSet {y : G | (γ : G) * y ∈ C} := (measurable_const_mul (γ : G)) hCm
    have h2 : MeasurableSet {y : G | φ y ≤ φ ((γ : G) * y)} :=
      measurableSet_le hφm (hφm.comp (measurable_const_mul (γ : G)))
    have : {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} =
        {y : G | (γ : G) * y ∈ C}ᶜ ∪ {y : G | φ y ≤ φ ((γ : G) * y)} := by
      ext y; simp [imp_iff_not_or]
    rw [this]; exact h1.compl.union h2
  · intro x
    have hK : IsCompact ((fun y => y * x⁻¹) '' C) := hC.image (continuous_mul_const _)
    have hF := hfin _ hK
    obtain ⟨γ₀, hγ₀, hγ₀C⟩ := hcov x
    have hne : ((fun y => y * x⁻¹) '' C ∩ (Γ : Set G)).Nonempty :=
      ⟨γ₀, ⟨γ₀ * x, hγ₀C, by simp⟩, hγ₀⟩
    obtain ⟨γ, ⟨⟨y, hy, hyγ⟩, hγΓ⟩, hmin⟩ := Set.exists_min_image _ (fun g => φ (g * x)) hF hne
    have hγx : γ * x ∈ C := by rw [← hyγ]; simpa using hy
    have hmem : (⟨γ, hγΓ⟩ : Γ) • x ∈
        C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} := by
      refine ⟨hγx, Set.mem_iInter.2 fun δ hδ => ?_⟩
      have hδ' : (δ : G) * (γ * x) ∈ C := hδ
      have := hmin ((δ : G) * γ) ⟨⟨_, hδ', by simp [mul_assoc]⟩, Γ.mul_mem δ.2 hγΓ⟩
      show φ (γ * x) ≤ φ ((δ : G) * (γ * x))
      simpa [mul_assoc] using this
    refine ⟨⟨γ, hγΓ⟩, hmem, fun δ hδ => ?_⟩
    have hδC : (δ : G) * x ∈ C := hδ.1
    have h1 : φ ((δ : G) * x) ≤ φ (γ * x) := by
      have := Set.mem_iInter.1 hδ.2 ⟨γ * (δ : G)⁻¹, Γ.mul_mem hγΓ (Γ.inv_mem δ.2)⟩
      have e : γ * (δ : G)⁻¹ * (δ • x) = γ * x := by
        show γ * (δ : G)⁻¹ * ((δ : G) * x) = γ * x
        simp [mul_assoc]
      simp only [Set.mem_ofPred_eq, e] at this
      exact this hγx
    have h2 : φ (γ * x) ≤ φ ((δ : G) * x) := hmin δ ⟨⟨_, hδC, by simp⟩, δ.2⟩
    exact Subtype.ext (mul_right_cancel (hφi (le_antisymm h1 h2)))

/- English proof (translation)
Take `⟨D, hDm, hDC, hD⟩` from `exists_domain Γ hfin C hC hcov`. Use `set μ : Measure G := Measure.haar`. Establish `hfd : IsFundamentalDomain Γ D μ` using `IsFundamentalDomain.mk' hDm.nullMeasurableSet hD`. Establish `hfd' : ∀ g : G, IsFundamentalDomain Γ ((fun y => y * g) ⁻¹' D) μ` using `fun g => IsFundamentalDomain.mk' ((measurable_mul_const g) hDm).nullMeasurableSet fun x => by`. Use `hD (x * g)` as an intermediate fact.

Simplify `this` using `[Subgroup.smul_def, mul_assoc]`. Establish `h0 : μ D ≠ 0` using `hfd.measure_ne_zero (NeZero.ne μ)`. Establish `htop : μ D ≠ ⊤` using `ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono hDC)`. Establish `hinv : ∀ g : G, Measure.map (fun y => y * g) μ = μ`. Introduce `g`.

Establish `: IsFiniteMeasureOnCompacts (Measure.map (fun y => y * g) μ)` using `⟨fun K hK => by`. Rewrite using `[Measure.map_apply (measurable_mul_const g) hK.measurableSet]`. Conclude with `((Homeomorph.mulRight g).isCompact_preimage.2 hK).measure_lt_top⟩`. Establish `h` using `Measure.isMulLeftInvariant_eq_smul (Measure.map (fun y => y * g) μ) μ`. Use `set c := (Measure.map (fun y => y * g) μ).haarScalarFactor μ`.

Establish `h1 : Measure.map (fun y => y * g) μ D = μ D`. Rewrite using `[Measure.map_apply (measurable_mul_const g) hDm]`. Conclude with `(hfd' g).measure_eq hfd`. Rewrite `h1` using `[h]`. Establish `h2 : (c : ENNReal) = 1`.

Establish `: (c : ENNReal) * μ D = 1 * μ D` using `by simpa using h1`. Conclude with `(ENNReal.mul_left_inj h0 htop).1 this`. Establish `h3 : c = 1` using `by exact_mod_cast h2`. Rewrite using `[h, h3, one_smul]`. Use `⟨(μ D)⁻¹ • μ.restrict D, ⟨?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[ENNReal.inv_mul_cancel h0 htop]`. Establish `: Cᶜ ∩ D = ∅`. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]`. Conclude with `fun h1 h2 => h1 (hDC h2)`.

Rewrite using `[Measure.smul_apply, Measure.restrict_apply hC.measurableSet.compl, this]`. Simplify using the standard rewrite rules. Introduce `f hf g`. Rewrite using `[integral_smul_measure, integral_smul_measure]`. Use `congr 1`.

Establish `hemb : MeasurableEmbedding (fun y : G => y * g)` using `measurableEmbedding_mulRight g`. Establish `h1` using `hemb.setIntegral_map (μ := μ) f ((fun y => y * g⁻¹) ⁻¹' D)`. Establish `h2 : (fun y : G => y * g) ⁻¹' ((fun y => y * g⁻¹) ⁻¹' D) = D`. Use extensionality with `y`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[hinv g, h2]`. Rewrite using `[← h1]`. Conclude with `(hfd' g⁻¹).setIntegral_eq hfd fun γ x => hf γ γ.2 x`.
-/
theorem exists_prob [LocallyCompactSpace G] (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m : G, ∃ γ ∈ Γ, γ * m ∈ C) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧
      ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) → ∀ g : G, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν := by
  obtain ⟨D, hDm, hDC, hD⟩ := exists_domain Γ hfin C hC hcov
  set μ : Measure G := Measure.haar
  have hfd : IsFundamentalDomain Γ D μ := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hfd' : ∀ g : G, IsFundamentalDomain Γ ((fun y => y * g) ⁻¹' D) μ := fun g =>
    IsFundamentalDomain.mk' ((measurable_mul_const g) hDm).nullMeasurableSet fun x => by
      have := hD (x * g)
      simpa [Subgroup.smul_def, mul_assoc] using this
  have h0 : μ D ≠ 0 := hfd.measure_ne_zero (NeZero.ne μ)
  have htop : μ D ≠ ⊤ := ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono hDC)
  have hinv : ∀ g : G, Measure.map (fun y => y * g) μ = μ := by
    intro g
    have : IsFiniteMeasureOnCompacts (Measure.map (fun y => y * g) μ) := ⟨fun K hK => by
      rw [Measure.map_apply (measurable_mul_const g) hK.measurableSet]
      exact ((Homeomorph.mulRight g).isCompact_preimage.2 hK).measure_lt_top⟩
    have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun y => y * g) μ) μ
    set c := (Measure.map (fun y => y * g) μ).haarScalarFactor μ
    have h1 : Measure.map (fun y => y * g) μ D = μ D := by
      rw [Measure.map_apply (measurable_mul_const g) hDm]
      exact (hfd' g).measure_eq hfd
    rw [h] at h1
    have h2 : (c : ENNReal) = 1 := by
      have : (c : ENNReal) * μ D = 1 * μ D := by simpa using h1
      exact (ENNReal.mul_left_inj h0 htop).1 this
    have h3 : c = 1 := by exact_mod_cast h2
    rw [h, h3, one_smul]
  refine ⟨(μ D)⁻¹ • μ.restrict D, ⟨?_⟩, ?_, ?_⟩
  · simp [ENNReal.inv_mul_cancel h0 htop]
  · have : Cᶜ ∩ D = ∅ := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h1 h2 => h1 (hDC h2)
    rw [Measure.smul_apply, Measure.restrict_apply hC.measurableSet.compl, this]
    simp
  · intro f hf g
    rw [integral_smul_measure, integral_smul_measure]
    congr 1
    have hemb : MeasurableEmbedding (fun y : G => y * g) := measurableEmbedding_mulRight g
    have h1 := hemb.setIntegral_map (μ := μ) f ((fun y => y * g⁻¹) ⁻¹' D)
    have h2 : (fun y : G => y * g) ⁻¹' ((fun y => y * g⁻¹) ⁻¹' D) = D := by
      ext y; simp
    rw [hinv g, h2] at h1
    rw [← h1]
    exact (hfd' g⁻¹).setIntegral_eq hfd fun γ x => hf γ γ.2 x

/- English proof (translation)
Establish `hce : Topology.IsClosedEmbedding (Subtype.val : N → G)` using `hN.isClosedEmbedding_subtypeVal`. Establish `: LocallyCompactSpace N` using `hce.locallyCompactSpace`. Establish `: SecondCountableTopology N` using `hce.isEmbedding.secondCountableTopology`. Establish `hemb : MeasurableEmbedding (Subtype.val : N → G)` using `hce.measurableEmbedding`. Establish `: Countable (Γ.subgroupOf N)`.

Use `Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨x.1.1, x.2⟩ : Γ)) ?_` and prove the remaining obligations. Introduce `a b h`. Conclude with `Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))`. Take `⟨ν, hν, hνC, hνf⟩` from `exists_prob (Γ.subgroupOf N) (fun K hK => by`. Use `hfin _ (hK.image continuous_subtype_val)` as an intermediate fact.

Use `(this.preimage (f := (Subtype.val : N → G)) Subtype.val_injective.injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hx, hx'⟩`. Conclude with `⟨⟨x, hx, rfl⟩, hx'⟩)`. Use the proof step `(Subtype.val ⁻¹' C) (hce.isCompact_preimage hC) (fun m => by`. Take `⟨γ, h1, h2, h3⟩` from `hcov m m.2`.

Conclude with `⟨⟨γ, h2⟩, h1, h3⟩)`. Use `⟨ν.map Subtype.val, Measure.isProbabilityMeasure_map hemb.measurable.aemeasurable, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hemb.map_apply]`. Conclude with `hνC`. Rewrite using `[hemb.map_apply]`.

Establish `: (Subtype.val : N → G) ⁻¹' (N : Set G)ᶜ = ∅`. Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite using `[this, measure_empty]`. Introduce `f hf g hg`.

Rewrite using `[hemb.integral_map, hemb.integral_map]`. Conclude with `hνf (fun y => f y) (fun γ hγ y => hf γ hγ γ.2 y) ⟨g, hg⟩`.
-/
theorem exists_prob_subgroup [LocallyCompactSpace G] (N Γ : Subgroup G) (hN : IsClosed (N : Set G))
    [Countable Γ] (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m ∈ N, ∃ γ ∈ Γ, γ ∈ N ∧ γ * m ∈ C) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧ ν (N : Set G)ᶜ = 0 ∧
      ∀ f : G → ℂ, (∀ γ ∈ Γ, γ ∈ N → ∀ y, f (γ * y) = f y) →
        ∀ g ∈ N, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν := by
  have hce : Topology.IsClosedEmbedding (Subtype.val : N → G) := hN.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace N := hce.locallyCompactSpace
  have : SecondCountableTopology N := hce.isEmbedding.secondCountableTopology
  have hemb : MeasurableEmbedding (Subtype.val : N → G) := hce.measurableEmbedding
  have : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨x.1.1, x.2⟩ : Γ)) ?_
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  obtain ⟨ν, hν, hνC, hνf⟩ := exists_prob (Γ.subgroupOf N) (fun K hK => by
      have := hfin _ (hK.image continuous_subtype_val)
      refine (this.preimage (f := (Subtype.val : N → G)) Subtype.val_injective.injOn).subset ?_
      rintro x ⟨hx, hx'⟩
      exact ⟨⟨x, hx, rfl⟩, hx'⟩)
    (Subtype.val ⁻¹' C) (hce.isCompact_preimage hC) (fun m => by
      obtain ⟨γ, h1, h2, h3⟩ := hcov m m.2
      exact ⟨⟨γ, h2⟩, h1, h3⟩)
  refine ⟨ν.map Subtype.val, Measure.isProbabilityMeasure_map hemb.measurable.aemeasurable, ?_, ?_, ?_⟩
  · rw [hemb.map_apply]; exact hνC
  · rw [hemb.map_apply]
    have : (Subtype.val : N → G) ⁻¹' (N : Set G)ᶜ = ∅ := by
      ext y; simp
    rw [this, measure_empty]
  · intro f hf g hg
    rw [hemb.integral_map, hemb.integral_map]
    exact hνf (fun y => f y) (fun γ hγ y => hf γ hγ γ.2 y) ⟨g, hg⟩

end General

/- English proof (translation)
Take `⟨h2, hlc, hsc, -⟩` from `GlobalTheory.CongTop.adelic_topology I`. Take `⟨⟨N, hN⟩, hcl, -, -, C, hC, hCN, hcov⟩` from `GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I W hW`. Take `⟨Γ, hΓ, hΓc, hfin, -⟩` from `GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain I`. Establish `: BorelSpace I.GA` using `inferInstance`. Establish `mN : ∀ x, x ∈ N ↔ x ∈ I.NA W` using `fun x => by rw [← hN]; rfl`.

Establish `mΓ : ∀ x, x ∈ Γ ↔ x ∈ I.GFset` using `fun x => by rw [← hΓ]; rfl`. Take `⟨ν, hν, hνC, hνN, hf⟩` from `exists_prob_subgroup N Γ (hN ▸ hcl) (hΓ ▸ hfin) C hC (fun m hm => by`. Take `⟨γ, ⟨h1, h1'⟩, h3⟩` from `hcov m ((mN m).1 hm)`. Conclude with `⟨γ⁻¹, Γ.inv_mem ((mΓ γ).2 h1), N.inv_mem ((mN γ).2 h1'), h3⟩)`. Use `⟨ν, hν, ⟨inferInstance, IsProbabilityMeasure.ne_zero ν, hN ▸ hνN, ?_⟩, C, hC, hCN, hνC⟩` and prove the remaining obligations.

Introduce `f hfi g hg`. Conclude with `hf f (fun γ h1 h1' y => hfi γ ⟨(mΓ γ).1 h1, (mN γ).1 h1'⟩ y) g ((mN g).2 hg)`.
-/
theorem exists_quot_prob (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) :
    ∃ ν : Measure I.GA, IsProbabilityMeasure ν ∧ I.IsNQuotMeas W ν ∧
      ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ν Cpᶜ = 0 := by
  obtain ⟨h2, hlc, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨⟨N, hN⟩, hcl, -, -, C, hC, hCN, hcov⟩ := GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I W hW
  obtain ⟨Γ, hΓ, hΓc, hfin, -⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain I
  have : BorelSpace I.GA := inferInstance
  have mN : ∀ x, x ∈ N ↔ x ∈ I.NA W := fun x => by rw [← hN]; rfl
  have mΓ : ∀ x, x ∈ Γ ↔ x ∈ I.GFset := fun x => by rw [← hΓ]; rfl
  obtain ⟨ν, hν, hνC, hνN, hf⟩ := exists_prob_subgroup N Γ (hN ▸ hcl) (hΓ ▸ hfin) C hC (fun m hm => by
    obtain ⟨γ, ⟨h1, h1'⟩, h3⟩ := hcov m ((mN m).1 hm)
    exact ⟨γ⁻¹, Γ.inv_mem ((mΓ γ).2 h1), N.inv_mem ((mN γ).2 h1'), h3⟩)
  refine ⟨ν, hν, ⟨inferInstance, IsProbabilityMeasure.ne_zero ν, hN ▸ hνN, ?_⟩, C, hC, hCN, hνC⟩
  intro f hfi g hg
  exact hf f (fun γ h1 h1' y => hfi γ ⟨(mΓ γ).1 h1, (mN γ).1 h1'⟩ y) g ((mN g).2 hg)

end GlobalTheory.UnipQuot
