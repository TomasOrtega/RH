import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralTsumEnormNeTop

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotStageInt

section Norm

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G]

/- English proof (translation)
Establish `hs : ∀ x : G, ∃ K, IsCompact K ∧ K ∈ 𝓝 x` using `fun x => exists_compact_mem_nhds x`. Use `choose K hK hKn using hs`. Take `⟨s, hsc, hsu⟩` from `TopologicalSpace.countable_cover_nhds (f := fun x => interior (K x)) (fun x => interior_mem_nhds.2 (hKn x))`. Establish `hne : s.Nonempty`. Establish `: (1 : G) ∈ ⋃ x ∈ s, interior (K x)` using `by rw [hsu]; trivial`.

Take `⟨x, hx, -⟩` from `mem_iUnion₂.1 this`. Conclude with `⟨x, hx⟩`. Take `⟨e, rfl⟩` from `hsc.exists_eq_range hne`. Use `⟨fun i => interior (K (e i)), fun i => K (e i), fun i => isOpen_interior, fun i => hK _, fun i => interior_subset, fun g => ?_⟩` and prove the remaining obligations. Establish `: g ∈ ⋃ x ∈ range e, interior (K x)` using `by rw [hsu]; trivial`.

Simplify using `using this`.
-/
theorem exists_open_cover :
    ∃ (U K : ℕ → Set G), (∀ i, IsOpen (U i)) ∧ (∀ i, IsCompact (K i)) ∧ (∀ i, U i ⊆ K i) ∧
      ∀ g, ∃ i, g ∈ U i := by
  have hs : ∀ x : G, ∃ K, IsCompact K ∧ K ∈ 𝓝 x := fun x => exists_compact_mem_nhds x
  choose K hK hKn using hs
  obtain ⟨s, hsc, hsu⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun x => interior (K x)) (fun x => interior_mem_nhds.2 (hKn x))
  have hne : s.Nonempty := by
    have : (1 : G) ∈ ⋃ x ∈ s, interior (K x) := by rw [hsu]; trivial
    obtain ⟨x, hx, -⟩ := mem_iUnion₂.1 this
    exact ⟨x, hx⟩
  obtain ⟨e, rfl⟩ := hsc.exists_eq_range hne
  refine ⟨fun i => interior (K (e i)), fun i => K (e i), fun i => isOpen_interior,
    fun i => hK _, fun i => interior_subset, fun g => ?_⟩
  have : g ∈ ⋃ x ∈ range e, interior (K x) := by rw [hsu]; trivial
  simpa using this

variable [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Use `haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : μT.IsMulRightInvariant := by`. Rewrite using `[← Measure.inv_eq_self μT]`. Use `infer_instance`. Use `haveI : SecondCountableTopology T := IsEmbedding.subtypeVal.secondCountableTopology`.

Use `haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `haveI : SigmaFinite μT := Measure.IsHaarMeasure.sigmaFinite μT`. Take `⟨U, K, hU, hK, hUK, hcov⟩` from `exists_open_cover (G := G)`. Establish `hUm : ∀ i, MeasurableSet (U i)` using `fun i => (hU i).measurableSet`. Establish `hmulT : Measurable fun p : G × T => (p.2 : G) * p.1` using `(measurable_subtype_coe.comp measurable_snd).mul measurable_fst`.

Set `f : ℕ → G → ℝ≥0∞` to `fun i => (U i).indicator 1`. Establish `hf : ∀ i, Measurable (f i)` using `fun i => measurable_one.indicator (hUm i)`. Set `m : ℕ → G → ℝ≥0∞` to `fun i g => ∫⁻ t : T, f i ((t : G) * g) ∂μT`. Establish `hmm : ∀ i, Measurable (m i)` using `fun i => ((hf i).comp hmulT).lintegral_prod_right'`. Establish `hinv : ∀ i (s : T) g, m i ((s : G) * g) = m i g`.

Introduce `i s g`. Use `lintegral_mul_right_eq_self (μ := μT) (fun t : T => f i ((t : G) * g)) s` as an intermediate fact. Simplify `this` using `[m, mul_assoc]`. Establish `hset : ∀ i g, m i g = μT ((fun t : T => (t : G) * g) ⁻¹' U i)`. Introduce `i g`.

Establish `hme : MeasurableSet ((fun t : T => (t : G) * g) ⁻¹' U i)` using `(measurable_subtype_coe.mul_const g) (hUm i)`. Rewrite using `[← lintegral_indicator_one hme]`. Both sides reduce to the same expression. Establish `hfin : ∀ i g, m i g ≠ ∞`. Introduce `i g`.

Establish `hemb : IsClosedEmbedding (fun t : T => (t : G) * g)` using `(Homeomorph.mulRight g).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal`. Establish `hc` using `hemb.isCompact_preimage (hK i)`. Rewrite using `[hset]`. Conclude with `ne_top_of_le_ne_top hc.measure_lt_top.ne (measure_mono (preimage_mono (hUK i)))`. Establish `hpos : ∀ i g, g ∈ U i → m i g ≠ 0`.

Introduce `i g hg`. Rewrite using `[hset]`. Establish `ho : IsOpen ((fun t : T => (t : G) * g) ⁻¹' U i)` using `(hU i).preimage (continuous_subtype_val.mul continuous_const)`. Conclude with `(ho.measure_pos μT ⟨1, by simpa using hg⟩).ne'`. Set `A : ℕ → Set G` to `fun i => {g | m i g ≠ 0}`.

Establish `hAm : ∀ i, MeasurableSet (A i)` using `fun i => (hmm i (measurableSet_singleton 0)).compl`. Set `B : ℕ → Set G` to `fun i => A i ∩ ⋂ j : Fin i, (A j)ᶜ`. Establish `hBm : ∀ i, MeasurableSet (B i)` using `fun i => (hAm i).inter (MeasurableSet.iInter fun j => (hAm j).compl)`. Establish `hBinv : ∀ i (s : T) g, (s : G) * g ∈ B i ↔ g ∈ B i`. Introduce `i s g`.

Simplify using `only [B, A, mem_inter_iff, mem_iInter, mem_compl_iff, mem_setOf_eq, hinv]`. Set `c : ℕ → G → ℝ≥0∞` to `fun i => (B i).indicator (fun g => (m i g)⁻¹)`. Establish `hc : ∀ i, Measurable (c i)` using `fun i => (hmm i).inv.indicator (hBm i)`. Establish `hcinv : ∀ i (s : T) g, c i ((s : G) * g) = c i g`. Introduce `i s g`.

Distinguish the cases in `h : g ∈ B i`. Simplify using `only [c, indicator_of_mem h, indicator_of_mem ((hBinv i s g).2 h), hinv]`. Simplify using `only [c, indicator_of_notMem h, indicator_of_notMem (fun h' => h ((hBinv i s g).1 h'))]`. Use `⟨fun g => ∑' i, c i g * f i g, Measurable.ennreal_tsum fun i => (hc i).mul (hf i), fun g => ?_⟩` and prove the remaining obligations. Establish `e1 : ∫⁻ t : T, ∑' i, c i ((t : G) * g) * f i ((t : G) * g) ∂μT = ∑' i, c i g * m i g`.

Establish `hmt : ∀ i, AEMeasurable (fun t : T => c i ((t : G) * g) * f i ((t : G) * g)) μT` using `fun i => (((hc i).mul (hf i)).comp (measurable_subtype_coe.mul_const g)).aemeasurable`. Rewrite using `[lintegral_tsum hmt]`. Use `tsum_congr fun i => ?_` and prove the remaining obligations. Simplify using `only [hcinv]`. Establish `hfm : Measurable fun t : T => f i ((t : G) * g)` using `(hf i).comp (measurable_subtype_coe.mul_const g)`.

Rewrite using `[lintegral_const_mul _ hfm]`. Rewrite using `[e1]`. Establish `hex : ∃ i, g ∈ A i`. Take `⟨i, hi⟩` from `hcov g`. Conclude with `⟨i, hpos i g hi⟩`.

Establish `hB0 : g ∈ B (Nat.find hex)`. Use `⟨Nat.find_spec hex, mem_iInter.2 fun j => ?_⟩` and prove the remaining obligations. Conclude with `Nat.find_min hex j.2`. Establish `hne : ∀ i, i ≠ Nat.find hex → g ∉ B i`. Introduce `i hi hB`.

Break down `lt_or_gt_of_ne hi with h | h` into its components or cases. Conclude with `Nat.find_min hex h hB.1`. Conclude with `(mem_iInter.1 hB.2 ⟨_, h⟩) (Nat.find_spec hex)`. Rewrite using `[tsum_eq_single (Nat.find hex) fun i hi => by simp [c, indicator_of_notMem (hne i hi)]]`. Simplify using `only [c, indicator_of_mem hB0]`.

Conclude with `ENNReal.inv_mul_cancel (Nat.find_spec hex) (hfin _ g)`.
-/
theorem exists_normaliser (T : Subgroup G) (hT : IsClosed (T : Set G)) (μT : Measure T)
    [μT.IsHaarMeasure] [μT.IsInvInvariant] : ∃ ρ, IsQuotNormaliser T μT ρ := by
  classical
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : μT.IsMulRightInvariant := by
    rw [← Measure.inv_eq_self μT]; infer_instance
  haveI : SecondCountableTopology T := IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μT := Measure.IsHaarMeasure.sigmaFinite μT
  obtain ⟨U, K, hU, hK, hUK, hcov⟩ := exists_open_cover (G := G)
  have hUm : ∀ i, MeasurableSet (U i) := fun i => (hU i).measurableSet
  have hmulT : Measurable fun p : G × T => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  let f : ℕ → G → ℝ≥0∞ := fun i => (U i).indicator 1
  have hf : ∀ i, Measurable (f i) := fun i => measurable_one.indicator (hUm i)
  let m : ℕ → G → ℝ≥0∞ := fun i g => ∫⁻ t : T, f i ((t : G) * g) ∂μT
  have hmm : ∀ i, Measurable (m i) := fun i => ((hf i).comp hmulT).lintegral_prod_right'
  have hinv : ∀ i (s : T) g, m i ((s : G) * g) = m i g := by
    intro i s g
    have := lintegral_mul_right_eq_self (μ := μT) (fun t : T => f i ((t : G) * g)) s
    simpa [m, mul_assoc] using this
  have hset : ∀ i g, m i g = μT ((fun t : T => (t : G) * g) ⁻¹' U i) := by
    intro i g
    have hme : MeasurableSet ((fun t : T => (t : G) * g) ⁻¹' U i) :=
      (measurable_subtype_coe.mul_const g) (hUm i)
    rw [← lintegral_indicator_one hme]
    rfl
  have hfin : ∀ i g, m i g ≠ ∞ := by
    intro i g
    have hemb : IsClosedEmbedding (fun t : T => (t : G) * g) :=
      (Homeomorph.mulRight g).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal
    have hc := hemb.isCompact_preimage (hK i)
    rw [hset]
    exact ne_top_of_le_ne_top hc.measure_lt_top.ne (measure_mono (preimage_mono (hUK i)))
  have hpos : ∀ i g, g ∈ U i → m i g ≠ 0 := by
    intro i g hg
    rw [hset]
    have ho : IsOpen ((fun t : T => (t : G) * g) ⁻¹' U i) :=
      (hU i).preimage (continuous_subtype_val.mul continuous_const)
    exact (ho.measure_pos μT ⟨1, by simpa using hg⟩).ne'
  let A : ℕ → Set G := fun i => {g | m i g ≠ 0}
  have hAm : ∀ i, MeasurableSet (A i) := fun i => (hmm i (measurableSet_singleton 0)).compl
  let B : ℕ → Set G := fun i => A i ∩ ⋂ j : Fin i, (A j)ᶜ
  have hBm : ∀ i, MeasurableSet (B i) := fun i =>
    (hAm i).inter (MeasurableSet.iInter fun j => (hAm j).compl)
  have hBinv : ∀ i (s : T) g, (s : G) * g ∈ B i ↔ g ∈ B i := by
    intro i s g
    simp only [B, A, mem_inter_iff, mem_iInter, mem_compl_iff, mem_setOf_eq, hinv]
  let c : ℕ → G → ℝ≥0∞ := fun i => (B i).indicator (fun g => (m i g)⁻¹)
  have hc : ∀ i, Measurable (c i) := fun i => (hmm i).inv.indicator (hBm i)
  have hcinv : ∀ i (s : T) g, c i ((s : G) * g) = c i g := by
    intro i s g
    by_cases h : g ∈ B i
    · simp only [c, indicator_of_mem h, indicator_of_mem ((hBinv i s g).2 h), hinv]
    · simp only [c, indicator_of_notMem h, indicator_of_notMem (fun h' => h ((hBinv i s g).1 h'))]
  refine ⟨fun g => ∑' i, c i g * f i g, Measurable.ennreal_tsum fun i => (hc i).mul (hf i),
    fun g => ?_⟩
  have e1 : ∫⁻ t : T, ∑' i, c i ((t : G) * g) * f i ((t : G) * g) ∂μT = ∑' i, c i g * m i g := by
    have hmt : ∀ i, AEMeasurable (fun t : T => c i ((t : G) * g) * f i ((t : G) * g)) μT := fun i =>
      (((hc i).mul (hf i)).comp (measurable_subtype_coe.mul_const g)).aemeasurable
    rw [lintegral_tsum hmt]
    refine tsum_congr fun i => ?_
    simp only [hcinv]
    have hfm : Measurable fun t : T => f i ((t : G) * g) :=
      (hf i).comp (measurable_subtype_coe.mul_const g)
    rw [lintegral_const_mul _ hfm]
  rw [e1]
  have hex : ∃ i, g ∈ A i := by
    obtain ⟨i, hi⟩ := hcov g
    exact ⟨i, hpos i g hi⟩
  have hB0 : g ∈ B (Nat.find hex) := by
    refine ⟨Nat.find_spec hex, mem_iInter.2 fun j => ?_⟩
    exact Nat.find_min hex j.2
  have hne : ∀ i, i ≠ Nat.find hex → g ∉ B i := by
    intro i hi hB
    rcases lt_or_gt_of_ne hi with h | h
    · exact Nat.find_min hex h hB.1
    · exact (mem_iInter.1 hB.2 ⟨_, h⟩) (Nat.find_spec hex)
  rw [tsum_eq_single (Nat.find hex) fun i hi => by simp [c, indicator_of_notMem (hne i hi)]]
  simp only [c, indicator_of_mem hB0]
  exact ENNReal.inv_mul_cancel (Nat.find_spec hex) (hfin _ g)

end Norm

section Count

/- English proof (translation)
Establish `hmi : Measurable (fun h : K => h⁻¹)` using `measurable_of_countable _`. Use `⟨?_⟩` and prove the remaining obligations. Use extensionality with `s hs`. Express the relevant statement in the definitionally equal form `Measure.map (fun h : K => h⁻¹) Measure.count s = _`. Rewrite using `[Measure.map_apply hmi hs]`.

Establish `: (Inv.inv ⁻¹' s : Set K) = (fun h : K => h⁻¹) '' s`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this, Measure.count_injective_image' inv_injective hs ((Set.to_countable _).measurableSet)]`.
-/
theorem count_inv {K : Type*} [Group K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Countable K] : (Measure.count : Measure K).IsInvInvariant := by
  have hmi : Measurable (fun h : K => h⁻¹) := measurable_of_countable _
  refine ⟨?_⟩
  ext s hs
  change Measure.map (fun h : K => h⁻¹) Measure.count s = _
  rw [Measure.map_apply hmi hs]
  have : (Inv.inv ⁻¹' s : Set K) = (fun h : K => h⁻¹) '' s := by
    ext x; simp
  rw [this, Measure.count_injective_image' inv_injective hs ((Set.to_countable _).measurableSet)]

/- English proof (translation)
Use `haveI : (Measure.count : Measure Γ).IsInvInvariant := count_inv`. Establish `hρ : IsQuotNormaliser Γ Measure.count (D.indicator (1 : K → ℝ≥0∞))`. Use `⟨measurable_one.indicator hDm, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[lintegral_count]`. Take `⟨h₀, h₁, hu⟩` from `hD g`.

Rewrite using `[tsum_eq_single h₀ (fun h hh => indicator_of_notMem (fun hm => hh (hu h hm)) _), indicator_of_mem h₁]`. Both sides reduce to the same expression. Rewrite using `[GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hf hfΓ hρ, ← integral_indicator hDm]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Apply the tactic sequence `by_cases hg : g ∈ D <;> simp [hg]`.
-/
theorem quotIntegral_strict {K : Type*} [Group K] [MeasurableSpace K] [MeasurableMul₂ K]
    [MeasurableInv K] {ν : Measure K} [ν.IsMulLeftInvariant] [SFinite ν] {Γ : Subgroup K}
    [Countable Γ] [MeasurableSingletonClass Γ] {D : Set K} (hDm : MeasurableSet D)
    (hD : ∀ t : K, ∃! h : Γ, (h : K) * t ∈ D) {f : K → ℂ} (hf : Measurable f)
    (hfΓ : ∀ h ∈ Γ, ∀ t, f (h * t) = f t) :
    quotIntegral ν Γ Measure.count f = ∫ t in D, f t ∂ν := by
  haveI : (Measure.count : Measure Γ).IsInvInvariant := count_inv
  have hρ : IsQuotNormaliser Γ Measure.count (D.indicator (1 : K → ℝ≥0∞)) := by
    refine ⟨measurable_one.indicator hDm, fun g => ?_⟩
    rw [lintegral_count]
    obtain ⟨h₀, h₁, hu⟩ := hD g
    rw [tsum_eq_single h₀ (fun h hh => indicator_of_notMem (fun hm => hh (hu h hm)) _),
      indicator_of_mem h₁]
    rfl
  rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hf hfΓ hρ, ← integral_indicator hDm]
  congr 1
  funext g
  by_cases hg : g ∈ D <;> simp [hg]

end Count

section PiLocalization₂

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Apply `discreteTopology_of_isOpen_singleton_one` to reduce the goal to its premises. Take `⟨V', hV'o, hV'⟩` from `isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ₀))`. Take `⟨V, hVo, rfl⟩` from `isOpen_induced_iff.1 hV'o`. Use `isOpen_induced_iff.2 ⟨V, hVo, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨h, hh⟩`.

Take `⟨γ, hγ, rfl⟩` from `Subgroup.mem_map.1 hh`. Use `Set.ext_iff.1 hV' ⟨γ, hγ⟩` as an intermediate fact. Simplify using `only [mem_preimage, mem_singleton_iff] at this ⊢`. Use `this.trans ⟨fun h => Subtype.ext (congrArg (fun z : Γ₀ => ((z : T) : G)) h), fun h => ?_⟩` and prove the remaining obligations. Establish `h' : ((⟨T.subtype γ, hh⟩ : Γ₀.map T.subtype) : G) = 1` using `congrArg Subtype.val h`.

Conclude with `Subtype.ext (Subtype.ext h')`.
-/
theorem map_discrete (T : Subgroup G) (Γ₀ : Subgroup T) [DiscreteTopology Γ₀] :
    DiscreteTopology (Γ₀.map T.subtype) := by
  apply discreteTopology_of_isOpen_singleton_one
  obtain ⟨V', hV'o, hV'⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ₀))
  obtain ⟨V, hVo, rfl⟩ := isOpen_induced_iff.1 hV'o
  refine isOpen_induced_iff.2 ⟨V, hVo, ?_⟩
  ext ⟨h, hh⟩
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hh
  have := Set.ext_iff.1 hV' ⟨γ, hγ⟩
  simp only [mem_preimage, mem_singleton_iff] at this ⊢
  refine this.trans ⟨fun h => Subtype.ext (congrArg (fun z : Γ₀ => ((z : T) : G)) h), fun h => ?_⟩
  have h' : ((⟨T.subtype γ, hh⟩ : Γ₀.map T.subtype) : G) = 1 := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {T : Subgroup G} {μT : Measure T} [μT.IsMulLeftInvariant] [SFinite μT] [μT.IsInvInvariant]

/- English proof (translation)
Use `haveI : SecondCountableTopology T := IsEmbedding.subtypeVal.secondCountableTopology`. Establish `hj : Measurable fun p : G × T => ((p.2⁻¹ : T) : G) * p.1` using `(measurable_subtype_coe.comp measurable_snd.inv).mul measurable_fst`. Use `⟨(hσ.1.comp hj).lintegral_prod_right', fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[lintegral_count]`. Set `e : Γ₀ ≃ Γ₀.map T.subtype` to `(Γ₀.equivMapOfInjective T.subtype T.subtype_injective).toEquiv`.

Establish `he : ∀ γ : Γ₀, ((e γ : Γ₀.map T.subtype) : G) = ((γ : T) : G)` using `fun _ => rfl`. Rewrite using `[← e.tsum_eq]`. Establish `e1 : ∀ γ : Γ₀, ∫⁻ t in D, σ (((t⁻¹ : T) : G) * (((e γ : Γ₀.map T.subtype) : G) * x)) ∂μT = ∫⁻ s : T, D.indicator (1 : T → ℝ≥0∞) ((γ : T) * s) * σ (((s⁻¹ : T) : G) * x) ∂μT`. Introduce `γ`. Rewrite using `[← lintegral_indicator hDm, ← lintegral_mul_left_eq_self _ (γ : T)]`.

Use `lintegral_congr fun s => ?_` and prove the remaining obligations. Rewrite using `[he]`. Distinguish the cases in `hs : (γ : T) * s ∈ D`. Simplify using `[hs, mul_assoc]`. Simplify using `[hs]`.

Repeatedly rewrite using `[e1]`. Establish `hm : ∀ γ : Γ₀, AEMeasurable (fun s : T => D.indicator (1 : T → ℝ≥0∞) ((γ : T) * s) * σ (((s⁻¹ : T) : G) * x)) μT` using `fun γ => (((measurable_one.indicator hDm).comp (measurable_const_mul _)).mul (hσ.1.comp ((measurable_subtype_coe.comp measurable_inv).mul_const x))).aemeasurable`. Rewrite using `[← lintegral_tsum hm]`. Establish `e2 : ∀ s : T, ∑' γ : Γ₀, D.indicator (1 : T → ℝ≥0∞) ((γ : T) * s) * σ (((s⁻¹ : T) : G) * x) = σ (((s⁻¹ : T) : G) * x)`. Introduce `s`.

Take `⟨h₀, h₁, hu⟩` from `hD s`. Rewrite using `[tsum_eq_single h₀ fun h hh => by`. Simplify using `[indicator_of_notMem (fun hm => hh (hu h hm))]]`. Simplify using `[h₁]`. Repeatedly rewrite using `[e2]`.

Rewrite using `[lintegral_inv_eq_self (fun s : T => σ ((s : G) * x))]`. Conclude with `hσ.2 x`.
-/
theorem stage_normaliser (Γ₀ : Subgroup T) [Countable Γ₀]
    [MeasurableSingletonClass (Γ₀.map T.subtype)] {D : Set T} (hDm : MeasurableSet D)
    (hD : ∀ t : T, ∃! h : Γ₀, (h : T) * t ∈ D) {σ : G → ℝ≥0∞} (hσ : IsQuotNormaliser T μT σ) :
    IsQuotNormaliser (Γ₀.map T.subtype) Measure.count
      (fun x => ∫⁻ t in D, σ (((t⁻¹ : T) : G) * x) ∂μT) := by
  haveI : SecondCountableTopology T := IsEmbedding.subtypeVal.secondCountableTopology
  have hj : Measurable fun p : G × T => ((p.2⁻¹ : T) : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd.inv).mul measurable_fst
  refine ⟨(hσ.1.comp hj).lintegral_prod_right', fun x => ?_⟩
  rw [lintegral_count]
  let e : Γ₀ ≃ Γ₀.map T.subtype := (Γ₀.equivMapOfInjective T.subtype T.subtype_injective).toEquiv
  have he : ∀ γ : Γ₀, ((e γ : Γ₀.map T.subtype) : G) = ((γ : T) : G) := fun _ => rfl
  rw [← e.tsum_eq]
  have e1 : ∀ γ : Γ₀, ∫⁻ t in D, σ (((t⁻¹ : T) : G) * (((e γ : Γ₀.map T.subtype) : G) * x)) ∂μT =
      ∫⁻ s : T, D.indicator (1 : T → ℝ≥0∞) ((γ : T) * s) * σ (((s⁻¹ : T) : G) * x) ∂μT := by
    intro γ
    rw [← lintegral_indicator hDm, ← lintegral_mul_left_eq_self _ (γ : T)]
    refine lintegral_congr fun s => ?_
    rw [he]
    by_cases hs : (γ : T) * s ∈ D
    · simp [hs, mul_assoc]
    · simp [hs]
  simp_rw [e1]
  have hm : ∀ γ : Γ₀, AEMeasurable (fun s : T => D.indicator (1 : T → ℝ≥0∞) ((γ : T) * s) *
      σ (((s⁻¹ : T) : G) * x)) μT := fun γ =>
    (((measurable_one.indicator hDm).comp (measurable_const_mul _)).mul
      (hσ.1.comp ((measurable_subtype_coe.comp measurable_inv).mul_const x))).aemeasurable
  rw [← lintegral_tsum hm]
  have e2 : ∀ s : T, ∑' γ : Γ₀, D.indicator (1 : T → ℝ≥0∞) ((γ : T) * s) * σ (((s⁻¹ : T) : G) * x) =
      σ (((s⁻¹ : T) : G) * x) := by
    intro s
    obtain ⟨h₀, h₁, hu⟩ := hD s
    rw [tsum_eq_single h₀ fun h hh => by
      simp [indicator_of_notMem (fun hm => hh (hu h hm))]]
    simp [h₁]
  simp_rw [e2]
  rw [lintegral_inv_eq_self (fun s : T => σ ((s : G) * x))]
  exact hσ.2 x

end PiLocalization₂

section Fubini

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Rewrite using `[← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]`. Conclude with `ENNReal.ofReal_toReal_le`.
-/
theorem enorm_ofReal_toReal_le (r : ℝ≥0∞) : ‖((r.toReal : ℝ) : ℂ)‖ₑ ≤ r := by
  rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

/- English proof (translation)
Use `haveI : SecondCountableTopology T := IsEmbedding.subtypeVal.secondCountableTopology`. Set `A : T × G → ℂ` to `fun p => F p.2 * (((σ (((p.1⁻¹ : T) : G) * p.2)).toReal : ℝ) : ℂ)`. Set `ψ : T × G → T × G` to `fun p => (p.1, (p.1 : G) * p.2)`. Establish `hj : Measurable fun p : T × G => ((p.1⁻¹ : T) : G) * p.2` using `(measurable_subtype_coe.comp measurable_fst.inv).mul measurable_snd`. Establish `hAm : Measurable A` using `(hF.comp measurable_snd).mul (Complex.measurable_ofReal.comp (hσ.comp hj).ennreal_toReal)`.

Establish `hψ : MeasurePreserving ψ (ν.prod μ) (ν.prod μ)` using `(MeasurePreserving.id ν).skew_product (g := fun (t : T) (x : G) => (t : G) * x) ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd) (ae_of_all _ fun t => map_mul_left_eq_self μ (t : G))`. Establish `hAi : Integrable A (ν.prod μ)`. Use `⟨hAm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hAm.enorm.aemeasurable]`. Use `lt_of_le_of_lt (lintegral_mono fun x => ?_) (lt_top_iff_ne_top.2 hfin)` and prove the remaining obligations.

Establish `hm : Measurable fun t : T => σ (((t⁻¹ : T) : G) * x)` using `hσ.comp ((measurable_subtype_coe.comp measurable_inv).mul_const x)`. Rewrite using `[← lintegral_const_mul _ hm]`. Use `lintegral_mono fun t => ?_` and prove the remaining obligations. Simplify using `only [A, enorm_mul]`. Conclude with `mul_le_mul_right (enorm_ofReal_toReal_le _) _`.

Establish `hBi : Integrable (A ∘ ψ) (ν.prod μ)` using `(hψ.integrable_comp hAm.aestronglyMeasurable).2 hAi`. Establish `e1 : ∫ x, F x * (((∫⁻ t, σ (((t⁻¹ : T) : G) * x) ∂ν).toReal : ℝ) : ℂ) ∂μ = ∫ p, A p ∂(ν.prod μ)`. Rewrite using `[integral_prod_symm _ hAi]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with x hx`.

Establish `hm : Measurable fun t : T => σ (((t⁻¹ : T) : G) * x)` using `hσ.comp ((measurable_subtype_coe.comp measurable_inv).mul_const x)`. Simplify using `only [A]`. Rewrite using `[integral_const_mul, integral_complex_ofReal, integral_toReal hm.aemeasurable (ae_lt_top hm hx.ne)]`. Establish `e2 : ∫ p, A p ∂(ν.prod μ) = ∫ p, A (ψ p) ∂(ν.prod μ)` using `by conv_lhs => rw [← hψ.map_eq]`. Conclude with `integral_map hψ.measurable.aemeasurable hAm.aestronglyMeasurable`.

Establish `e3 : ∫ p, A (ψ p) ∂(ν.prod μ) = ∫ x, (∫ t, F ((t : G) * x) ∂ν) * (((σ x).toReal : ℝ) : ℂ) ∂μ`. Rewrite using `[show ∫ p, A (ψ p) ∂(ν.prod μ) = ∫ p, (A ∘ ψ) p ∂(ν.prod μ) from rfl, integral_prod_symm _ hBi]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [A, ψ, Function.comp, Subgroup.coe_inv, inv_mul_cancel_left]`. Rewrite using `[integral_mul_const]`.

Rewrite using `[e1, e2, e3]`.
-/
theorem integral_stage {T : Subgroup G} (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (ν : Measure T) [SFinite ν] {F : G → ℂ} (hF : Measurable F) {σ : G → ℝ≥0∞} (hσ : Measurable σ)
    (hae : ∀ᵐ x ∂μ, ∫⁻ t, σ (((t⁻¹ : T) : G) * x) ∂ν < ∞)
    (hfin : ∫⁻ x, ‖F x‖ₑ * ∫⁻ t, σ (((t⁻¹ : T) : G) * x) ∂ν ∂μ ≠ ∞) :
    ∫ x, F x * (((∫⁻ t, σ (((t⁻¹ : T) : G) * x) ∂ν).toReal : ℝ) : ℂ) ∂μ =
      ∫ x, (∫ t, F ((t : G) * x) ∂ν) * (((σ x).toReal : ℝ) : ℂ) ∂μ := by
  haveI : SecondCountableTopology T := IsEmbedding.subtypeVal.secondCountableTopology
  let A : T × G → ℂ := fun p => F p.2 * (((σ (((p.1⁻¹ : T) : G) * p.2)).toReal : ℝ) : ℂ)
  let ψ : T × G → T × G := fun p => (p.1, (p.1 : G) * p.2)
  have hj : Measurable fun p : T × G => ((p.1⁻¹ : T) : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst.inv).mul measurable_snd
  have hAm : Measurable A := (hF.comp measurable_snd).mul
    (Complex.measurable_ofReal.comp (hσ.comp hj).ennreal_toReal)
  have hψ : MeasurePreserving ψ (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun (t : T) (x : G) => (t : G) * x)
      ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
      (ae_of_all _ fun t => map_mul_left_eq_self μ (t : G))
  have hAi : Integrable A (ν.prod μ) := by
    refine ⟨hAm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hAm.enorm.aemeasurable]
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (lt_top_iff_ne_top.2 hfin)
    have hm : Measurable fun t : T => σ (((t⁻¹ : T) : G) * x) :=
      hσ.comp ((measurable_subtype_coe.comp measurable_inv).mul_const x)
    rw [← lintegral_const_mul _ hm]
    refine lintegral_mono fun t => ?_
    simp only [A, enorm_mul]
    exact mul_le_mul_right (enorm_ofReal_toReal_le _) _
  have hBi : Integrable (A ∘ ψ) (ν.prod μ) :=
    (hψ.integrable_comp hAm.aestronglyMeasurable).2 hAi
  have e1 : ∫ x, F x * (((∫⁻ t, σ (((t⁻¹ : T) : G) * x) ∂ν).toReal : ℝ) : ℂ) ∂μ =
      ∫ p, A p ∂(ν.prod μ) := by
    rw [integral_prod_symm _ hAi]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    have hm : Measurable fun t : T => σ (((t⁻¹ : T) : G) * x) :=
      hσ.comp ((measurable_subtype_coe.comp measurable_inv).mul_const x)
    simp only [A]
    rw [integral_const_mul, integral_complex_ofReal,
      integral_toReal hm.aemeasurable (ae_lt_top hm hx.ne)]
  have e2 : ∫ p, A p ∂(ν.prod μ) = ∫ p, A (ψ p) ∂(ν.prod μ) := by
    conv_lhs => rw [← hψ.map_eq]
    exact integral_map hψ.measurable.aemeasurable hAm.aestronglyMeasurable
  have e3 : ∫ p, A (ψ p) ∂(ν.prod μ) =
      ∫ x, (∫ t, F ((t : G) * x) ∂ν) * (((σ x).toReal : ℝ) : ℂ) ∂μ := by
    rw [show ∫ p, A (ψ p) ∂(ν.prod μ) = ∫ p, (A ∘ ψ) p ∂(ν.prod μ) from rfl,
      integral_prod_symm _ hBi]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [A, ψ, Function.comp, Subgroup.coe_inv, inv_mul_cancel_left]
    rw [integral_mul_const]
  rw [e1, e2, e3]

end Fubini

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ μ _ T μT _ _ Γ₀ F hT hdisc hF hFΓ hfin`. Use `haveI := hdisc`. Use `haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology T := IsEmbedding.subtypeVal.secondCountableTopology`. Use `haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable`.

Use `haveI : SigmaFinite μT := Measure.IsHaarMeasure.sigmaFinite μT`. Use `haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ`. Use `haveI : μT.IsMulRightInvariant := by`. Rewrite using `[← Measure.inv_eq_self μT]`.

Use `infer_instance`. Use `haveI : SecondCountableTopology Γ₀ := IsEmbedding.subtypeVal.secondCountableTopology`. Use `haveI : Countable Γ₀ := countable_of_Lindelof_of_discrete`. Use `haveI : DiscreteTopology (Γ₀.map T.subtype) := map_discrete T Γ₀`. Use `haveI : Countable (Γ₀.map T.subtype) := (Γ₀.equivMapOfInjective T.subtype T.subtype_injective).toEquiv.surjective.countable`.

Use `haveI : (Measure.count : Measure (Γ₀.map T.subtype)).IsInvInvariant := count_inv`. Take `⟨σ, hσ⟩` from `exists_normaliser T hT μT`. Take `⟨D, hDm, hD⟩` from `GlobalTheory.CompanionTheory.QuotUnfold.exists_strict_domain Γ₀`. Establish `hρ` using `stage_normaliser Γ₀ hDm hD hσ`. Establish `hFH : ∀ h ∈ Γ₀.map T.subtype, ∀ x, F (h * x) = F x`.

Introduce `h hh x`. Take `⟨γ, hγ, rfl⟩` from `Subgroup.mem_map.1 hh`. Conclude with `hFΓ γ hγ x`. Establish `hmt : ∀ x, Measurable fun t : T => F ((t : G) * x)` using `fun x => hF.comp (measurable_subtype_coe.mul_const x)`. Establish `hΓt : ∀ x, ∀ h ∈ Γ₀, ∀ t : T, F (((h * t : T) : G) * x) = F ((t : G) * x)`.

Introduce `x h hh t`. Use `hFΓ h hh ((t : G) * x)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `hin : ∀ x, quotIntegral μT Γ₀ Measure.count (fun t : T => F ((t : G) * x)) = ∫ t in D, F ((t : G) * x) ∂μT` using `fun x => quotIntegral_strict hDm hD (hmt x) (hΓt x)`. Establish `hΦm : Measurable fun x => ∫ t in D, F ((t : G) * x) ∂μT`.

Establish `hj : Measurable fun p : G × T => F ((p.2 : G) * p.1)` using `hF.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)`. Conclude with `(hj.stronglyMeasurable.integral_prod_right' (ν := μT.restrict D)).measurable`. Establish `hΦT : ∀ s ∈ T, ∀ x, ∫ t in D, F ((t : G) * (s * x)) ∂μT = ∫ t in D, F ((t : G) * x) ∂μT`. Introduce `s hs x`. Set `s' : T` to `⟨s, hs⟩`.

Set `D' : Set T` to `(fun t => t * s'⁻¹) ⁻¹' D`. Establish `hD'm : MeasurableSet D'` using `(measurable_mul_const _) hDm`. Establish `hD' : ∀ t : T, ∃! h : Γ₀, (h : T) * t ∈ D'`. Introduce `t`. Take `⟨h, h₁, hu⟩` from `hD (t * s'⁻¹)`.

Conclude with `⟨h, by simpa [D', mul_assoc] using h₁, fun k hk => hu k (by simpa [D', mul_assoc] using hk)⟩`. Establish `e : ∫ t in D, F ((t : G) * (s * x)) ∂μT = ∫ t in D', F ((t : G) * x) ∂μT`. Rewrite using `[← integral_indicator hDm, ← integral_indicator hD'm]`. Use `(integral_mul_right_eq_self _ s'⁻¹).symm.trans ?_` and prove the remaining obligations. Use `integral_congr_ae (ae_of_all _ fun t => ?_)` and prove the remaining obligations.

Use `beta_reduce`. Distinguish the cases in `ht : t * s'⁻¹ ∈ D`. Rewrite using `[indicator_of_mem ht, indicator_of_mem (show t ∈ D' from ht)]`. Simplify using `[s', mul_assoc]`. Rewrite using `[indicator_of_notMem ht, indicator_of_notMem (show t ∉ D' from ht)]`.

Rewrite using `[e, ← quotIntegral_strict hD'm hD' (hmt x) (hΓt x), hin]`. Establish `hΨ : (fun x => quotIntegral μT Γ₀ Measure.count fun t : T => F ((t : G) * x)) = fun x => ∫ t in D, F ((t : G) * x) ∂μT` using `funext hin`. Rewrite using `[hΨ, GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hFH hρ, GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hΦm hΦT hσ]`. Establish `hfin' : ∫⁻ x, ‖F x‖ₑ * ∫⁻ t in D, σ (((t⁻¹ : T) : G) * x) ∂μT ∂μ ≠ ∞`. Establish `hex : ∃ ρ, IsQuotNormaliser (Γ₀.map T.subtype) Measure.count ρ` using `⟨_, hρ⟩`.

Rewrite `hfin` using `[quotLIntegral, dif_pos hex]`. Rewrite using `[lintegral_normaliser_eq hF.enorm (fun h hh g => by simp only [hFH h hh g]) hρ hex.choose_spec]` and apply the resulting hypothesis. Conclude with `integral_stage μ (μT.restrict D) hF hσ.1 (GlobalTheory.CompanionTheory.QuotNorm.ae_lt_top_of_normaliser hρ) hfin'`.
-/
theorem quotStage_holds : PositivityTheory.Rg.BcB.D4.QuotStage := by
  intro G _ _ _ _ _ _ _ μ _ T μT _ _ Γ₀ F hT hdisc hF hFΓ hfin
  classical
  haveI := hdisc
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T := IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μT := Measure.IsHaarMeasure.sigmaFinite μT
  haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  haveI : μT.IsMulRightInvariant := by
    rw [← Measure.inv_eq_self μT]; infer_instance
  haveI : SecondCountableTopology Γ₀ := IsEmbedding.subtypeVal.secondCountableTopology
  haveI : Countable Γ₀ := countable_of_Lindelof_of_discrete
  haveI : DiscreteTopology (Γ₀.map T.subtype) := map_discrete T Γ₀
  haveI : Countable (Γ₀.map T.subtype) :=
    (Γ₀.equivMapOfInjective T.subtype T.subtype_injective).toEquiv.surjective.countable
  haveI : (Measure.count : Measure (Γ₀.map T.subtype)).IsInvInvariant := count_inv
  obtain ⟨σ, hσ⟩ := exists_normaliser T hT μT
  obtain ⟨D, hDm, hD⟩ := GlobalTheory.CompanionTheory.QuotUnfold.exists_strict_domain Γ₀
  have hρ := stage_normaliser Γ₀ hDm hD hσ
  have hFH : ∀ h ∈ Γ₀.map T.subtype, ∀ x, F (h * x) = F x := by
    intro h hh x
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hh
    exact hFΓ γ hγ x
  have hmt : ∀ x, Measurable fun t : T => F ((t : G) * x) := fun x =>
    hF.comp (measurable_subtype_coe.mul_const x)
  have hΓt : ∀ x, ∀ h ∈ Γ₀, ∀ t : T, F (((h * t : T) : G) * x) = F ((t : G) * x) := by
    intro x h hh t
    have := hFΓ h hh ((t : G) * x)
    simpa [mul_assoc] using this
  have hin : ∀ x, quotIntegral μT Γ₀ Measure.count (fun t : T => F ((t : G) * x)) =
      ∫ t in D, F ((t : G) * x) ∂μT := fun x =>
    quotIntegral_strict hDm hD (hmt x) (hΓt x)
  have hΦm : Measurable fun x => ∫ t in D, F ((t : G) * x) ∂μT := by
    have hj : Measurable fun p : G × T => F ((p.2 : G) * p.1) :=
      hF.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := μT.restrict D)).measurable
  have hΦT : ∀ s ∈ T, ∀ x, ∫ t in D, F ((t : G) * (s * x)) ∂μT = ∫ t in D, F ((t : G) * x) ∂μT := by
    intro s hs x
    let s' : T := ⟨s, hs⟩
    let D' : Set T := (fun t => t * s'⁻¹) ⁻¹' D
    have hD'm : MeasurableSet D' := (measurable_mul_const _) hDm
    have hD' : ∀ t : T, ∃! h : Γ₀, (h : T) * t ∈ D' := by
      intro t
      obtain ⟨h, h₁, hu⟩ := hD (t * s'⁻¹)
      exact ⟨h, by simpa [D', mul_assoc] using h₁, fun k hk => hu k (by simpa [D', mul_assoc] using hk)⟩
    have e : ∫ t in D, F ((t : G) * (s * x)) ∂μT = ∫ t in D', F ((t : G) * x) ∂μT := by
      rw [← integral_indicator hDm, ← integral_indicator hD'm]
      refine (integral_mul_right_eq_self _ s'⁻¹).symm.trans ?_
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      beta_reduce
      by_cases ht : t * s'⁻¹ ∈ D
      · rw [indicator_of_mem ht, indicator_of_mem (show t ∈ D' from ht)]
        simp [s', mul_assoc]
      · rw [indicator_of_notMem ht, indicator_of_notMem (show t ∉ D' from ht)]
    rw [e, ← quotIntegral_strict hD'm hD' (hmt x) (hΓt x), hin]
  have hΨ : (fun x => quotIntegral μT Γ₀ Measure.count fun t : T => F ((t : G) * x)) =
      fun x => ∫ t in D, F ((t : G) * x) ∂μT := funext hin
  rw [hΨ, GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hFH hρ,
    GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hΦm hΦT hσ]
  have hfin' : ∫⁻ x, ‖F x‖ₑ * ∫⁻ t in D, σ (((t⁻¹ : T) : G) * x) ∂μT ∂μ ≠ ∞ := by
    have hex : ∃ ρ, IsQuotNormaliser (Γ₀.map T.subtype) Measure.count ρ := ⟨_, hρ⟩
    rw [quotLIntegral, dif_pos hex] at hfin
    rwa [lintegral_normaliser_eq hF.enorm (fun h hh g => by simp only [hFH h hh g]) hρ hex.choose_spec]
  exact integral_stage μ (μT.restrict D) hF hσ.1
    (GlobalTheory.CompanionTheory.QuotNorm.ae_lt_top_of_normaliser hρ) hfin'

/- English proof (translation)
The claim follows from `quotStage_holds`.
-/
theorem quotStage_of (_ : PositivityTheory.Rg.BcB.D4.NormEq) : PositivityTheory.Rg.BcB.D4.QuotStage := quotStage_holds

end GlobalTheory.CompanionTheory.QuotStageInt
