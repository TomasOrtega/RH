import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramified
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity

/- English proof (translation)
Establish `hsub : (A \ B) ∩ W ⊆ Zᶜ ∪ ⋃ i : {x // x ∉ T}, P i ∩ W`. Introduce and unpack `x ⟨⟨hxA, hxB⟩, hxW⟩`. Distinguish the cases in `hxZ : x ∈ Z`. Take `⟨i, hi⟩` from `Set.mem_iUnion.1 (hcov ⟨hxA, hxZ⟩)`. Distinguish the cases in `hiT : i ∈ T`.

Conclude with `absurd (hB ⟨hxA, Set.mem_iUnion₂.2 ⟨i, hiT, hi⟩⟩) hxB`. Conclude with `Or.inr (Set.mem_iUnion.2 ⟨⟨i, hiT⟩, hi, hxW⟩)`. Conclude with `Or.inl hxZ`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tail_le {V ι : Type} [Countable ι] [MeasurableSpace V] (ρ : Measure V) {Z A B W : Set V}
    {P : ι → Set V} {c : ι → ℝ≥0} {T : Finset ι} {e : ℝ≥0∞}
    (hZ : ρ Zᶜ = 0) (hcov : A ∩ Z ⊆ ⋃ i, P i) (hB : A ∩ (⋃ i ∈ T, P i) ⊆ B)
    (hP : ∀ i, ρ (P i ∩ W) ≤ (c i : ℝ≥0∞) * e) :
    ρ ((A \ B) ∩ W) ≤ (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) * e := by
  have hsub : (A \ B) ∩ W ⊆ Zᶜ ∪ ⋃ i : {x // x ∉ T}, P i ∩ W := by
    rintro x ⟨⟨hxA, hxB⟩, hxW⟩
    by_cases hxZ : x ∈ Z
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov ⟨hxA, hxZ⟩)
      by_cases hiT : i ∈ T
      · exact absurd (hB ⟨hxA, Set.mem_iUnion₂.2 ⟨i, hiT, hi⟩⟩) hxB
      · exact Or.inr (Set.mem_iUnion.2 ⟨⟨i, hiT⟩, hi, hxW⟩)
    · exact Or.inl hxZ
  calc ρ ((A \ B) ∩ W) ≤ ρ (Zᶜ ∪ ⋃ i : {x // x ∉ T}, P i ∩ W) := measure_mono hsub
    _ ≤ ρ Zᶜ + ρ (⋃ i : {x // x ∉ T}, P i ∩ W) := measure_union_le _ _
    _ ≤ 0 + ∑' i : {x // x ∉ T}, ρ (P i ∩ W) := add_le_add hZ.le (measure_iUnion_le _)
    _ ≤ 0 + ∑' i : {x // x ∉ T}, (c i : ℝ≥0∞) * e :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum fun i => hP i)
    _ = (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) * e := by rw [zero_add, ENNReal.tsum_mul_right]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `hBm : MeasurableSet B` using `hBo.measurableSet`. Establish `hφc : Continuous (B.indicator (1 : V → ℝ))`. Use `continuous_indicator ?_ continuous_one.continuousOn` and prove the remaining obligations. Introduce `a ha`.

Simplify using `[frontier, hBc.isClosed.closure_eq, hBo.interior_eq] at ha`. Establish `hφs : HasCompactSupport (B.indicator (1 : V → ℝ))` using `HasCompactSupport.intro hBc fun x hx => by simp [hx]`. Establish `hφt : tsupport (B.indicator (1 : V → ℝ)) ⊆ Z` using `(closure_minimal Set.support_indicator_subset hBc.isClosed).trans hBZ`. Take `⟨hint, hcont⟩` from `h3 _ hφc hφs hφt`. Establish `hfin : ∀ b, m b B ≠ ⊤` using `fun b => by`.

Establish `h4` using `(integrable_indicator_iff hBm).1 (hint b (Set.mem_univ b))`. Conclude with `((integrableOn_const_iff).1 h4).resolve_left (by rw [enorm_eq_zero]; exact (one_ne_zero : (1 : ℝ) ≠ 0)) |>.ne`. Establish `hg : Continuous (fun b => (m b B).toReal)`. Establish `he : (fun b => ∫ v, B.indicator (1 : V → ℝ) v ∂(m b)) = fun b => (m b B).toReal`. Use function extensionality and compare the values at `fun b => integral_indicator_one hBm`.

Rewrite using `[← he]`. Conclude with `continuousOn_univ.1 hcont`. Establish `hform : ∀ S : Set K, MeasurableSet S → μ (B ∩ Q ⁻¹' S) = ∫⁻ b in S, m b B ∂lam`. Introduce `S hS`. Establish `hX : MeasurableSet (B ∩ Q ⁻¹' S)` using `hBm.inter (hQ.measurable hS)`.

Establish `e1` using `h2 ((B ∩ Q ⁻¹' S).indicator 1) (measurable_one.indicator hX)`. Rewrite `e1` using `[lintegral_indicator_one hX]`. Rewrite `e1` using `[Measure.restrict_apply hX, Set.inter_eq_left.2 (Set.inter_subset_left.trans hBZ)]`. Rewrite using `[e1, ← lintegral_indicator hS]`. Use `lintegral_congr fun b => ?_` and prove the remaining obligations.

Distinguish the cases in `hb : b ∈ S`. Rewrite using `[Set.indicator_of_mem hb]`. Use `le_antisymm (measure_mono Set.inter_subset_left) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `measure_mono fun v hv => ?_` and prove the remaining obligations.

Distinguish the cases in `hv' : v ∈ Q ⁻¹' {id b} ∩ Z`. Establish `hq : Q v = b` using `hv'.1`. Conclude with `Or.inl ⟨hv, show Q v ∈ S by rw [hq]; exact hb⟩`. Conclude with `Or.inr hv'`. Use `_ ≤ m b (B ∩ Q ⁻¹' S) + m b (Q ⁻¹' {id b} ∩ Z)ᶜ := measure_union_le _ _`.

Use `_ = m b (B ∩ Q ⁻¹' S) := by rw [h1 b, add_zero]`. Simplify using `only [hb, not_false_eq_true, Set.indicator_of_notMem]`. Use `measure_mono_null (t := (Q ⁻¹' {id b} ∩ Z)ᶜ) ?_ (h1 b)` and prove the remaining obligations. Introduce `v hv hv'`. Apply `hb` to reduce the goal to its premises.

Establish `hq : Q v = b` using `hv'.1`. Rewrite using `[← hq]`. Conclude with `hv.2`. Take `⟨U', hU'n, hU'fin⟩` from `lam.finiteAt_nhds s₀`. Establish `hgn : (fun b => (m b B).toReal) ⁻¹' Set.Ioo ((m s₀ B).toReal - η) ((m s₀ B).toReal + η) ∈ 𝓝 s₀` using `hg.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))`.

Use `⟨U' ∩ (fun b => (m b B).toReal) ⁻¹' Set.Ioo ((m s₀ B).toReal - η) ((m s₀ B).toReal + η), Filter.inter_mem hU'n hgn, fun S hS hSU => ?_⟩` and prove the remaining obligations. Establish `hlam : lam S ≠ ⊤` using `(lt_of_le_of_lt (measure_mono (hSU.trans Set.inter_subset_left)) hU'fin).ne`. Establish `hmb : ∀ b ∈ S, m b B = ENNReal.ofReal (m b B).toReal` using `fun b _ => (ENNReal.ofReal_toReal (hfin b)).symm`. Establish `hup : μ (B ∩ Q ⁻¹' S) ≤ ENNReal.ofReal ((m s₀ B).toReal + η) * lam S`. Rewrite using `[hform S hS, ← setLIntegral_const]`.

Use `setLIntegral_mono' hS fun b hb => ?_` and prove the remaining obligations. Rewrite using `[hmb b hb]`. Conclude with `ENNReal.ofReal_le_ofReal (hSU hb).2.2.le`. Establish `hμfin : μ (B ∩ Q ⁻¹' S) ≠ ⊤` using `ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlam) hup`. Establish `hg0 : 0 ≤ (m s₀ B).toReal` using `ENNReal.toReal_nonneg`.

Establish `hl0 : 0 ≤ (lam S).toReal` using `ENNReal.toReal_nonneg`. Establish `hx0 : 0 ≤ (μ (B ∩ Q ⁻¹' S)).toReal` using `ENNReal.toReal_nonneg`. Establish `hhi : (μ (B ∩ Q ⁻¹' S)).toReal ≤ ((m s₀ B).toReal + η) * (lam S).toReal`. Establish `h5` using `ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlam) hup`. Rewrite `h5` using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]`. Then use the resulting hypothesis.

Use `⟨hlam, hμfin, ?_, hhi⟩` and prove the remaining obligations. Distinguish the cases in `hc : (m s₀ B).toReal - η ≤ 0`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlow : ENNReal.ofReal ((m s₀ B).toReal - η) * lam S ≤ μ (B ∩ Q ⁻¹' S)`. Rewrite using `[hform S hS, ← setLIntegral_const]`.

Use `setLIntegral_mono' hS fun b hb => ?_` and prove the remaining obligations. Rewrite using `[hmb b hb]`. Conclude with `ENNReal.ofReal_le_ofReal (hSU hb).2.1.le`. Establish `h6` using `ENNReal.toReal_mono hμfin hlow`. Rewrite `h6` using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]`. Then use the resulting hypothesis.
-/
theorem near_compact_open {V K : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
    {μ : Measure V} {lam : Measure K} {Q : V → K} {Z : Set V} {m : K → Measure V}
    (hQ : Continuous Q) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m)
    [IsLocallyFiniteMeasure lam] {B : Set V} (hBc : IsCompact B) (hBo : IsOpen B) (hBZ : B ⊆ Z)
    (s₀ : K) {η : ℝ} (hη : 0 < η) :
    ∃ U ∈ 𝓝 s₀, ∀ S : Set K, MeasurableSet S → S ⊆ U → lam S ≠ ⊤ ∧ μ (B ∩ Q ⁻¹' S) ≠ ⊤ ∧
      ((m s₀ B).toReal - η) * (lam S).toReal ≤ (μ (B ∩ Q ⁻¹' S)).toReal ∧
      (μ (B ∩ Q ⁻¹' S)).toReal ≤ ((m s₀ B).toReal + η) * (lam S).toReal := by
  obtain ⟨h1, h2, h3⟩ := h
  have hBm : MeasurableSet B := hBo.measurableSet
  have hφc : Continuous (B.indicator (1 : V → ℝ)) := by
    refine continuous_indicator ?_ continuous_one.continuousOn
    intro a ha
    simp [frontier, hBc.isClosed.closure_eq, hBo.interior_eq] at ha
  have hφs : HasCompactSupport (B.indicator (1 : V → ℝ)) :=
    HasCompactSupport.intro hBc fun x hx => by simp [hx]
  have hφt : tsupport (B.indicator (1 : V → ℝ)) ⊆ Z :=
    (closure_minimal Set.support_indicator_subset hBc.isClosed).trans hBZ
  obtain ⟨hint, hcont⟩ := h3 _ hφc hφs hφt
  have hfin : ∀ b, m b B ≠ ⊤ := fun b => by
    have h4 := (integrable_indicator_iff hBm).1 (hint b (Set.mem_univ b))
    exact ((integrableOn_const_iff).1 h4).resolve_left (by rw [enorm_eq_zero]; exact (one_ne_zero : (1 : ℝ) ≠ 0)) |>.ne
  have hg : Continuous (fun b => (m b B).toReal) := by
    have he : (fun b => ∫ v, B.indicator (1 : V → ℝ) v ∂(m b)) = fun b => (m b B).toReal :=
      funext fun b => integral_indicator_one hBm
    rw [← he]
    exact continuousOn_univ.1 hcont
  have hform : ∀ S : Set K, MeasurableSet S → μ (B ∩ Q ⁻¹' S) = ∫⁻ b in S, m b B ∂lam := by
    intro S hS
    have hX : MeasurableSet (B ∩ Q ⁻¹' S) := hBm.inter (hQ.measurable hS)
    have e1 := h2 ((B ∩ Q ⁻¹' S).indicator 1) (measurable_one.indicator hX)
    simp_rw [lintegral_indicator_one hX] at e1
    rw [Measure.restrict_apply hX, Set.inter_eq_left.2 (Set.inter_subset_left.trans hBZ)] at e1
    rw [e1, ← lintegral_indicator hS]
    refine lintegral_congr fun b => ?_
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      refine le_antisymm (measure_mono Set.inter_subset_left) ?_
      calc m b B ≤ m b (B ∩ Q ⁻¹' S ∪ (Q ⁻¹' {id b} ∩ Z)ᶜ) := by
            refine measure_mono fun v hv => ?_
            by_cases hv' : v ∈ Q ⁻¹' {id b} ∩ Z
            · have hq : Q v = b := hv'.1
              exact Or.inl ⟨hv, show Q v ∈ S by rw [hq]; exact hb⟩
            · exact Or.inr hv'
        _ ≤ m b (B ∩ Q ⁻¹' S) + m b (Q ⁻¹' {id b} ∩ Z)ᶜ := measure_union_le _ _
        _ = m b (B ∩ Q ⁻¹' S) := by rw [h1 b, add_zero]
    · simp only [hb, not_false_eq_true, Set.indicator_of_notMem]
      refine measure_mono_null (t := (Q ⁻¹' {id b} ∩ Z)ᶜ) ?_ (h1 b)
      intro v hv hv'
      apply hb
      have hq : Q v = b := hv'.1
      rw [← hq]; exact hv.2
  obtain ⟨U', hU'n, hU'fin⟩ := lam.finiteAt_nhds s₀
  have hgn : (fun b => (m b B).toReal) ⁻¹' Set.Ioo ((m s₀ B).toReal - η) ((m s₀ B).toReal + η) ∈ 𝓝 s₀ :=
    hg.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  refine ⟨U' ∩ (fun b => (m b B).toReal) ⁻¹' Set.Ioo ((m s₀ B).toReal - η) ((m s₀ B).toReal + η),
    Filter.inter_mem hU'n hgn, fun S hS hSU => ?_⟩
  have hlam : lam S ≠ ⊤ := (lt_of_le_of_lt (measure_mono (hSU.trans Set.inter_subset_left)) hU'fin).ne
  have hmb : ∀ b ∈ S, m b B = ENNReal.ofReal (m b B).toReal := fun b _ => (ENNReal.ofReal_toReal (hfin b)).symm
  have hup : μ (B ∩ Q ⁻¹' S) ≤ ENNReal.ofReal ((m s₀ B).toReal + η) * lam S := by
    rw [hform S hS, ← setLIntegral_const]
    refine setLIntegral_mono' hS fun b hb => ?_
    rw [hmb b hb]
    exact ENNReal.ofReal_le_ofReal (hSU hb).2.2.le
  have hμfin : μ (B ∩ Q ⁻¹' S) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlam) hup
  have hg0 : 0 ≤ (m s₀ B).toReal := ENNReal.toReal_nonneg
  have hl0 : 0 ≤ (lam S).toReal := ENNReal.toReal_nonneg
  have hx0 : 0 ≤ (μ (B ∩ Q ⁻¹' S)).toReal := ENNReal.toReal_nonneg
  have hhi : (μ (B ∩ Q ⁻¹' S)).toReal ≤ ((m s₀ B).toReal + η) * (lam S).toReal := by
    have h5 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlam) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h5
  refine ⟨hlam, hμfin, ?_, hhi⟩
  by_cases hc : (m s₀ B).toReal - η ≤ 0
  · nlinarith
  · have hlow : ENNReal.ofReal ((m s₀ B).toReal - η) * lam S ≤ μ (B ∩ Q ⁻¹' S) := by
      rw [hform S hS, ← setLIntegral_const]
      refine setLIntegral_mono' hS fun b hb => ?_
      rw [hmb b hb]
      exact ENNReal.ofReal_le_ofReal (hSU hb).2.1.le
    have h6 := ENNReal.toReal_mono hμfin hlow
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h6

/- English proof (translation)
Introduce `V K ι _ _ _ _ _ _ _ _ _ μ lam Q Z m hQ h _ hZ A hAc hAo P c hP hcov hc hPS hPm s₀`. Establish `hmZ : ∀ s, m s Zᶜ = 0` using `fun s => measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (h.1 s)`. Establish `hcfin : ∑' i, (c i : ℝ≥0∞) ≠ ⊤` using `ENNReal.tsum_coe_ne_top_iff_summable.2 hc`. Establish `hA1 : m s₀ A < ⊤`. Combine the equalities or inequalities in the displayed calculation.

Use `measure_mono fun x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hz : x ∈ Z`. Conclude with `Or.inl ⟨hx, hz⟩`. Conclude with `Or.inr hz`. Use `_ ≤ m s₀ (A ∩ Z) + m s₀ Zᶜ := measure_union_le _ _`.

Use `_ = m s₀ (A ∩ Z) := by rw [hmZ, add_zero]`. Use `_ ≤ m s₀ (⋃ i, P i) := measure_mono hcov`. Use `_ ≤ ∑' i, m s₀ (P i) := measure_iUnion_le _`. Use `_ ≤ ∑' i, (c i : ℝ≥0∞) := ENNReal.tsum_le_tsum fun i => hPm i s₀`. Use `_ < ⊤ := lt_top_iff_ne_top.2 hcfin`.

Use `⟨hA1, fun ε hε => ?_⟩` and prove the remaining obligations. Take `⟨T, hT⟩` from `((ENNReal.tendsto_tsum_compl_atTop_zero hcfin).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by positivity : (0 : ℝ) < ε / 3)))).exists`. Establish `htne : (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) ≠ ⊤` using `ne_top_of_lt hT`. Establish `htR : (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)).toReal < ε / 3` using `ENNReal.toReal_lt_of_lt_ofReal hT`. Establish `hBc : IsCompact (A ∩ ⋃ i ∈ T, P i)` using `hAc.inter_right (isClosed_biUnion_finset fun i _ => (hP i).1.isClosed)`.

Establish `hBo : IsOpen (A ∩ ⋃ i ∈ T, P i)` using `hAo.inter (isOpen_iUnion fun i => isOpen_iUnion fun _ => (hP i).2.1)`. Establish `hBZ : A ∩ ⋃ i ∈ T, P i ⊆ Z` using `fun x hx => by`. Take `⟨i, -, hi⟩` from `Set.mem_iUnion₂.1 hx.2`. Conclude with `(hP i).2.2 hi`. Take `⟨U, hUn, hU⟩` from `near_compact_open hQ h hBc hBo hBZ s₀ (η := ε / 3) (by positivity)`.

Use `⟨U, hUn, fun S hS hSU => ?_⟩` and prove the remaining obligations. Take `⟨hlam, hμB, hlo, hhi⟩` from `hU S hS hSU`. Establish `htail` using `tail_le μ (W := Q ⁻¹' S) (e := lam S) (T := T) hZ hcov (B := A ∩ ⋃ i ∈ T, P i) Set.Subset.rfl (fun i => hPS i S hS)`. Establish `hAW1 : μ ((A ∩ ⋃ i ∈ T, P i) ∩ Q ⁻¹' S) ≤ μ (A ∩ Q ⁻¹' S)` using `measure_mono (Set.inter_subset_inter_left _ Set.inter_subset_left)`. Establish `hAW2 : μ (A ∩ Q ⁻¹' S) ≤ μ ((A ∩ ⋃ i ∈ T, P i) ∩ Q ⁻¹' S) + (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) * lam S`.

Combine the equalities or inequalities in the displayed calculation. Use `measure_mono fun x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hxB : x ∈ A ∩ ⋃ i ∈ T, P i`. Conclude with `Or.inl ⟨hxB, hx.2⟩`. Conclude with `Or.inr ⟨⟨hx.1, hxB⟩, hx.2⟩`.

Use `_ ≤ _ := measure_union_le _ _`. Use `_ ≤ _ := add_le_add le_rfl htail`. Establish `ht2` using `tail_le (m s₀) (W := Set.univ) (e := 1) (T := T) (hmZ s₀) hcov (B := A ∩ ⋃ i ∈ T, P i) Set.Subset.rfl (fun i => by rw [Set.inter_univ, mul_one]; exact hPm i s₀)`. Rewrite `ht2` using `[Set.inter_univ, mul_one]`. Establish `hm1 : m s₀ (A ∩ ⋃ i ∈ T, P i) ≤ m s₀ A` using `measure_mono Set.inter_subset_left`.

Establish `hm2 : m s₀ A ≤ m s₀ (A ∩ ⋃ i ∈ T, P i) + ∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)`. Combine the equalities or inequalities in the displayed calculation. Use `measure_mono fun x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hxB : x ∈ A ∩ ⋃ i ∈ T, P i`. Conclude with `Or.inl hxB`.

Conclude with `Or.inr ⟨hx, hxB⟩`. Use `_ ≤ _ := measure_union_le _ _`. Use `_ ≤ _ := add_le_add le_rfl ht2`. Establish `hmBfin : m s₀ (A ∩ ⋃ i ∈ T, P i) ≠ ⊤` using `ne_top_of_le_ne_top hA1.ne hm1`. Establish `htl : (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) * lam S ≠ ⊤` using `ENNReal.mul_ne_top htne hlam`.

Establish `hμA : μ (A ∩ Q ⁻¹' S) ≠ ⊤` using `ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hμB, htl⟩) hAW2`. Establish `hx1` using `ENNReal.toReal_mono hμA hAW1`. Establish `hx2` using `ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hμB, htl⟩) hAW2`. Rewrite `hx2` using `[ENNReal.toReal_add hμB htl, ENNReal.toReal_mul]`. Establish `ha1` using `ENNReal.toReal_mono hA1.ne hm1`.

Establish `ha2` using `ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hmBfin, htne⟩) hm2`. Rewrite `ha2` using `[ENNReal.toReal_add hmBfin htne]`. Establish `hl : 0 ≤ (lam S).toReal` using `ENNReal.toReal_nonneg`. Establish `ht0 : 0 ≤ (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)).toReal` using `ENNReal.toReal_nonneg`. Establish `p1` using `mul_le_mul_of_nonneg_right ha1 hl`.

Establish `p2` using `mul_le_mul_of_nonneg_right ha2 hl`. Establish `p3` using `mul_le_mul_of_nonneg_right htR.le hl`. Establish `p4` using `mul_nonneg hε.le hl`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem density_of_summable_cover : ∀ (V K ι : Type) [Countable ι] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ [IsLocallyFiniteMeasure lam], μ Zᶜ = 0 → ∀ A : Set V, IsCompact A → IsOpen A → ∀ (P : ι → Set V) (c : ι → ℝ≥0), (∀ i, IsCompact (P i) ∧ IsOpen (P i) ∧ P i ⊆ Z) → A ∩ Z ⊆ ⋃ i, P i → Summable c → (∀ i (S : Set K), MeasurableSet S → μ (P i ∩ Q ⁻¹' S) ≤ (c i : ℝ≥0∞) * lam S) → (∀ i s, m s (P i) ≤ (c i : ℝ≥0∞)) → ∀ s₀ : K, m s₀ A < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 s₀, ∀ S : Set K, MeasurableSet S → S ⊆ U → |(μ (A ∩ Q ⁻¹' S)).toReal - (m s₀ A).toReal * (lam S).toReal| ≤ ε * (lam S).toReal := by
  intro V K ι _ _ _ _ _ _ _ _ _ μ lam Q Z m hQ h _ hZ A hAc hAo P c hP hcov hc hPS hPm s₀
  have hmZ : ∀ s, m s Zᶜ = 0 := fun s =>
    measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (h.1 s)
  have hcfin : ∑' i, (c i : ℝ≥0∞) ≠ ⊤ := ENNReal.tsum_coe_ne_top_iff_summable.2 hc
  have hA1 : m s₀ A < ⊤ := by
    calc m s₀ A ≤ m s₀ (A ∩ Z ∪ Zᶜ) := by
          refine measure_mono fun x hx => ?_
          by_cases hz : x ∈ Z
          · exact Or.inl ⟨hx, hz⟩
          · exact Or.inr hz
      _ ≤ m s₀ (A ∩ Z) + m s₀ Zᶜ := measure_union_le _ _
      _ = m s₀ (A ∩ Z) := by rw [hmZ, add_zero]
      _ ≤ m s₀ (⋃ i, P i) := measure_mono hcov
      _ ≤ ∑' i, m s₀ (P i) := measure_iUnion_le _
      _ ≤ ∑' i, (c i : ℝ≥0∞) := ENNReal.tsum_le_tsum fun i => hPm i s₀
      _ < ⊤ := lt_top_iff_ne_top.2 hcfin
  refine ⟨hA1, fun ε hε => ?_⟩
  obtain ⟨T, hT⟩ := ((ENNReal.tendsto_tsum_compl_atTop_zero hcfin).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (by positivity : (0 : ℝ) < ε / 3)))).exists
  have htne : (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) ≠ ⊤ := ne_top_of_lt hT
  have htR : (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)).toReal < ε / 3 := ENNReal.toReal_lt_of_lt_ofReal hT
  have hBc : IsCompact (A ∩ ⋃ i ∈ T, P i) :=
    hAc.inter_right (isClosed_biUnion_finset fun i _ => (hP i).1.isClosed)
  have hBo : IsOpen (A ∩ ⋃ i ∈ T, P i) :=
    hAo.inter (isOpen_iUnion fun i => isOpen_iUnion fun _ => (hP i).2.1)
  have hBZ : A ∩ ⋃ i ∈ T, P i ⊆ Z := fun x hx => by
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.1 hx.2
    exact (hP i).2.2 hi
  obtain ⟨U, hUn, hU⟩ := near_compact_open hQ h hBc hBo hBZ s₀ (η := ε / 3) (by positivity)
  refine ⟨U, hUn, fun S hS hSU => ?_⟩
  obtain ⟨hlam, hμB, hlo, hhi⟩ := hU S hS hSU
  have htail := tail_le μ (W := Q ⁻¹' S) (e := lam S) (T := T) hZ hcov
    (B := A ∩ ⋃ i ∈ T, P i) Set.Subset.rfl (fun i => hPS i S hS)
  have hAW1 : μ ((A ∩ ⋃ i ∈ T, P i) ∩ Q ⁻¹' S) ≤ μ (A ∩ Q ⁻¹' S) :=
    measure_mono (Set.inter_subset_inter_left _ Set.inter_subset_left)
  have hAW2 : μ (A ∩ Q ⁻¹' S) ≤ μ ((A ∩ ⋃ i ∈ T, P i) ∩ Q ⁻¹' S) +
      (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) * lam S := by
    calc μ (A ∩ Q ⁻¹' S) ≤ μ ((A ∩ ⋃ i ∈ T, P i) ∩ Q ⁻¹' S ∪ (A \ (A ∩ ⋃ i ∈ T, P i)) ∩ Q ⁻¹' S) := by
          refine measure_mono fun x hx => ?_
          by_cases hxB : x ∈ A ∩ ⋃ i ∈ T, P i
          · exact Or.inl ⟨hxB, hx.2⟩
          · exact Or.inr ⟨⟨hx.1, hxB⟩, hx.2⟩
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl htail
  have ht2 := tail_le (m s₀) (W := Set.univ) (e := 1) (T := T) (hmZ s₀) hcov
    (B := A ∩ ⋃ i ∈ T, P i) Set.Subset.rfl (fun i => by rw [Set.inter_univ, mul_one]; exact hPm i s₀)
  rw [Set.inter_univ, mul_one] at ht2
  have hm1 : m s₀ (A ∩ ⋃ i ∈ T, P i) ≤ m s₀ A := measure_mono Set.inter_subset_left
  have hm2 : m s₀ A ≤ m s₀ (A ∩ ⋃ i ∈ T, P i) + ∑' i : {x // x ∉ T}, (c i : ℝ≥0∞) := by
    calc m s₀ A ≤ m s₀ ((A ∩ ⋃ i ∈ T, P i) ∪ A \ (A ∩ ⋃ i ∈ T, P i)) := by
          refine measure_mono fun x hx => ?_
          by_cases hxB : x ∈ A ∩ ⋃ i ∈ T, P i
          · exact Or.inl hxB
          · exact Or.inr ⟨hx, hxB⟩
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl ht2
  have hmBfin : m s₀ (A ∩ ⋃ i ∈ T, P i) ≠ ⊤ := ne_top_of_le_ne_top hA1.ne hm1
  have htl : (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) * lam S ≠ ⊤ := ENNReal.mul_ne_top htne hlam
  have hμA : μ (A ∩ Q ⁻¹' S) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hμB, htl⟩) hAW2
  have hx1 := ENNReal.toReal_mono hμA hAW1
  have hx2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hμB, htl⟩) hAW2
  rw [ENNReal.toReal_add hμB htl, ENNReal.toReal_mul] at hx2
  have ha1 := ENNReal.toReal_mono hA1.ne hm1
  have ha2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hmBfin, htne⟩) hm2
  rw [ENNReal.toReal_add hmBfin htne] at ha2
  have hl : 0 ≤ (lam S).toReal := ENNReal.toReal_nonneg
  have ht0 : 0 ≤ (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)).toReal := ENNReal.toReal_nonneg
  have p1 := mul_le_mul_of_nonneg_right ha1 hl
  have p2 := mul_le_mul_of_nonneg_right ha2 hl
  have p3 := mul_le_mul_of_nonneg_right htR.le hl
  have p4 := mul_nonneg hε.le hl
  rw [abs_le]
  constructor <;> nlinarith

end GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity
