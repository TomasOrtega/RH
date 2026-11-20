import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

noncomputable section

namespace PI.OmFibreUniq.W

open MeasureTheory Topology Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

section Gen

variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [TotallyDisconnectedSpace V]

/- English proof (translation)
Take `⟨s, hs, hsW, hsc⟩` from `local_compact_nhds (hW.mem_nhds hx)`. Take `⟨K, hKmem, hxK, hKsub⟩` from `(loc_compact_Haus_tot_disc_of_zero_dim (H := V)).exists_subset_of_mem_open (mem_interior_iff_mem_nhds.2 hs) isOpen_interior`. Establish `hKc : IsClopen K` using `hKmem`. Conclude with `⟨K, hsc.of_isClosed_subset hKc.1 (hKsub.trans interior_subset), hKc.2, hxK, hKsub.trans (interior_subset.trans hsW)⟩`.
-/
theorem exists_compact_open {W : Set V} (hW : IsOpen W) {x : V} (hx : x ∈ W) :
    ∃ K, IsCompact K ∧ IsOpen K ∧ x ∈ K ∧ K ⊆ W := by
  obtain ⟨s, hs, hsW, hsc⟩ := local_compact_nhds (hW.mem_nhds hx)
  obtain ⟨K, hKmem, hxK, hKsub⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := V)).exists_subset_of_mem_open
    (mem_interior_iff_mem_nhds.2 hs) isOpen_interior
  have hKc : IsClopen K := hKmem
  exact ⟨K, hsc.of_isClosed_subset hKc.1 (hKsub.trans interior_subset), hKc.2, hxK,
    hKsub.trans (interior_subset.trans hsW)⟩

variable [SecondCountableTopology V]

/- English proof (translation)
Use `choose K hK using fun x : W => exists_compact_open hW x.2`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable K (fun x => (hK x).2.1)`. Use `⟨K '' T, hTc.image K, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, _, rfl⟩`. Conclude with `⟨(hK x).1, (hK x).2.1, (hK x).2.2.2⟩`.

Rewrite using `[sUnion_image, hTU]`. Use extensionality with `y`. Simplify using `only [mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hy⟩`.

Conclude with `(hK x).2.2.2 hy`. Introduce `hy`. Conclude with `⟨⟨y, hy⟩, (hK ⟨y, hy⟩).2.2.1⟩`.
-/
theorem open_eq_countable_union {W : Set V} (hW : IsOpen W) :
    ∃ T : Set (Set V), T.Countable ∧ (∀ K ∈ T, IsCompact K ∧ IsOpen K ∧ K ⊆ W) ∧ ⋃₀ T = W := by
  choose K hK using fun x : W => exists_compact_open hW x.2
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable K (fun x => (hK x).2.1)
  refine ⟨K '' T, hTc.image K, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨(hK x).1, (hK x).2.1, (hK x).2.2.2⟩
  · rw [sUnion_image, hTU]
    ext y
    simp only [mem_iUnion]
    constructor
    · rintro ⟨x, hy⟩
      exact (hK x).2.2.2 hy
    · intro hy
      exact ⟨⟨y, hy⟩, (hK ⟨y, hy⟩).2.2.1⟩

variable [MeasurableSpace V] [BorelSpace V]

/- English proof (translation)
Establish `key : ∀ O, IsOpen O → O ⊆ U → m O = m' O`. Introduce `O hO hOU`. Take `⟨T, hTc, hT, hTO⟩` from `open_eq_countable_union hO`. Break down `T.eq_empty_or_nonempty with he | hne` into its components or cases. Rewrite using `[← hTO, he, sUnion_empty, measure_empty, measure_empty]`.

Take `⟨g, rfl⟩` from `hTc.exists_eq_range hne`. Establish `hacc : ∀ n, IsCompact (accumulate g n) ∧ IsOpen (accumulate g n) ∧ accumulate g n ⊆ U`. Introduce `n`. Establish `hg : ∀ k, IsCompact (g k) ∧ IsOpen (g k) ∧ g k ⊆ O` using `fun k => hT _ ⟨k, rfl⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[accumulate_def]`. Conclude with `(finite_le_nat n).isCompact_biUnion fun k _ => (hg k).1`. Rewrite using `[accumulate_def]`. Conclude with `isOpen_biUnion fun k _ => (hg k).2.1`. Rewrite using `[accumulate_def]`.

Conclude with `iUnion₂_subset fun k _ => (hg k).2.2.trans hOU`. Rewrite using `[← hTO, sUnion_range, measure_iUnion_eq_iSup_accumulate, measure_iUnion_eq_iSup_accumulate]`. Use `congr 1`. Use function extensionality and compare the values at `n`. Conclude with `(hK _ (hacc n).1 (hacc n).2.1 (hacc n).2.2).2`.

Establish `hres : m.restrict U = m'.restrict U`. Take `⟨T, hTc, hT, hTU⟩` from `open_eq_countable_union hU`. Rewrite using `[← hTU]`. Use `(Measure.restrict_sUnion_congr hTc).2 fun K hKT => ?_` and prove the remaining obligations. Take `⟨hKc, hKo, hKU⟩` from `hT K hKT`.

Take `⟨hfin, heq⟩` from `hK K hKc hKo hKU`. Use `haveI : IsFiniteMeasure (m.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩`. Use `ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_` and prove the remaining obligations. Introduce `O hO`. Rewrite using `[Measure.restrict_apply hO.measurableSet, Measure.restrict_apply hO.measurableSet]`.

Conclude with `key _ (hO.inter hKo) (inter_subset_right.trans hKU)`. Rewrite using `[Measure.restrict_apply_univ, Measure.restrict_apply_univ, heq]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem measure_ext_of_compactOpen {U : Set V} (hU : IsOpen U) (m m' : Measure V)
    (h0 : m Uᶜ = 0) (h0' : m' Uᶜ = 0)
    (hK : ∀ K, IsCompact K → IsOpen K → K ⊆ U → m K < ∞ ∧ m K = m' K) : m = m' := by
  have key : ∀ O, IsOpen O → O ⊆ U → m O = m' O := by
    intro O hO hOU
    obtain ⟨T, hTc, hT, hTO⟩ := open_eq_countable_union hO
    rcases T.eq_empty_or_nonempty with he | hne
    · rw [← hTO, he, sUnion_empty, measure_empty, measure_empty]
    obtain ⟨g, rfl⟩ := hTc.exists_eq_range hne
    have hacc : ∀ n, IsCompact (accumulate g n) ∧ IsOpen (accumulate g n) ∧ accumulate g n ⊆ U := by
      intro n
      have hg : ∀ k, IsCompact (g k) ∧ IsOpen (g k) ∧ g k ⊆ O := fun k => hT _ ⟨k, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [accumulate_def]
        exact (finite_le_nat n).isCompact_biUnion fun k _ => (hg k).1
      · rw [accumulate_def]
        exact isOpen_biUnion fun k _ => (hg k).2.1
      · rw [accumulate_def]
        exact iUnion₂_subset fun k _ => (hg k).2.2.trans hOU
    rw [← hTO, sUnion_range, measure_iUnion_eq_iSup_accumulate, measure_iUnion_eq_iSup_accumulate]
    congr 1
    funext n
    exact (hK _ (hacc n).1 (hacc n).2.1 (hacc n).2.2).2
  have hres : m.restrict U = m'.restrict U := by
    obtain ⟨T, hTc, hT, hTU⟩ := open_eq_countable_union hU
    rw [← hTU]
    refine (Measure.restrict_sUnion_congr hTc).2 fun K hKT => ?_
    obtain ⟨hKc, hKo, hKU⟩ := hT K hKT
    obtain ⟨hfin, heq⟩ := hK K hKc hKo hKU
    haveI : IsFiniteMeasure (m.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_
    · intro O hO
      rw [Measure.restrict_apply hO.measurableSet, Measure.restrict_apply hO.measurableSet]
      exact key _ (hO.inter hKo) (inter_subset_right.trans hKU)
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ, heq]
  calc m = m.restrict U := (Measure.restrict_eq_self_of_ae_mem (ae_iff.2 h0)).symm
    _ = m'.restrict U := hres
    _ = m' := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 h0')

end Gen

section Fib

variable {V X Y : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [TotallyDisconnectedSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

/- English proof (translation)
Establish `hKcl : IsClopen K` using `⟨hKc.isClosed, hKo⟩`. Establish `hKm : MeasurableSet K` using `hKo.measurableSet`. Establish `hcont : Continuous (K.indicator (1 : V → ℝ))` using `hKcl.continuous_indicator continuous_const`. Establish `hcs : HasCompactSupport (K.indicator (1 : V → ℝ))` using `HasCompactSupport.intro hKc fun x hx => by simp [hx]`. Establish `hts : tsupport (K.indicator (1 : V → ℝ)) ⊆ U` using `(closure_minimal (support_indicator_subset) hKcl.1).trans hKU`.

Take `⟨hint, hco⟩` from `h.2.2 _ hcont hcs hts`. Establish `hEq : (fun b => ∫ v, K.indicator (1 : V → ℝ) v ∂(fib b)) = fun b => (fib b K).toReal`. Use function extensionality and compare the values at `b`. Rewrite using `[integral_indicator_one hKm]`. Both sides reduce to the same expression.

Use `⟨fun b => ?_, ?_⟩` and prove the remaining obligations. Establish `hfi` using `(hint b (mem_univ b)).2`. Establish `hl : ∫⁻ x, ‖K.indicator (1 : V → ℝ) x‖ₑ ∂(fib b) = fib b K`. Rewrite using `[← lintegral_indicator_one hKm]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Apply the tactic sequence `by_cases hx : x ∈ K <;> simp [hx]`. Rewrite using `[← hl]`. Conclude with `hfi`. Rewrite using `[← hEq]`.

Conclude with `continuousOn_univ.1 hco`.
-/
theorem fib_compactOpen {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
    {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν Set.univ fib) {K : Set V}
    (hKc : IsCompact K) (hKo : IsOpen K) (hKU : K ⊆ U) :
    (∀ b, fib b K < ∞) ∧ Continuous (fun b => (fib b K).toReal) := by
  have hKcl : IsClopen K := ⟨hKc.isClosed, hKo⟩
  have hKm : MeasurableSet K := hKo.measurableSet
  have hcont : Continuous (K.indicator (1 : V → ℝ)) := hKcl.continuous_indicator continuous_const
  have hcs : HasCompactSupport (K.indicator (1 : V → ℝ)) :=
    HasCompactSupport.intro hKc fun x hx => by simp [hx]
  have hts : tsupport (K.indicator (1 : V → ℝ)) ⊆ U :=
    (closure_minimal (support_indicator_subset) hKcl.1).trans hKU
  obtain ⟨hint, hco⟩ := h.2.2 _ hcont hcs hts
  have hEq : (fun b => ∫ v, K.indicator (1 : V → ℝ) v ∂(fib b)) = fun b => (fib b K).toReal := by
    funext b
    rw [integral_indicator_one hKm]
    rfl
  refine ⟨fun b => ?_, ?_⟩
  · have hfi := (hint b (mem_univ b)).2
    have hl : ∫⁻ x, ‖K.indicator (1 : V → ℝ) x‖ₑ ∂(fib b) = fib b K := by
      rw [← lintegral_indicator_one hKm]
      congr 1
      funext x
      by_cases hx : x ∈ K <;> simp [hx]
    rw [← hl]
    exact hfi
  · rw [← hEq]
    exact continuousOn_univ.1 hco

variable (μ : Measure V) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
  (f : V → Y) (ι : X → Y) (U : Set V)

/- English proof (translation)
Establish `hm : MeasurableSet (K ∩ f ⁻¹' (ι '' S))` using `hKm.inter (hA S hS)`. Rewrite using `[h.2.1 _ (measurable_one.indicator hm), ← lintegral_indicator hS]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[lintegral_indicator_one hm]`.

Establish `hC` using `h.1 b`. Distinguish the cases in `hb : b ∈ S`. Rewrite using `[indicator_of_mem hb]`. Apply `le_antisymm` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Apply `measure_mono` to reduce the goal to its premises. Introduce `v hv`. Distinguish the cases in `hv' : v ∈ f ⁻¹' {ι b} ∩ U`. Use `left`. Conclude with `⟨hv, ⟨b, hb, hv'.1.symm⟩⟩`.

Use `right`. Conclude with `hv'`. Use `_ ≤ fib b (K ∩ f ⁻¹' (ι '' S)) + fib b (f ⁻¹' {ι b} ∩ U)ᶜ := measure_union_le _ _`. Use `_ = fib b (K ∩ f ⁻¹' (ι '' S)) := by rw [hC, add_zero]`. Conclude with `measure_mono inter_subset_left`.

Establish `hz : fib b (K ∩ f ⁻¹' (ι '' S)) = 0`. Apply `measure_mono_null _ hC` to reduce the goal to its premises. Introduce `v hv hvC`. Take `⟨b', hb', he⟩` from `hv.2`. Establish `: ι b' = ι b` using `he.trans hvC.1`.

Rewrite `hb'` using `[hι this]`. Conclude with `hb hb'`. Rewrite using `[hz]`. Simplify using `[hb]`.
-/
theorem fib_setLIntegral (hA : ∀ S : Set X, MeasurableSet S → MeasurableSet (f ⁻¹' (ι '' S)))
    (hι : Function.Injective ι) {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν Set.univ fib)
    {K : Set V} (hKm : MeasurableSet K) (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ b in S, fib b K ∂ν = ∫⁻ x in U, (K ∩ f ⁻¹' (ι '' S)).indicator 1 x ∂μ := by
  have hm : MeasurableSet (K ∩ f ⁻¹' (ι '' S)) := hKm.inter (hA S hS)
  rw [h.2.1 _ (measurable_one.indicator hm), ← lintegral_indicator hS]
  congr 1
  funext b
  rw [lintegral_indicator_one hm]
  have hC := h.1 b
  by_cases hb : b ∈ S
  · rw [indicator_of_mem hb]
    apply le_antisymm
    · calc fib b K ≤ fib b ((K ∩ f ⁻¹' (ι '' S)) ∪ (f ⁻¹' {ι b} ∩ U)ᶜ) := by
            apply measure_mono
            intro v hv
            by_cases hv' : v ∈ f ⁻¹' {ι b} ∩ U
            · left
              exact ⟨hv, ⟨b, hb, hv'.1.symm⟩⟩
            · right
              exact hv'
        _ ≤ fib b (K ∩ f ⁻¹' (ι '' S)) + fib b (f ⁻¹' {ι b} ∩ U)ᶜ := measure_union_le _ _
        _ = fib b (K ∩ f ⁻¹' (ι '' S)) := by rw [hC, add_zero]
    · exact measure_mono inter_subset_left
  · have hz : fib b (K ∩ f ⁻¹' (ι '' S)) = 0 := by
      apply measure_mono_null _ hC
      intro v hv hvC
      obtain ⟨b', hb', he⟩ := hv.2
      have : ι b' = ι b := he.trans hvC.1
      rw [hι this] at hb'
      exact hb hb'
    rw [hz]
    simp [hb]

/- English proof (translation)
Establish `hKeq : ∀ K, IsCompact K → IsOpen K → K ⊆ U → ∀ b, fib b K = fib' b K`. Introduce `K hKc hKo hKU`. Establish `hK1` using `fib_compactOpen h hKc hKo hKU`. Establish `hK2` using `fib_compactOpen h' hKc hKo hKU`. Establish `hKm : MeasurableSet K` using `hKo.measurableSet`.

Establish `hm1 : Measurable (fun b => fib b K)`. Establish `: (fun b => fib b K) = fun b => ENNReal.ofReal ((fib b K).toReal)`. Use function extensionality and compare the values at `b`. Rewrite using `[ENNReal.ofReal_toReal (hK1.1 b).ne]`. Rewrite using `[this]`.

Conclude with `hK1.2.measurable.ennreal_ofReal`. Establish `hm2 : Measurable (fun b => fib' b K)`. Establish `: (fun b => fib' b K) = fun b => ENNReal.ofReal ((fib' b K).toReal)`. Use function extensionality and compare the values at `b`. Rewrite using `[ENNReal.ofReal_toReal (hK2.1 b).ne]`.

Rewrite using `[this]`. Conclude with `hK2.2.measurable.ennreal_ofReal`. Establish `hae : (fun b => fib b K) =ᵐ[ν] fun b => fib' b K` using `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hm1 hm2 fun S hS _ => by`. Rewrite using `[fib_setLIntegral μ ν f ι U hA hι h hKm S hS, fib_setLIntegral μ ν f ι U hA hι h' hKm S hS]`. Establish `hae' : (fun b => (fib b K).toReal) =ᵐ[ν] fun b => (fib' b K).toReal` using `hae.mono fun b hb => by simp only at hb ⊢; rw [hb]`.

Establish `heq` using `(hK1.2.ae_eq_iff_eq ν hK2.2).1 hae'`. Introduce `b`. Conclude with `(ENNReal.toReal_eq_toReal_iff' (hK1.1 b).ne (hK2.1 b).ne).1 (congrFun heq b)`. Use function extensionality and compare the values at `b`. Establish `h0 : fib b Uᶜ = 0` using `measure_mono_null (compl_subset_compl.2 inter_subset_right) (h.1 b)`.

Establish `h0' : fib' b Uᶜ = 0` using `measure_mono_null (compl_subset_compl.2 inter_subset_right) (h'.1 b)`. Conclude with `measure_ext_of_compactOpen hU (fib b) (fib' b) h0 h0' fun K hKc hKo hKU => ⟨(fib_compactOpen h hKc hKo hKU).1 b, hKeq K hKc hKo hKU b⟩`.
-/
theorem fib_unique (hA : ∀ S : Set X, MeasurableSet S → MeasurableSet (f ⁻¹' (ι '' S)))
    (hι : Function.Injective ι) (hU : IsOpen U) (fib fib' : X → Measure V)
    (h : IsFibreFamily μ f ι U ν Set.univ fib) (h' : IsFibreFamily μ f ι U ν Set.univ fib') :
    fib = fib' := by
  have hKeq : ∀ K, IsCompact K → IsOpen K → K ⊆ U → ∀ b, fib b K = fib' b K := by
    intro K hKc hKo hKU
    have hK1 := fib_compactOpen h hKc hKo hKU
    have hK2 := fib_compactOpen h' hKc hKo hKU
    have hKm : MeasurableSet K := hKo.measurableSet
    have hm1 : Measurable (fun b => fib b K) := by
      have : (fun b => fib b K) = fun b => ENNReal.ofReal ((fib b K).toReal) := by
        funext b; rw [ENNReal.ofReal_toReal (hK1.1 b).ne]
      rw [this]; exact hK1.2.measurable.ennreal_ofReal
    have hm2 : Measurable (fun b => fib' b K) := by
      have : (fun b => fib' b K) = fun b => ENNReal.ofReal ((fib' b K).toReal) := by
        funext b; rw [ENNReal.ofReal_toReal (hK2.1 b).ne]
      rw [this]; exact hK2.2.measurable.ennreal_ofReal
    have hae : (fun b => fib b K) =ᵐ[ν] fun b => fib' b K :=
      ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hm1 hm2 fun S hS _ => by
        rw [fib_setLIntegral μ ν f ι U hA hι h hKm S hS, fib_setLIntegral μ ν f ι U hA hι h' hKm S hS]
    have hae' : (fun b => (fib b K).toReal) =ᵐ[ν] fun b => (fib' b K).toReal :=
      hae.mono fun b hb => by simp only at hb ⊢; rw [hb]
    have heq := (hK1.2.ae_eq_iff_eq ν hK2.2).1 hae'
    intro b
    exact (ENNReal.toReal_eq_toReal_iff' (hK1.1 b).ne (hK2.1 b).ne).1 (congrFun heq b)
  funext b
  have h0 : fib b Uᶜ = 0 := measure_mono_null (compl_subset_compl.2 inter_subset_right) (h.1 b)
  have h0' : fib' b Uᶜ = 0 := measure_mono_null (compl_subset_compl.2 inter_subset_right) (h'.1 b)
  exact measure_ext_of_compactOpen hU (fib b) (fib' b) h0 h0' fun K hKc hKo hKU =>
    ⟨(fib_compactOpen h hKc hKo hKU).1 b, hKeq K hKc hKo hKU b⟩

end Fib

end PI.OmFibreUniq.W
