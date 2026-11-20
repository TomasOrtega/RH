import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushSupp

noncomputable section

namespace PI.AprimeInfW.DG

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}

/- English proof (translation)
Rewrite using `[ae_iff]`. Use `measure_mono_null (fun v hv => ?_) (hfib.1 b)` and prove the remaining obligations. Simplify using `only [mem_setOf_eq] at hv`. Simplify using `only [mem_compl_iff, mem_inter_iff, mem_preimage, mem_singleton_iff, not_and]`. Introduce `h1 _`.

Conclude with `hv (hι (by rw [← hff', h1]))`.
-/
theorem ae_fib (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (b : X) :
    ∀ᵐ v ∂(fib b), f' v = b := by
  rw [ae_iff]
  refine measure_mono_null (fun v hv => ?_) (hfib.1 b)
  simp only [mem_setOf_eq] at hv
  simp only [mem_compl_iff, mem_inter_iff, mem_preimage, mem_singleton_iff, not_and]
  intro h1 _
  exact hv (hι (by rw [← hff', h1]))

/- English proof (translation)
Establish `hSm : MeasurableSet S` using `hS.isClosed.measurableSet`. Establish `hAm : MeasurableSet (f' ⁻¹' S)` using `(hS.isClosed.preimage hf').measurableSet`. Establish `h3` using `hfib.2.2 ρ hρc hρs hρU`. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hρ0) hρc.aestronglyMeasurable, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun b => integral_nonneg fun v => hρ0 v) ((h3.2.mono hSB).aestronglyMeasurable hSm)]`. Use `congr 1`.

Establish `hmeas : Measurable fun v => ENNReal.ofReal (ρ v)` using `hρc.measurable.ennreal_ofReal`. Establish `hsupp : ((f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v))).support ⊆ U`. Introduce `v hv`. Apply `hρU` to reduce the goal to its premises. Apply `subset_tsupport` to reduce the goal to its premises.

Introduce `h0`. Apply `hv` to reduce the goal to its premises. Simplify using `[h0]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[setLIntegral_eq_of_support_subset hsupp, lintegral_indicator hAm]`.

Use `_ = ∫⁻ b, ∫⁻ v, (f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v)) v ∂(fib b) ∂ν := hfib.2.1 _ (hmeas.indicator hAm)`. Use `_ = ∫⁻ b, S.indicator (fun b => ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b)) b ∂ν := by`. Use `lintegral_congr fun b => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b ∈ S`. Rewrite using `[Set.indicator_of_mem hb]`.

Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_fib hfib hff' hι b] with v hv`. Establish `hv' : v ∈ f' ⁻¹' S` using `by simp [hv, hb]`. Simplify using `[Set.indicator_of_mem hv']`. Establish `e0 : S.indicator (fun b => ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b)) b = 0`.

Simplify using `[hb]`. Rewrite using `[e0]`. Establish `: (fun v => (f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v)) v) =ᵐ[fib b] fun _ => 0` using `by filter_upwards [ae_fib hfib hff' hι b] with v hv`. Establish `hv' : v ∉ f' ⁻¹' S` using `by simp [hv, hb]`. Simplify using `[hv']`.

Rewrite using `[lintegral_congr_ae this, lintegral_zero]`. Use `_ = ∫⁻ b in S, ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b) ∂ν := lintegral_indicator hSm _`. Use `_ = ∫⁻ b in S, ENNReal.ofReal (∫ v, ρ v ∂(fib b)) ∂ν := by`. Use `setLIntegral_congr_fun hSm ?_` and prove the remaining obligations. Introduce `b hb`.

Conclude with `(ofReal_integral_eq_lintegral_ofReal (h3.1 b (hSB hb)) (Eventually.of_forall hρ0)).symm`.
-/
theorem fib_set_nonneg [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hρ0 : ∀ v, 0 ≤ ρ v) (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hAm : MeasurableSet (f' ⁻¹' S) := (hS.isClosed.preimage hf').measurableSet
  have h3 := hfib.2.2 ρ hρc hρs hρU
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hρ0) hρc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun b => integral_nonneg fun v => hρ0 v)
      ((h3.2.mono hSB).aestronglyMeasurable hSm)]
  congr 1
  have hmeas : Measurable fun v => ENNReal.ofReal (ρ v) := hρc.measurable.ennreal_ofReal
  have hsupp : ((f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v))).support ⊆ U := by
    intro v hv
    apply hρU
    apply subset_tsupport
    intro h0
    apply hv
    simp [h0]
  calc ∫⁻ v in f' ⁻¹' S, ENNReal.ofReal (ρ v) ∂μ
      = ∫⁻ v in U, (f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v)) v ∂μ := by
        rw [setLIntegral_eq_of_support_subset hsupp, lintegral_indicator hAm]
    _ = ∫⁻ b, ∫⁻ v, (f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v)) v ∂(fib b) ∂ν :=
        hfib.2.1 _ (hmeas.indicator hAm)
    _ = ∫⁻ b, S.indicator (fun b => ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b)) b ∂ν := by
        refine lintegral_congr fun b => ?_
        by_cases hb : b ∈ S
        · rw [Set.indicator_of_mem hb]
          refine lintegral_congr_ae ?_
          filter_upwards [ae_fib hfib hff' hι b] with v hv
          have hv' : v ∈ f' ⁻¹' S := by simp [hv, hb]
          simp [Set.indicator_of_mem hv']
        · have e0 : S.indicator (fun b => ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b)) b = 0 := by
            simp [hb]
          rw [e0]
          have : (fun v => (f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v)) v)
              =ᵐ[fib b] fun _ => 0 := by
            filter_upwards [ae_fib hfib hff' hι b] with v hv
            have hv' : v ∉ f' ⁻¹' S := by simp [hv, hb]
            simp [hv']
          rw [lintegral_congr_ae this, lintegral_zero]
    _ = ∫⁻ b in S, ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b) ∂ν := lintegral_indicator hSm _
    _ = ∫⁻ b in S, ENNReal.ofReal (∫ v, ρ v ∂(fib b)) ∂ν := by
        refine setLIntegral_congr_fun hSm ?_
        intro b hb
        exact (ofReal_integral_eq_lintegral_ofReal (h3.1 b (hSB hb))
          (Eventually.of_forall hρ0)).symm

/- English proof (translation)
Establish `hSm : MeasurableSet S` using `hS.isClosed.measurableSet`. Establish `hpc : Continuous fun v => max (ρ v) 0` using `hρc.max continuous_const`. Establish `hnc : Continuous fun v => max (-ρ v) 0` using `hρc.neg.max continuous_const`. Establish `hps : HasCompactSupport fun v => max (ρ v) 0` using `hρs.comp_left (g := fun t : ℝ => max t 0) (by simp)`. Establish `hns : HasCompactSupport fun v => max (-ρ v) 0` using `hρs.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)`.

Establish `hpU : tsupport (fun v => max (ρ v) 0) ⊆ U`. Use `(closure_mono fun v hv => ?_).trans hρU` and prove the remaining obligations. Introduce `h0`. Apply `hv` to reduce the goal to its premises. Simplify using `[h0]`.

Establish `hnU : tsupport (fun v => max (-ρ v) 0) ⊆ U`. Use `(closure_mono fun v hv => ?_).trans hρU` and prove the remaining obligations. Introduce `h0`. Apply `hv` to reduce the goal to its premises. Simplify using `[h0]`.

Establish `hp3` using `hfib.2.2 _ hpc hps hpU`. Establish `hn3` using `hfib.2.2 _ hnc hns hnU`. Establish `hsplit : ∀ v, ρ v = max (ρ v) 0 - max (-ρ v) 0` using `fun v => (max_zero_sub_eq_self (ρ v)).symm`. Establish `hIp : IntegrableOn (fun b => ∫ v, max (ρ v) 0 ∂(fib b)) S ν` using `(hp3.2.mono hSB).integrableOn_compact hS`. Establish `hIn : IntegrableOn (fun b => ∫ v, max (-ρ v) 0 ∂(fib b)) S ν` using `(hn3.2.mono hSB).integrableOn_compact hS`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `hsplit v`. Use `_ = ∫ v in f' ⁻¹' S, max (ρ v) 0 ∂μ - ∫ v in f' ⁻¹' S, max (-ρ v) 0 ∂μ := integral_sub (hpc.integrable_of_hasCompactSupport hps).integrableOn (hnc.integrable_of_hasCompactSupport hns).integrableOn`.

Use `_ = ∫ b in S, (∫ v, max (ρ v) 0 ∂(fib b)) ∂ν - ∫ b in S, (∫ v, max (-ρ v) 0 ∂(fib b)) ∂ν := by`. Rewrite using `[fib_set_nonneg hfib hf' hff' hι _ hpc hps hpU (fun v => le_max_right _ _) S hS hSB, fib_set_nonneg hfib hf' hff' hι _ hnc hns hnU (fun v => le_max_right _ _) S hS hSB]`. Use `_ = ∫ b in S, (∫ v, max (ρ v) 0 ∂(fib b) - ∫ v, max (-ρ v) 0 ∂(fib b)) ∂ν := (integral_sub hIp hIn).symm`. Use `_ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by`. Use `setIntegral_congr_fun hSm fun b hb => ?_` and prove the remaining obligations.

Rewrite using `[← integral_sub (hp3.1 b (hSB hb)) (hn3.1 b (hSB hb))]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `(hsplit v).symm`.
-/
theorem fib_set [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hpc : Continuous fun v => max (ρ v) 0 := hρc.max continuous_const
  have hnc : Continuous fun v => max (-ρ v) 0 := hρc.neg.max continuous_const
  have hps : HasCompactSupport fun v => max (ρ v) 0 :=
    hρs.comp_left (g := fun t : ℝ => max t 0) (by simp)
  have hns : HasCompactSupport fun v => max (-ρ v) 0 :=
    hρs.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)
  have hpU : tsupport (fun v => max (ρ v) 0) ⊆ U := by
    refine (closure_mono fun v hv => ?_).trans hρU
    intro h0
    apply hv
    simp [h0]
  have hnU : tsupport (fun v => max (-ρ v) 0) ⊆ U := by
    refine (closure_mono fun v hv => ?_).trans hρU
    intro h0
    apply hv
    simp [h0]
  have hp3 := hfib.2.2 _ hpc hps hpU
  have hn3 := hfib.2.2 _ hnc hns hnU
  have hsplit : ∀ v, ρ v = max (ρ v) 0 - max (-ρ v) 0 := fun v =>
    (max_zero_sub_eq_self (ρ v)).symm
  have hIp : IntegrableOn (fun b => ∫ v, max (ρ v) 0 ∂(fib b)) S ν :=
    (hp3.2.mono hSB).integrableOn_compact hS
  have hIn : IntegrableOn (fun b => ∫ v, max (-ρ v) 0 ∂(fib b)) S ν :=
    (hn3.2.mono hSB).integrableOn_compact hS
  calc ∫ v in f' ⁻¹' S, ρ v ∂μ
      = ∫ v in f' ⁻¹' S, (max (ρ v) 0 - max (-ρ v) 0) ∂μ := by
        congr 1
        funext v
        exact hsplit v
    _ = ∫ v in f' ⁻¹' S, max (ρ v) 0 ∂μ - ∫ v in f' ⁻¹' S, max (-ρ v) 0 ∂μ :=
        integral_sub (hpc.integrable_of_hasCompactSupport hps).integrableOn
          (hnc.integrable_of_hasCompactSupport hns).integrableOn
    _ = ∫ b in S, (∫ v, max (ρ v) 0 ∂(fib b)) ∂ν -
          ∫ b in S, (∫ v, max (-ρ v) 0 ∂(fib b)) ∂ν := by
        rw [fib_set_nonneg hfib hf' hff' hι _ hpc hps hpU (fun v => le_max_right _ _) S hS hSB,
          fib_set_nonneg hfib hf' hff' hι _ hnc hns hnU (fun v => le_max_right _ _) S hS hSB]
    _ = ∫ b in S, (∫ v, max (ρ v) 0 ∂(fib b) - ∫ v, max (-ρ v) 0 ∂(fib b)) ∂ν :=
        (integral_sub hIp hIn).symm
    _ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
        refine setIntegral_congr_fun hSm fun b hb => ?_
        rw [← integral_sub (hp3.1 b (hSB hb)) (hn3.1 b (hSB hb))]
        congr 1
        funext v
        exact (hsplit v).symm

/- English proof (translation)
Establish `claim : ∀ G : X → ℝ, ContinuousOn G W → (∀ S, IsCompact S → S ⊆ W → ∫ b in S, G b ∂ν = 0) → ¬ (0 < G b0)`. Introduce `G hG h0G hpos`. Establish `hcont : ContinuousAt G b0` using `(hG b0 (mem_of_mem_nhds hW)).continuousAt hW`. Establish `hev : ∀ᶠ b in 𝓝 b0, G b0 / 2 < G b` using `hcont.eventually (lt_mem_nhds (half_lt_self hpos))`. Take `⟨K, hK, hKN, hKc⟩` from `local_compact_nhds (inter_mem hev hW)`.

Establish `hKW : K ⊆ W` using `hKN.trans inter_subset_right`. Establish `hpos' : 0 < ν K` using `Measure.measure_pos_of_mem_nhds ν hK`. Establish `hfin : ν K < ⊤` using `hKc.measure_lt_top`. Establish `hint : IntegrableOn G K ν` using `(hG.mono hKW).integrableOn_compact hKc`. Establish `hle : ∫ b in K, G b0 / 2 ∂ν ≤ ∫ b in K, G b ∂ν` using `setIntegral_mono_on (integrableOn_const hfin.ne) hint hKc.measurableSet (fun b hb => (hKN hb).1.le)`.

Rewrite `hle` using `[h0G K hKc hKW, setIntegral_const, smul_eq_mul]`. Establish `hr : 0 < ν.real K`. Rewrite using `[Measure.real]`. Conclude with `ENNReal.toReal_pos hpos'.ne' hfin.ne`. Use the polynomial consequences of the given equalities and inequalities.

Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with hneg | hpos` into its components or cases. Apply `claim (fun b => -D b) hD.neg (fun S hS hSW => by rw [integral_neg, h0 S hS hSW, neg_zero]) show 0 < -D b0` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `claim D hD h0 hpos`.
-/
theorem eq_zero_of_setIntegral [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℝ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  have claim : ∀ G : X → ℝ, ContinuousOn G W →
      (∀ S, IsCompact S → S ⊆ W → ∫ b in S, G b ∂ν = 0) → ¬ (0 < G b0) := by
    intro G hG h0G hpos
    have hcont : ContinuousAt G b0 := (hG b0 (mem_of_mem_nhds hW)).continuousAt hW
    have hev : ∀ᶠ b in 𝓝 b0, G b0 / 2 < G b := hcont.eventually (lt_mem_nhds (half_lt_self hpos))
    obtain ⟨K, hK, hKN, hKc⟩ := local_compact_nhds (inter_mem hev hW)
    have hKW : K ⊆ W := hKN.trans inter_subset_right
    have hpos' : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
    have hfin : ν K < ⊤ := hKc.measure_lt_top
    have hint : IntegrableOn G K ν := (hG.mono hKW).integrableOn_compact hKc
    have hle : ∫ b in K, G b0 / 2 ∂ν ≤ ∫ b in K, G b ∂ν :=
      setIntegral_mono_on (integrableOn_const hfin.ne) hint hKc.measurableSet
        (fun b hb => (hKN hb).1.le)
    rw [h0G K hKc hKW, setIntegral_const, smul_eq_mul] at hle
    have hr : 0 < ν.real K := by
      rw [Measure.real]
      exact ENNReal.toReal_pos hpos'.ne' hfin.ne
    nlinarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · apply claim (fun b => -D b) hD.neg (fun S hS hSW => by rw [integral_neg, h0 S hS hSW, neg_zero])
    show 0 < -D b0
    linarith
  · exact claim D hD h0 hpos

end PI.AprimeInfW.DG

namespace PI.AprimeInfW.DiscreteGroups

open MeasureTheory Topology Set Filter
open scoped ENNReal

section

variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]

/- English proof (translation)
Use `haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace`. Set `E` to `CompactExhaustion.choice U`. Establish `h : ∀ n, ∃ W, IsOpen W ∧ Subtype.val '' E n ⊆ W ∧ closure W ⊆ U ∧ IsCompact (closure W)` using `fun n => exists_open_between_and_isCompact_closure ((E.isCompact n).image continuous_subtype_val) hU (by rintro _ ⟨u, -, rfl⟩; exact u.2)`. Use `choose W hW1 hW2 hW3 hW4 using h`. Use `⟨W, fun n => ⟨hW1 n, hW4 n, hW3 n⟩, subset_antisymm (iUnion_subset fun n => subset_closure.trans (hW3 n)) ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Take `⟨n, hn⟩` from `E.exists_mem ⟨x, hx⟩`. Conclude with `mem_iUnion.2 ⟨n, hW2 n ⟨_, hn, rfl⟩⟩`.
-/
theorem cover (U : Set V) (hU : IsOpen U) : ∃ W : ℕ → Set V,
    (∀ n, IsOpen (W n) ∧ IsCompact (closure (W n)) ∧ closure (W n) ⊆ U) ∧ ⋃ n, W n = U := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let E := CompactExhaustion.choice U
  have h : ∀ n, ∃ W, IsOpen W ∧ Subtype.val '' E n ⊆ W ∧ closure W ⊆ U ∧ IsCompact (closure W) :=
    fun n => exists_open_between_and_isCompact_closure ((E.isCompact n).image continuous_subtype_val)
      hU (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  choose W hW1 hW2 hW3 hW4 using h
  refine ⟨W, fun n => ⟨hW1 n, hW4 n, hW3 n⟩,
    subset_antisymm (iUnion_subset fun n => subset_closure.trans (hW3 n)) ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
  exact mem_iUnion.2 ⟨n, hW2 n ⟨_, hn, rfl⟩⟩

/- English proof (translation)
Use `haveI : LocallyCompactSpace O := hO.isOpenEmbedding_subtypeVal.locallyCompactSpace`. Set `E` to `CompactExhaustion.choice O`. Establish `h : ∀ k, ∃ g : C(V, ℝ), EqOn g 1 (Subtype.val '' E k) ∧ IsCompact (tsupport g) ∧ tsupport g ⊆ Subtype.val '' interior (E (k + 1)) ∧ ∀ x, g x ∈ Icc (0 : ℝ) 1` using `fun k => exists_continuousMap_one_of_isCompact_subset_isOpen ((E.isCompact k).image continuous_subtype_val) (hO.isOpenMap_subtype_val _ isOpen_interior) (image_mono (E.subset_interior_succ k))`. Use `choose g hg1 hgc hgs hg01 using h`. Establish `hsubO : ∀ k, tsupport (g k) ⊆ O` using `fun k => (hgs k).trans (by rintro _ ⟨u, -, rfl⟩; exact u.2)`.

Establish `hmono : ∀ x, Monotone fun k => g k x`. Introduce `x`. Use `monotone_nat_of_le_succ fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ tsupport (g k)`. Take `⟨u, hu, rfl⟩` from `hgs k hx`.

Rewrite using `[hg1 (k + 1) ⟨u, interior_subset hu, rfl⟩]`. Conclude with `(hg01 k _).2`. Rewrite using `[image_eq_zero_of_notMem_tsupport hx]`. Conclude with `(hg01 (k + 1) x).1`. Use `⟨fun k => g k, fun k => ⟨(g k).continuous, hgc k, hsubO k⟩, fun k x => hg01 k x, hmono, fun x => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hx : x ∈ O`. Take `⟨n, hn⟩` from `E.exists_mem ⟨x, hx⟩`. Rewrite using `[indicator_of_mem hx]`. Apply `le_antisymm` to reduce the goal to its premises. Use `iSup_le fun k => ?_` and prove the remaining obligations.

Use `ENNReal.ofReal_le_ofReal (hg01 k x).2` as an intermediate fact. Simplify using `using this`. Use `le_iSup_of_le n ?_` and prove the remaining obligations. Establish `h1 : g n x = 1` using `hg1 n ⟨⟨x, hx⟩, hn, rfl⟩`. Use `show (1 : V → ℝ≥0∞) x ≤ ENNReal.ofReal (g n x)`.

Rewrite using `[h1]`. Simplify using the standard rewrite rules. Rewrite using `[indicator_of_notMem hx]`. Simplify using `[image_eq_zero_of_notMem_tsupport (fun h => hx (hsubO _ h))]`.
-/
theorem approx (O : Set V) (hO : IsOpen O) : ∃ φ : ℕ → V → ℝ,
    (∀ k, Continuous (φ k) ∧ HasCompactSupport (φ k) ∧ tsupport (φ k) ⊆ O) ∧
    (∀ k x, 0 ≤ φ k x ∧ φ k x ≤ 1) ∧ (∀ x, Monotone fun k => φ k x) ∧
    ∀ x, ⨆ k, ENNReal.ofReal (φ k x) = O.indicator 1 x := by
  haveI : LocallyCompactSpace O := hO.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let E := CompactExhaustion.choice O
  have h : ∀ k, ∃ g : C(V, ℝ), EqOn g 1 (Subtype.val '' E k) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ Subtype.val '' interior (E (k + 1)) ∧ ∀ x, g x ∈ Icc (0 : ℝ) 1 := fun k =>
    exists_continuousMap_one_of_isCompact_subset_isOpen ((E.isCompact k).image continuous_subtype_val)
      (hO.isOpenMap_subtype_val _ isOpen_interior) (image_mono (E.subset_interior_succ k))
  choose g hg1 hgc hgs hg01 using h
  have hsubO : ∀ k, tsupport (g k) ⊆ O :=
    fun k => (hgs k).trans (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  have hmono : ∀ x, Monotone fun k => g k x := by
    intro x
    refine monotone_nat_of_le_succ fun k => ?_
    by_cases hx : x ∈ tsupport (g k)
    · obtain ⟨u, hu, rfl⟩ := hgs k hx
      rw [hg1 (k + 1) ⟨u, interior_subset hu, rfl⟩]
      exact (hg01 k _).2
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact (hg01 (k + 1) x).1
  refine ⟨fun k => g k, fun k => ⟨(g k).continuous, hgc k, hsubO k⟩, fun k x => hg01 k x, hmono,
    fun x => ?_⟩
  by_cases hx : x ∈ O
  · obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
    rw [indicator_of_mem hx]
    apply le_antisymm
    · refine iSup_le fun k => ?_
      have := ENNReal.ofReal_le_ofReal (hg01 k x).2
      simpa using this
    · refine le_iSup_of_le n ?_
      have h1 : g n x = 1 := hg1 n ⟨⟨x, hx⟩, hn, rfl⟩
      show (1 : V → ℝ≥0∞) x ≤ ENNReal.ofReal (g n x)
      rw [h1]
      simp
  · rw [indicator_of_notMem hx]
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hsubO _ h))]

end

end PI.AprimeInfW.DiscreteGroups

namespace PI.AprimeInfW.FU

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib1 fib2 : X → Measure V}

/- English proof (translation)
Establish `c1` using `(h1.2.2 φ hφc hφs hφU).2`. Establish `c2` using `(h2.2.2 φ hφc hφs hφU).2`. Establish `h0 : ∀ S, IsCompact S → S ⊆ univ → ∫ b in S, (∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) ∂ν = 0`. Introduce `S hS _`. Rewrite using `[integral_sub ((c1.mono (subset_univ S)).integrableOn_compact hS) ((c2.mono (subset_univ S)).integrableOn_compact hS), ← PI.AprimeInfW.DG.fib_set h1 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S), ← PI.AprimeInfW.DG.fib_set h2 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S), sub_s …`.

Conclude with `sub_eq_zero.1 (PI.AprimeInfW.DG.eq_zero_of_setIntegral (ν := ν) (fun b => ∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) univ b univ_mem (c1.sub c2) h0)`.
-/
theorem integral_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (φ : V → ℝ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (b : X) :
    ∫ v, φ v ∂(fib1 b) = ∫ v, φ v ∂(fib2 b) := by
  have c1 := (h1.2.2 φ hφc hφs hφU).2
  have c2 := (h2.2.2 φ hφc hφs hφU).2
  have h0 : ∀ S, IsCompact S → S ⊆ univ →
      ∫ b in S, (∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) ∂ν = 0 := by
    intro S hS _
    rw [integral_sub ((c1.mono (subset_univ S)).integrableOn_compact hS)
      ((c2.mono (subset_univ S)).integrableOn_compact hS),
      ← PI.AprimeInfW.DG.fib_set h1 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S),
      ← PI.AprimeInfW.DG.fib_set h2 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S), sub_self]
  exact sub_eq_zero.1 (PI.AprimeInfW.DG.eq_zero_of_setIntegral (ν := ν)
    (fun b => ∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) univ b univ_mem (c1.sub c2) h0)

/- English proof (translation)
Take `⟨g, hg1, hgc, hgs, _⟩` from `exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU`. Establish `hI` using `(h.2.2 g g.continuous hgc hgs).1 b (mem_univ b)`. Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `hv : v ∈ K`. Simplify using `[indicator_of_mem hv, hg1 hv]`.

Simplify using `[indicator_of_notMem hv]`. Use `_ < ⊤ := hI.lintegral_lt_top`.
-/
theorem fin_cpt {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) (K : Set V) (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨g, hg1, hgc, hgs, _⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hI := (h.2.2 g g.continuous hgc hgs).1 b (mem_univ b)
  calc fib b K = ∫⁻ v, K.indicator 1 v ∂(fib b) := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂(fib b) := lintegral_mono fun v => by
        by_cases hv : v ∈ K
        · simp [indicator_of_mem hv, hg1 hv]
        · simp [indicator_of_notMem hv]
    _ < ⊤ := hI.lintegral_lt_top

/- English proof (translation)
Take `⟨φ, hφ, h01, hmono, hlim⟩` from `PI.AprimeInfW.DiscreteGroups.approx O hO`. Establish `hmeas : ∀ k, Measurable fun v => ENNReal.ofReal (φ k v)` using `fun k => ENNReal.measurable_ofReal.comp (hφ k).1.measurable`. Establish `hmon : Monotone fun k v => ENNReal.ofReal (φ k v)` using `fun i j hij v => ENNReal.ofReal_le_ofReal (hmono v hij)`. Establish `key : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → fib b O = ⨆ k, ENNReal.ofReal (∫ v, φ k v ∂(fib b))`. Introduce `fib hf`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `(ofReal_integral_eq_lintegral_ofReal ((hf.2.2 _ (hφ k).1 (hφ k).2.1 ((hφ k).2.2.trans hOU)).1 b (mem_univ b)) (ae_of_all _ fun v => (h01 k v).1)).symm`. Rewrite using `[key fib1 h1, key fib2 h2]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[integral_eq h1 h2 hf' hff' hι (φ k) (hφ k).1 (hφ k).2.1 ((hφ k).2.2.trans hOU) b]`.
-/
theorem open_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (O : Set V) (hO : IsOpen O)
    (hOU : O ⊆ U) (b : X) : fib1 b O = fib2 b O := by
  obtain ⟨φ, hφ, h01, hmono, hlim⟩ := PI.AprimeInfW.DiscreteGroups.approx O hO
  have hmeas : ∀ k, Measurable fun v => ENNReal.ofReal (φ k v) :=
    fun k => ENNReal.measurable_ofReal.comp (hφ k).1.measurable
  have hmon : Monotone fun k v => ENNReal.ofReal (φ k v) :=
    fun i j hij v => ENNReal.ofReal_le_ofReal (hmono v hij)
  have key : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib →
      fib b O = ⨆ k, ENNReal.ofReal (∫ v, φ k v ∂(fib b)) := by
    intro fib hf
    calc fib b O = ∫⁻ v, O.indicator 1 v ∂(fib b) :=
          (lintegral_indicator_one hO.measurableSet).symm
      _ = ∫⁻ v, ⨆ k, ENNReal.ofReal (φ k v) ∂(fib b) := lintegral_congr fun v => (hlim v).symm
      _ = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := lintegral_iSup hmeas hmon
      _ = ⨆ k, ENNReal.ofReal (∫ v, φ k v ∂(fib b)) := by
          congr 1
          funext k
          exact (ofReal_integral_eq_lintegral_ofReal
            ((hf.2.2 _ (hφ k).1 (hφ k).2.1 ((hφ k).2.2.trans hOU)).1 b (mem_univ b))
            (ae_of_all _ fun v => (h01 k v).1)).symm
  rw [key fib1 h1, key fib2 h2]
  congr 1
  funext k
  rw [integral_eq h1 h2 hf' hff' hι (φ k) (hφ k).1 (hφ k).2.1 ((hφ k).2.2.trans hOU) b]

/- English proof (translation)
Use function extensionality and compare the values at `b`. Take `⟨W, hW, hWU⟩` from `PI.AprimeInfW.DiscreteGroups.cover U hU`. Establish `hWsub : ∀ n, W n ⊆ U` using `fun n => subset_closure.trans (hW n).2.2`. Establish `hnull : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → fib b Uᶜ = 0` using `fun fib hf => measure_mono_null (compl_subset_compl.2 inter_subset_right) (hf.1 b)`. Establish `hfin : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → ∀ n, fib b (W n) ≠ ⊤` using `fun fib hf n => (lt_of_le_of_lt (measure_mono subset_closure) (fin_cpt hf hU b _ (hW n).2.1 (hW n).2.2)).ne`.

Set `s : Option ℕ → Set V` to `fun o => o.elim Uᶜ W`. Establish `hs : ⋃ o, s o = univ`. Rewrite using `[iUnion_option]`. Simplify using `only [s, Option.elim_none, Option.elim_some]`. Rewrite using `[hWU, compl_union_self]`.

Use `(Measure.ext_iff_of_iUnion_eq_univ hs).2 fun o => ?_` and prove the remaining obligations. Consider the cases of `o with`. Consider the case `none`. Simplify using `only [s, Option.elim_none]`. Rewrite using `[Measure.restrict_eq_zero.2 (hnull fib1 h1), Measure.restrict_eq_zero.2 (hnull fib2 h2)]`.

Consider the case `some n`. Simplify using `only [s, Option.elim_some]`. Establish `: IsFiniteMeasure ((fib1 b).restrict (W n))` using `isFiniteMeasure_restrict.2 (hfin fib1 h1 n)`. Use `ext_of_generate_finite {t : Set V | IsOpen t} (BorelSpace.measurable_eq.trans rfl) isPiSystem_isOpen (fun t ht => ?_) ?_` and prove the remaining obligations. Rewrite using `[Measure.restrict_apply ht.measurableSet, Measure.restrict_apply ht.measurableSet]`.

Conclude with `open_eq h1 h2 hf' hff' hι _ (ht.inter (hW n).1) (inter_subset_right.trans (hWsub n)) b`. Rewrite using `[Measure.restrict_apply_univ, Measure.restrict_apply_univ]`. Conclude with `open_eq h1 h2 hf' hff' hι _ (hW n).1 (hWsub n) b`.
-/
theorem fib_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hU : IsOpen U) : fib1 = fib2 := by
  funext b
  obtain ⟨W, hW, hWU⟩ := PI.AprimeInfW.DiscreteGroups.cover U hU
  have hWsub : ∀ n, W n ⊆ U := fun n => subset_closure.trans (hW n).2.2
  have hnull : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → fib b Uᶜ = 0 :=
    fun fib hf => measure_mono_null (compl_subset_compl.2 inter_subset_right) (hf.1 b)
  have hfin : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → ∀ n, fib b (W n) ≠ ⊤ :=
    fun fib hf n => (lt_of_le_of_lt (measure_mono subset_closure)
      (fin_cpt hf hU b _ (hW n).2.1 (hW n).2.2)).ne
  let s : Option ℕ → Set V := fun o => o.elim Uᶜ W
  have hs : ⋃ o, s o = univ := by
    rw [iUnion_option]
    simp only [s, Option.elim_none, Option.elim_some]
    rw [hWU, compl_union_self]
  refine (Measure.ext_iff_of_iUnion_eq_univ hs).2 fun o => ?_
  cases o with
  | none =>
    simp only [s, Option.elim_none]
    rw [Measure.restrict_eq_zero.2 (hnull fib1 h1), Measure.restrict_eq_zero.2 (hnull fib2 h2)]
  | some n =>
    simp only [s, Option.elim_some]
    have : IsFiniteMeasure ((fib1 b).restrict (W n)) :=
      isFiniteMeasure_restrict.2 (hfin fib1 h1 n)
    refine ext_of_generate_finite {t : Set V | IsOpen t} (BorelSpace.measurable_eq.trans rfl)
      isPiSystem_isOpen (fun t ht => ?_) ?_
    · rw [Measure.restrict_apply ht.measurableSet, Measure.restrict_apply ht.measurableSet]
      exact open_eq h1 h2 hf' hff' hι _ (ht.inter (hW n).1) (inter_subset_right.trans (hWsub n)) b
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      exact open_eq h1 h2 hf' hff' hι _ (hW n).1 (hWsub n) b

end Gen

end PI.AprimeInfW.FU
