import Mathlib
import Formalism.PeriodIntegrals.VolFromSW

noncomputable section

namespace PI.VolStabSW.DensGen

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}

/- English proof (translation)
Establish `h` using `hfib.1 b`. Rewrite using `[ae_iff]`. Use `measure_mono_null ?_ h` and prove the remaining obligations. Introduce `v hv hmem`. Conclude with `hv (hι (by rw [← hff' v]; exact hmem.1))`.
-/
theorem ae_fib (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (b : X) :
    ∀ᵐ v ∂(fib b), f' v = b := by
  have h := hfib.1 b
  rw [ae_iff]
  refine measure_mono_null ?_ h
  intro v hv hmem
  exact hv (hι (by rw [← hff' v]; exact hmem.1))

/- English proof (translation)
Take `⟨hint, hGc⟩` from `hfib.2.2 ρ hρc hρs hρU`. Establish `hSm : MeasurableSet S` using `hS.isClosed.measurableSet`. Establish `hS'm : MeasurableSet (f' ⁻¹' S)` using `(hS.isClosed.preimage hf').measurableSet`. Establish `hρm : Measurable fun v => ENNReal.ofReal (ρ v)` using `hρc.measurable.ennreal_ofReal`. Establish `hmain : ∫⁻ v in f' ⁻¹' S, ENNReal.ofReal (ρ v) ∂μ = ∫⁻ b in S, ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b) ∂ν`.

Establish `key` using `hfib.2.1 ((f' ⁻¹' S).indicator fun v => ENNReal.ofReal (ρ v)) (hρm.indicator hS'm)`. Establish `hsupp : Function.support ((f' ⁻¹' S).indicator fun v => ENNReal.ofReal (ρ v)) ⊆ U`. Introduce `v hv`. Apply `hρU` to reduce the goal to its premises. Apply `subset_tsupport` to reduce the goal to its premises.

Introduce `h0`. Apply `hv` to reduce the goal to its premises. Simplify using `[Set.indicator, h0]`. Rewrite `key` using `[setLIntegral_eq_of_support_subset hsupp, lintegral_indicator hS'm]`. Rewrite using `[key, ← lintegral_indicator hSm]`.

Apply `lintegral_congr` to reduce the goal to its premises. Introduce `b`. Establish `hae` using `ae_fib hfib hff' hι b`. Distinguish the cases in `hb : b ∈ S`. Rewrite using `[Set.indicator_apply, if_pos hb]`.

Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with v hv`. Establish `hv' : v ∈ f' ⁻¹' S` using `by show f' v ∈ S`. Rewrite using `[hv]`. Conclude with `hb`.

Rewrite using `[Set.indicator_apply, if_pos hv']`. Rewrite using `[Set.indicator_apply, if_neg hb]`. Use `(lintegral_congr_ae ?_).trans lintegral_zero` and prove the remaining obligations. Use `filter_upwards [hae] with v hv`. Establish `hv' : v ∉ f' ⁻¹' S` using `by show f' v ∉ S`.

Rewrite using `[hv]`. Conclude with `hb`. Rewrite using `[Set.indicator_apply, if_neg hv']`. Establish `hG0 : ∀ b, 0 ≤ ∫ v, ρ v ∂(fib b)` using `fun b => integral_nonneg hρ0`. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hρ0) hρc.aestronglyMeasurable, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0) ((hGc.mono hSB).aestronglyMeasurable hSm), hmain]`.

Use `congr 1`. Use `lintegral_congr_ae ((ae_restrict_iff' hSm).mpr (Filter.Eventually.of_forall fun b hb => ?_))` and prove the remaining obligations. Conclude with `(ofReal_integral_eq_lintegral_ofReal (hint b (hSB hb)) (Filter.Eventually.of_forall hρ0)).symm`.
-/
theorem fib_set_nonneg [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hρ0 : ∀ v, 0 ≤ ρ v) (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  classical
  obtain ⟨hint, hGc⟩ := hfib.2.2 ρ hρc hρs hρU
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hS'm : MeasurableSet (f' ⁻¹' S) := (hS.isClosed.preimage hf').measurableSet
  have hρm : Measurable fun v => ENNReal.ofReal (ρ v) := hρc.measurable.ennreal_ofReal
  have hmain : ∫⁻ v in f' ⁻¹' S, ENNReal.ofReal (ρ v) ∂μ =
      ∫⁻ b in S, ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b) ∂ν := by
    have key := hfib.2.1 ((f' ⁻¹' S).indicator fun v => ENNReal.ofReal (ρ v)) (hρm.indicator hS'm)
    have hsupp : Function.support ((f' ⁻¹' S).indicator fun v => ENNReal.ofReal (ρ v)) ⊆ U := by
      intro v hv
      apply hρU
      apply subset_tsupport
      intro h0
      apply hv
      simp [Set.indicator, h0]
    rw [setLIntegral_eq_of_support_subset hsupp, lintegral_indicator hS'm] at key
    rw [key, ← lintegral_indicator hSm]
    apply lintegral_congr
    intro b
    have hae := ae_fib hfib hff' hι b
    by_cases hb : b ∈ S
    · rw [Set.indicator_apply, if_pos hb]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with v hv
      have hv' : v ∈ f' ⁻¹' S := by
        show f' v ∈ S
        rw [hv]
        exact hb
      rw [Set.indicator_apply, if_pos hv']
    · rw [Set.indicator_apply, if_neg hb]
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [hae] with v hv
      have hv' : v ∉ f' ⁻¹' S := by
        show f' v ∉ S
        rw [hv]
        exact hb
      rw [Set.indicator_apply, if_neg hv']
  have hG0 : ∀ b, 0 ≤ ∫ v, ρ v ∂(fib b) := fun b => integral_nonneg hρ0
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hρ0) hρc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0)
      ((hGc.mono hSB).aestronglyMeasurable hSm), hmain]
  congr 1
  refine lintegral_congr_ae ((ae_restrict_iff' hSm).mpr (Filter.Eventually.of_forall fun b hb => ?_))
  exact (ofReal_integral_eq_lintegral_ofReal (hint b (hSB hb)) (Filter.Eventually.of_forall hρ0)).symm

/- English proof (translation)
Use `set ρp : V → ℝ := fun v => max (ρ v) 0 with hρpdef`. Use `set ρn : V → ℝ := fun v => max (-ρ v) 0 with hρndef`. Establish `hρeq : ρ = fun v => ρp v - ρn v`. Use function extensionality and compare the values at `fun v => (max_zero_sub_max_neg_zero_eq_self (ρ v)).symm`. Establish `hcp : Continuous ρp` using `hρc.max continuous_const`.

Establish `hcn : Continuous ρn` using `hρc.neg.max continuous_const`. Establish `hsp : HasCompactSupport ρp` using `hρs.comp_left (g := fun x : ℝ => max x 0) (by simp)`. Establish `hsn : HasCompactSupport ρn` using `hρs.neg.comp_left (g := fun x : ℝ => max x 0) (by simp)`. Establish `hup : tsupport ρp ⊆ U` using `(tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) ρ).trans hρU`. Establish `hun : tsupport ρn ⊆ U`.

Use `(tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) (-ρ)).trans ?_` and prove the remaining obligations. Rewrite using `[tsupport_neg]`. Conclude with `hρU`. Establish `hp` using `fib_set_nonneg hfib hf' hff' hι ρp hcp hsp hup (fun v => le_max_right _ _) S hS hSB`. Establish `hn` using `fib_set_nonneg hfib hf' hff' hι ρn hcn hsn hun (fun v => le_max_right _ _) S hS hSB`.

Establish `hip : Integrable ρp μ` using `hcp.integrable_of_hasCompactSupport hsp`. Establish `hin : Integrable ρn μ` using `hcn.integrable_of_hasCompactSupport hsn`. Take `⟨hintp, hGp⟩` from `hfib.2.2 ρp hcp hsp hup`. Take `⟨hintn, hGn⟩` from `hfib.2.2 ρn hcn hsn hun`. Establish `hSm : MeasurableSet S` using `hS.isClosed.measurableSet`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hρeq]`. Conclude with `integral_sub hip.integrableOn hin.integrableOn`. Use `_ = ∫ b in S, (∫ v, ρp v ∂(fib b)) ∂ν - ∫ b in S, (∫ v, ρn v ∂(fib b)) ∂ν := by rw [hp, hn]`. Use `_ = ∫ b in S, ((∫ v, ρp v ∂(fib b)) - ∫ v, ρn v ∂(fib b)) ∂ν := (integral_sub ((hGp.mono hSB).integrableOn_compact hS) ((hGn.mono hSB).integrableOn_compact hS)).symm`.

Use `_ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by`. Use `setIntegral_congr_fun hSm (fun b hb => ?_)` and prove the remaining obligations. Rewrite using `[hρeq]`. Conclude with `(integral_sub (hintp b (hSB hb)) (hintn b (hSB hb))).symm`.
-/
theorem fib_set [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  set ρp : V → ℝ := fun v => max (ρ v) 0 with hρpdef
  set ρn : V → ℝ := fun v => max (-ρ v) 0 with hρndef
  have hρeq : ρ = fun v => ρp v - ρn v :=
    funext fun v => (max_zero_sub_max_neg_zero_eq_self (ρ v)).symm
  have hcp : Continuous ρp := hρc.max continuous_const
  have hcn : Continuous ρn := hρc.neg.max continuous_const
  have hsp : HasCompactSupport ρp := hρs.comp_left (g := fun x : ℝ => max x 0) (by simp)
  have hsn : HasCompactSupport ρn := hρs.neg.comp_left (g := fun x : ℝ => max x 0) (by simp)
  have hup : tsupport ρp ⊆ U := (tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) ρ).trans hρU
  have hun : tsupport ρn ⊆ U := by
    refine (tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) (-ρ)).trans ?_
    rw [tsupport_neg]
    exact hρU
  have hp := fib_set_nonneg hfib hf' hff' hι ρp hcp hsp hup (fun v => le_max_right _ _) S hS hSB
  have hn := fib_set_nonneg hfib hf' hff' hι ρn hcn hsn hun (fun v => le_max_right _ _) S hS hSB
  have hip : Integrable ρp μ := hcp.integrable_of_hasCompactSupport hsp
  have hin : Integrable ρn μ := hcn.integrable_of_hasCompactSupport hsn
  obtain ⟨hintp, hGp⟩ := hfib.2.2 ρp hcp hsp hup
  obtain ⟨hintn, hGn⟩ := hfib.2.2 ρn hcn hsn hun
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  calc ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ v in f' ⁻¹' S, ρp v ∂μ - ∫ v in f' ⁻¹' S, ρn v ∂μ := by
        rw [hρeq]
        exact integral_sub hip.integrableOn hin.integrableOn
    _ = ∫ b in S, (∫ v, ρp v ∂(fib b)) ∂ν - ∫ b in S, (∫ v, ρn v ∂(fib b)) ∂ν := by rw [hp, hn]
    _ = ∫ b in S, ((∫ v, ρp v ∂(fib b)) - ∫ v, ρn v ∂(fib b)) ∂ν :=
        (integral_sub ((hGp.mono hSB).integrableOn_compact hS)
          ((hGn.mono hSB).integrableOn_compact hS)).symm
    _ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
        refine setIntegral_congr_fun hSm (fun b hb => ?_)
        rw [hρeq]
        exact (integral_sub (hintp b (hSB hb)) (hintn b (hSB hb))).symm

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < D b0 * D b0` using `mul_self_pos.mpr hne`. Establish `hcont : ContinuousAt (fun b => D b0 * D b) b0` using `continuousAt_const.mul (hD.continuousAt hW)`. Establish `hev : ∀ᶠ b in 𝓝 b0, D b0 * D b0 / 2 < D b0 * D b` using `hcont.eventually (lt_mem_nhds (by linarith))`. Take `⟨K, hK, hKsub, hKc⟩` from `local_compact_nhds (Filter.inter_mem hW hev)`.

Establish `hKW : K ⊆ W` using `fun x hx => (hKsub hx).1`. Establish `h0K` using `h0 K hKc hKW`. Establish `hKpos : 0 < ν K` using `Measure.measure_pos_of_mem_nhds ν hK`. Establish `hKfin : ν K < ⊤` using `hKc.measure_lt_top`. Establish `hint : IntegrableOn D K ν` using `(hD.mono hKW).integrableOn_compact hKc`.

Establish `hle : ∫ b in K, D b0 * D b0 / 2 ∂ν ≤ ∫ b in K, D b0 * D b ∂ν` using `setIntegral_mono_on (integrableOn_const hKfin.ne) (hint.const_mul (D b0)) hKc.isClosed.measurableSet (fun b hb => le_of_lt (hKsub hb).2)`. Rewrite `hle` using `[integral_const_mul, h0K, mul_zero, setIntegral_const, smul_eq_mul]`. Establish `hr : 0 < ν.real K` using `ENNReal.toReal_pos hKpos.ne' hKfin.ne`. Establish `: 0 < ν.real K * (D b0 * D b0 / 2)` using `mul_pos hr (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zero_of_setIntegral [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℝ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  by_contra hne
  have hpos : 0 < D b0 * D b0 := mul_self_pos.mpr hne
  have hcont : ContinuousAt (fun b => D b0 * D b) b0 :=
    continuousAt_const.mul (hD.continuousAt hW)
  have hev : ∀ᶠ b in 𝓝 b0, D b0 * D b0 / 2 < D b0 * D b :=
    hcont.eventually (lt_mem_nhds (by linarith))
  obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hW hev)
  have hKW : K ⊆ W := fun x hx => (hKsub hx).1
  have h0K := h0 K hKc hKW
  have hKpos : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
  have hKfin : ν K < ⊤ := hKc.measure_lt_top
  have hint : IntegrableOn D K ν := (hD.mono hKW).integrableOn_compact hKc
  have hle : ∫ b in K, D b0 * D b0 / 2 ∂ν ≤ ∫ b in K, D b0 * D b ∂ν :=
    setIntegral_mono_on (integrableOn_const hKfin.ne) (hint.const_mul (D b0))
      hKc.isClosed.measurableSet (fun b hb => le_of_lt (hKsub hb).2)
  rw [integral_const_mul, h0K, mul_zero, setIntegral_const, smul_eq_mul] at hle
  have hr : 0 < ν.real K := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  have : 0 < ν.real K * (D b0 * D b0 / 2) := mul_pos hr (by linarith)
  linarith

/- English proof (translation)
Establish `hre : (D b0).re = 0`. Use `eq_zero_of_setIntegral (ν := ν) (fun b => (D b).re) W b0 hW (Complex.continuous_re.comp_continuousOn hD) (fun S hS hSW => ?_)` and prove the remaining obligations. Establish `hint : IntegrableOn D S ν` using `(hD.mono hSW).integrableOn_compact hS`. Establish `h1` using `integral_re hint`. Simplify using `only [RCLike.re_to_complex] at h1`.

Rewrite using `[h1, h0 S hS hSW, Complex.zero_re]`. Establish `him : (D b0).im = 0`. Use `eq_zero_of_setIntegral (ν := ν) (fun b => (D b).im) W b0 hW (Complex.continuous_im.comp_continuousOn hD) (fun S hS hSW => ?_)` and prove the remaining obligations. Establish `hint : IntegrableOn D S ν` using `(hD.mono hSW).integrableOn_compact hS`. Establish `h1` using `integral_im hint`.

Simplify using `only [RCLike.im_to_complex] at h1`. Rewrite using `[h1, h0 S hS hSW, Complex.zero_im]`. Conclude with `Complex.ext hre him`.
-/
theorem eq_zero_of_setIntegral_c [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℂ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  have hre : (D b0).re = 0 := by
    refine eq_zero_of_setIntegral (ν := ν) (fun b => (D b).re) W b0 hW
      (Complex.continuous_re.comp_continuousOn hD) (fun S hS hSW => ?_)
    have hint : IntegrableOn D S ν := (hD.mono hSW).integrableOn_compact hS
    have h1 := integral_re hint
    simp only [RCLike.re_to_complex] at h1
    rw [h1, h0 S hS hSW, Complex.zero_re]
  have him : (D b0).im = 0 := by
    refine eq_zero_of_setIntegral (ν := ν) (fun b => (D b).im) W b0 hW
      (Complex.continuous_im.comp_continuousOn hD) (fun S hS hSW => ?_)
    have hint : IntegrableOn D S ν := (hD.mono hSW).integrableOn_compact hS
    have h1 := integral_im hint
    simp only [RCLike.im_to_complex] at h1
    rw [h1, h0 S hS hSW, Complex.zero_im]
  exact Complex.ext hre him

/- English proof (translation)
Use `⟨hq.mul (hψ.comp hf'), hqs.mul_right, ?_⟩` and prove the remaining obligations. Establish `h1 : tsupport (fun v => q v * ψ (f' v)) ⊆ tsupport (fun v => ψ (f' v))` using `tsupport_mul_subset_right`. Establish `h2 : tsupport (fun v => ψ (f' v)) ⊆ f' ⁻¹' C`. Apply `closure_minimal _ (hC.preimage hf')` to reduce the goal to its premises. Introduce `v hv`.

Conclude with `hψC (f' v) hv`. Conclude with `fun v hv => hCU v (h2 (h1 hv))`.
-/
theorem cut_props {f' : V → X} (hf' : Continuous f') (q : V → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (ψ : X → ℝ) (hψ : Continuous ψ) (C : Set X) (hC : IsClosed C)
    (hψC : ∀ x, ψ x ≠ 0 → x ∈ C) (hCU : ∀ v, f' v ∈ C → v ∈ U) :
    Continuous (fun v => q v * ψ (f' v)) ∧ HasCompactSupport (fun v => q v * ψ (f' v)) ∧
      tsupport (fun v => q v * ψ (f' v)) ⊆ U := by
  refine ⟨hq.mul (hψ.comp hf'), hqs.mul_right, ?_⟩
  have h1 : tsupport (fun v => q v * ψ (f' v)) ⊆ tsupport (fun v => ψ (f' v)) :=
    tsupport_mul_subset_right
  have h2 : tsupport (fun v => ψ (f' v)) ⊆ f' ⁻¹' C := by
    apply closure_minimal _ (hC.preimage hf')
    intro v hv
    exact hψC (f' v) hv
  exact fun v hv => hCU v (h2 (h1 hv))

/- English proof (translation)
Take `⟨M, hM, hMN, hMc⟩` from `local_compact_nhds hN`. Take `⟨K, hK, hKM, hKc⟩` from `local_compact_nhds (interior_mem_nhds.mpr hM)`. Take `⟨ψ, hψ1, hψ0, -, -⟩` from `exists_continuous_one_zero_of_isCompact hKc isOpen_interior.isClosed_compl (Set.disjoint_compl_right_iff_subset.mpr hKM)`. Establish `hψC : ∀ x, ψ x ≠ 0 → x ∈ M`. Introduce `x hx`.

Assume the negation of the conclusion as `hxM`. Conclude with `hx (hψ0 (fun hxi => hxM (interior_subset hxi)))`. Establish `hCU : ∀ v, f' v ∈ M → v ∈ U` using `fun v hv => hNU v (hMN hv)`. Take `⟨hcr, hsr, hur⟩` from `cut_props hf' (fun v => (Φ v).re) (Complex.continuous_re.comp hΦc) (hΦs.comp_left Complex.zero_re) ψ ψ.continuous M hMc.isClosed hψC hCU`. Take `⟨hci, hsi, hui⟩` from `cut_props hf' (fun v => (Φ v).im) (Complex.continuous_im.comp hΦc) (hΦs.comp_left Complex.zero_im) ψ ψ.continuous M hMc.isClosed hψC hCU`.

Take `⟨hintr, hGr⟩` from `hfib.2.2 _ hcr hsr hur`. Take `⟨hinti, hGi⟩` from `hfib.2.2 _ hci hsi hui`. Establish `hre : ∀ v, (Φ v * (ψ (f' v) : ℂ)).re = (Φ v).re * ψ (f' v)` using `fun v => by simp`. Establish `him : ∀ v, (Φ v * (ψ (f' v) : ℂ)).im = (Φ v).im * ψ (f' v)` using `fun v => by simp`. Establish `hintc : ∀ b ∈ B, Integrable (fun v => Φ v * (ψ (f' v) : ℂ)) (fib b)`.

Introduce `b hb`. Use `Integrable.re_im_iff.mp ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(hintr b hb).congr (Filter.Eventually.of_forall fun v => by`. Simplify using `only [RCLike.re_to_complex, hre])`. Conclude with `(hinti b hb).congr (Filter.Eventually.of_forall fun v => by`.

Simplify using `only [RCLike.im_to_complex, him])`. Establish `hHeq : ∀ b ∈ B, (∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) = ((∫ v, (Φ v).re * ψ (f' v) ∂(fib b) : ℝ) : ℂ) + ((∫ v, (Φ v).im * ψ (f' v) ∂(fib b) : ℝ) : ℂ) * Complex.I`. Introduce `b hb`. Apply `Complex.ext` to reduce the goal to its premises. Establish `h1` using `integral_re (hintc b hb)`.

Simplify using `only [RCLike.re_to_complex, hre] at h1`. Simplify using `[← h1]`. Establish `h1` using `integral_im (hintc b hb)`. Simplify using `only [RCLike.im_to_complex, him] at h1`. Simplify using `[← h1]`.

Establish `hHc : ContinuousOn (fun b => ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) B`. Use `ContinuousOn.congr (f := fun b => ((∫ v, (Φ v).re * ψ (f' v) ∂(fib b) : ℝ) : ℂ) + ((∫ v, (Φ v).im * ψ (f' v) ∂(fib b) : ℝ) : ℂ) * Complex.I) ?_ (fun b hb => hHeq b hb)` and prove the remaining obligations. Conclude with `(Complex.continuous_ofReal.comp_continuousOn hGr).add ((Complex.continuous_ofReal.comp_continuousOn hGi).mul continuousOn_const)`. Establish `hΦint : Integrable (fun v => Φ v * (ψ (f' v) : ℂ)) μ` using `(hΦc.mul (Complex.continuous_ofReal.comp (ψ.continuous.comp hf'))).integrable_of_hasCompactSupport hΦs.mul_right`. Establish `hW : B ∩ B' ∩ K ∈ 𝓝 b0` using `Filter.inter_mem (Filter.inter_mem hB hB') hK`.

Establish `hDc : ContinuousOn (fun b => g b - ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) (B ∩ B' ∩ K)` using `(hg.1.mono fun x hx => hx.1.2).sub (hHc.mono fun x hx => hx.1.1)`. Establish `h0 : ∀ S, IsCompact S → S ⊆ B ∩ B' ∩ K → ∫ b in S, (g b - ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) ∂ν = 0`. Introduce `S hS hSW`. Establish `hSB : S ⊆ B` using `fun x hx => (hSW hx).1.1`. Establish `hSB' : S ⊆ B'` using `fun x hx => (hSW hx).1.2`.

Establish `hSK : S ⊆ K` using `fun x hx => (hSW hx).2`. Establish `hSm : MeasurableSet S` using `hS.isClosed.measurableSet`. Establish `hS'm : MeasurableSet (f' ⁻¹' S)` using `(hS.isClosed.preimage hf').measurableSet`. Establish `hpre : f ⁻¹' (ι '' S) = f' ⁻¹' S`. Use extensionality with `v`.

Simplify using `only [Set.mem_preimage, Set.mem_image, hff' v]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, hbv⟩`. Rewrite `hb` using `[hι hbv]`. Conclude with `hb`.

Introduce `hv`. Conclude with `⟨f' v, hv, rfl⟩`. Establish `hgS` using `hg.2 S hS hSB'`. Rewrite `hgS` using `[hpre]`. Establish `hcut : ∫ v in f' ⁻¹' S, Φ v ∂μ = ∫ v in f' ⁻¹' S, Φ v * (ψ (f' v) : ℂ) ∂μ`.

Use `setIntegral_congr_fun hS'm (fun v hv => ?_)` and prove the remaining obligations. Simplify using `only [hψ1 (hSK hv), Pi.one_apply, Complex.ofReal_one, mul_one]`. Establish `hr` using `fib_set hfib hf' hff' hι _ hcr hsr hur S hS hSB`. Establish `hi` using `fib_set hfib hf' hff' hι _ hci hsi hui S hS hSB`. Establish `hintS : IntegrableOn (fun b => ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) S ν` using `(hHc.mono hSB).integrableOn_compact hS`.

Establish `hfib_eq : ∫ v in f' ⁻¹' S, Φ v * (ψ (f' v) : ℂ) ∂μ = ∫ b in S, (∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) ∂ν`. Apply `Complex.ext` to reduce the goal to its premises. Establish `h1` using `integral_re (hΦint.integrableOn (s := f' ⁻¹' S))`. Establish `h2` using `integral_re hintS`. Simplify using `only [RCLike.re_to_complex] at h1 h2`.

Rewrite using `[← h1, ← h2]`. Simplify using `only [hre]`. Rewrite using `[hr]`. Use `setIntegral_congr_fun hSm (fun b hb => ?_)` and prove the remaining obligations. Establish `h3` using `integral_re (hintc b (hSB hb))`.

Simplify using `only [RCLike.re_to_complex, hre] at h3`. Conclude with `h3`. Establish `h1` using `integral_im (hΦint.integrableOn (s := f' ⁻¹' S))`. Establish `h2` using `integral_im hintS`. Simplify using `only [RCLike.im_to_complex] at h1 h2`.

Rewrite using `[← h1, ← h2]`. Simplify using `only [him]`. Rewrite using `[hi]`. Use `setIntegral_congr_fun hSm (fun b hb => ?_)` and prove the remaining obligations. Establish `h3` using `integral_im (hintc b (hSB hb))`.

Simplify using `only [RCLike.im_to_complex, him] at h3`. Conclude with `h3`. Rewrite using `[integral_sub ((hg.1.mono hSB').integrableOn_compact hS) hintS, ← hgS, hcut, hfib_eq, sub_self]`. Establish `hD0` using `eq_zero_of_setIntegral_c (ν := ν) (fun b => g b - ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) (B ∩ B' ∩ K) b0 hW hDc h0`. Establish `hb0K : b0 ∈ K` using `mem_of_mem_nhds hK`.

Establish `hfin : ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b0) = ∫ v, Φ v ∂(fib b0)`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_fib hfib hff' hι b0] with v hv`. Simplify using `only [hv, hψ1 hb0K, Pi.one_apply, Complex.ofReal_one, mul_one]`. Rewrite using `[← hfin]`.

Conclude with `sub_eq_zero.mp hD0`.
-/
theorem densGen [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts μ] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {B' N : Set X} (hfib : IsFibreFamily μ f ι U ν B fib)
    {f' : V → X} (hf' : Continuous f') (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (hNU : ∀ v, f' v ∈ N → v ∈ U)
    {Φ : V → ℂ} (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ) {g : X → ℂ}
    (hg : IsContDensityOn μ f ι ν B' Φ g) {b0 : X} (hB : B ∈ 𝓝 b0) (hB' : B' ∈ 𝓝 b0)
    (hN : N ∈ 𝓝 b0) :
    g b0 = ∫ v, Φ v ∂(fib b0) := by
  classical
  obtain ⟨M, hM, hMN, hMc⟩ := local_compact_nhds hN
  obtain ⟨K, hK, hKM, hKc⟩ := local_compact_nhds (interior_mem_nhds.mpr hM)
  obtain ⟨ψ, hψ1, hψ0, -, -⟩ := exists_continuous_one_zero_of_isCompact hKc
    isOpen_interior.isClosed_compl (Set.disjoint_compl_right_iff_subset.mpr hKM)
  have hψC : ∀ x, ψ x ≠ 0 → x ∈ M := by
    intro x hx
    by_contra hxM
    exact hx (hψ0 (fun hxi => hxM (interior_subset hxi)))
  have hCU : ∀ v, f' v ∈ M → v ∈ U := fun v hv => hNU v (hMN hv)
  obtain ⟨hcr, hsr, hur⟩ := cut_props hf' (fun v => (Φ v).re) (Complex.continuous_re.comp hΦc)
    (hΦs.comp_left Complex.zero_re) ψ ψ.continuous M hMc.isClosed hψC hCU
  obtain ⟨hci, hsi, hui⟩ := cut_props hf' (fun v => (Φ v).im) (Complex.continuous_im.comp hΦc)
    (hΦs.comp_left Complex.zero_im) ψ ψ.continuous M hMc.isClosed hψC hCU
  obtain ⟨hintr, hGr⟩ := hfib.2.2 _ hcr hsr hur
  obtain ⟨hinti, hGi⟩ := hfib.2.2 _ hci hsi hui
  have hre : ∀ v, (Φ v * (ψ (f' v) : ℂ)).re = (Φ v).re * ψ (f' v) := fun v => by simp
  have him : ∀ v, (Φ v * (ψ (f' v) : ℂ)).im = (Φ v).im * ψ (f' v) := fun v => by simp
  have hintc : ∀ b ∈ B, Integrable (fun v => Φ v * (ψ (f' v) : ℂ)) (fib b) := by
    intro b hb
    refine Integrable.re_im_iff.mp ⟨?_, ?_⟩
    · exact (hintr b hb).congr (Filter.Eventually.of_forall fun v => by
        simp only [RCLike.re_to_complex, hre])
    · exact (hinti b hb).congr (Filter.Eventually.of_forall fun v => by
        simp only [RCLike.im_to_complex, him])
  have hHeq : ∀ b ∈ B, (∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) =
      ((∫ v, (Φ v).re * ψ (f' v) ∂(fib b) : ℝ) : ℂ) +
        ((∫ v, (Φ v).im * ψ (f' v) ∂(fib b) : ℝ) : ℂ) * Complex.I := by
    intro b hb
    apply Complex.ext
    · have h1 := integral_re (hintc b hb)
      simp only [RCLike.re_to_complex, hre] at h1
      simp [← h1]
    · have h1 := integral_im (hintc b hb)
      simp only [RCLike.im_to_complex, him] at h1
      simp [← h1]
  have hHc : ContinuousOn (fun b => ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) B := by
    refine ContinuousOn.congr (f := fun b => ((∫ v, (Φ v).re * ψ (f' v) ∂(fib b) : ℝ) : ℂ) +
      ((∫ v, (Φ v).im * ψ (f' v) ∂(fib b) : ℝ) : ℂ) * Complex.I) ?_ (fun b hb => hHeq b hb)
    exact (Complex.continuous_ofReal.comp_continuousOn hGr).add
      ((Complex.continuous_ofReal.comp_continuousOn hGi).mul continuousOn_const)
  have hΦint : Integrable (fun v => Φ v * (ψ (f' v) : ℂ)) μ :=
    (hΦc.mul (Complex.continuous_ofReal.comp (ψ.continuous.comp hf'))).integrable_of_hasCompactSupport
      hΦs.mul_right
  have hW : B ∩ B' ∩ K ∈ 𝓝 b0 := Filter.inter_mem (Filter.inter_mem hB hB') hK
  have hDc : ContinuousOn (fun b => g b - ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) (B ∩ B' ∩ K) :=
    (hg.1.mono fun x hx => hx.1.2).sub (hHc.mono fun x hx => hx.1.1)
  have h0 : ∀ S, IsCompact S → S ⊆ B ∩ B' ∩ K →
      ∫ b in S, (g b - ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) ∂ν = 0 := by
    intro S hS hSW
    have hSB : S ⊆ B := fun x hx => (hSW hx).1.1
    have hSB' : S ⊆ B' := fun x hx => (hSW hx).1.2
    have hSK : S ⊆ K := fun x hx => (hSW hx).2
    have hSm : MeasurableSet S := hS.isClosed.measurableSet
    have hS'm : MeasurableSet (f' ⁻¹' S) := (hS.isClosed.preimage hf').measurableSet
    have hpre : f ⁻¹' (ι '' S) = f' ⁻¹' S := by
      ext v
      simp only [Set.mem_preimage, Set.mem_image, hff' v]
      constructor
      · rintro ⟨b, hb, hbv⟩
        rw [hι hbv] at hb
        exact hb
      · intro hv
        exact ⟨f' v, hv, rfl⟩
    have hgS := hg.2 S hS hSB'
    rw [hpre] at hgS
    have hcut : ∫ v in f' ⁻¹' S, Φ v ∂μ = ∫ v in f' ⁻¹' S, Φ v * (ψ (f' v) : ℂ) ∂μ := by
      refine setIntegral_congr_fun hS'm (fun v hv => ?_)
      simp only [hψ1 (hSK hv), Pi.one_apply, Complex.ofReal_one, mul_one]
    have hr := fib_set hfib hf' hff' hι _ hcr hsr hur S hS hSB
    have hi := fib_set hfib hf' hff' hι _ hci hsi hui S hS hSB
    have hintS : IntegrableOn (fun b => ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) S ν :=
      (hHc.mono hSB).integrableOn_compact hS
    have hfib_eq : ∫ v in f' ⁻¹' S, Φ v * (ψ (f' v) : ℂ) ∂μ =
        ∫ b in S, (∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) ∂ν := by
      apply Complex.ext
      · have h1 := integral_re (hΦint.integrableOn (s := f' ⁻¹' S))
        have h2 := integral_re hintS
        simp only [RCLike.re_to_complex] at h1 h2
        rw [← h1, ← h2]
        simp only [hre]
        rw [hr]
        refine setIntegral_congr_fun hSm (fun b hb => ?_)
        have h3 := integral_re (hintc b (hSB hb))
        simp only [RCLike.re_to_complex, hre] at h3
        exact h3
      · have h1 := integral_im (hΦint.integrableOn (s := f' ⁻¹' S))
        have h2 := integral_im hintS
        simp only [RCLike.im_to_complex] at h1 h2
        rw [← h1, ← h2]
        simp only [him]
        rw [hi]
        refine setIntegral_congr_fun hSm (fun b hb => ?_)
        have h3 := integral_im (hintc b (hSB hb))
        simp only [RCLike.im_to_complex, him] at h3
        exact h3
    rw [integral_sub ((hg.1.mono hSB').integrableOn_compact hS) hintS, ← hgS, hcut, hfib_eq, sub_self]
  have hD0 := eq_zero_of_setIntegral_c (ν := ν)
    (fun b => g b - ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) (B ∩ B' ∩ K) b0 hW hDc h0
  have hb0K : b0 ∈ K := mem_of_mem_nhds hK
  have hfin : ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b0) = ∫ v, Φ v ∂(fib b0) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_fib hfib hff' hι b0] with v hv
    simp only [hv, hψ1 hb0K, Pi.one_apply, Complex.ofReal_one, mul_one]
  rw [← hfin]
  exact sub_eq_zero.mp hD0

end PI.VolStabSW.DensGen
