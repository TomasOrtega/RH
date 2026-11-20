import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarMeasureNonunitsNull
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsFibreFamilyLength

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `h`. Establish `hT : MeasurableSet (A ∩ q ⁻¹' S)` using `hA.inter (hq hS)`. Establish `e` using `h2 ((A ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator hT)`. Simplify using `only [Measure.restrict_univ, lintegral_indicator_one hT] at e`. Rewrite using `[e, ← lintegral_indicator hS]`.

Use `lintegral_congr fun b => ?_` and prove the remaining obligations. Establish `hae : ∀ᵐ x ∂(fib b), q x = b`. Use `measure_mono_null ?_ (h1 b)` and prove the remaining obligations. Introduce `x hx hx'`. Conclude with `hx hx'.1`.

Distinguish the cases in `hb : b ∈ S`. Rewrite using `[Set.indicator_of_mem hb]`. Use `measure_congr ?_` and prove the remaining obligations. Use `filter_upwards [hae] with x hx`. Use `propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩` and prove the remaining obligations.

Use `show q x ∈ S`. Rewrite using `[hx]` and apply the resulting hypothesis. Rewrite using `[Set.indicator_of_notMem hb]`. Use `measure_mono_null (t := {x | ¬ q x = b}) ?_ hae` and prove the remaining obligations. Introduce `x hx hxb`.

Apply `hb` to reduce the goal to its premises. Rewrite using `[← hxb]`. Conclude with `hx.2`.
-/
theorem fibre_mass_eq {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace R] [MeasurableSpace R]
    (μ : Measure V) (ν : Measure R) (q : V → R) (hq : Measurable q) (B : Set R) (fib : R → Measure V)
    (h : IsFibreFamily μ q id Set.univ ν B fib) {A : Set V} {S : Set R} (hA : MeasurableSet A)
    (hS : MeasurableSet S) : μ (A ∩ q ⁻¹' S) = ∫⁻ s in S, fib s A ∂ν := by
  obtain ⟨h1, h2, -⟩ := h
  have hT : MeasurableSet (A ∩ q ⁻¹' S) := hA.inter (hq hS)
  have e := h2 ((A ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator hT)
  simp only [Measure.restrict_univ, lintegral_indicator_one hT] at e
  rw [e, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae : ∀ᵐ x ∂(fib b), q x = b := by
    refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx hx'.1
  by_cases hb : b ∈ S
  · rw [Set.indicator_of_mem hb]
    refine measure_congr ?_
    filter_upwards [hae] with x hx
    refine propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show q x ∈ S
    rwa [hx]
  · rw [Set.indicator_of_notMem hb]
    refine measure_mono_null (t := {x | ¬ q x = b}) ?_ hae
    intro x hx hxb
    apply hb
    rw [← hxb]
    exact hx.2

/- English proof (translation)
Rewrite using `[Metric.tendsto_nhds]`. Introduce `ε hε`. Establish `hN : {s | G s ≠ ⊤ ∧ dist (G s).toReal (G c).toReal < ε / 2} ∈ nhds c` using `Filter.inter_mem hfin (hG.eventually (Metric.ball_mem_nhds _ (half_pos hε)))`. Establish `hev` using `hl.eventually (Filter.eventually_smallSets_subset.2 hN)`. Use `filter_upwards [hev] with k hk`.

Use `set g := (G c).toReal with hg`. Establish `hg0 : 0 ≤ g` using `ENNReal.toReal_nonneg`. Use `set n := ν (S k) with hn`. Establish `hnr : 0 < n.toReal` using `ENNReal.toReal_pos (hpos k) (htop k)`. Establish `hup : ∫⁻ s in S k, G s ∂ν ≤ ENNReal.ofReal (g + ε / 2) * n`.

Rewrite using `[hn, ← setLIntegral_const]`. Use `setLIntegral_mono' (hS k) fun s hs => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hk hs`. Rewrite using `[← ENNReal.ofReal_toReal h1]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Use `(abs_lt.1 (Real.dist_eq _ _ ▸ h2)).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlo : ENNReal.ofReal (g - ε / 2) * n ≤ ∫⁻ s in S k, G s ∂ν`. Rewrite using `[hn, ← setLIntegral_const]`. Use `setLIntegral_mono' (hS k) fun s hs => ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `hk hs`. Rewrite using `[← ENNReal.ofReal_toReal h1]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Use `(abs_lt.1 (Real.dist_eq _ _ ▸ h2)).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hfinU : ENNReal.ofReal (g + ε / 2) * n ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htop k)`. Establish `hup' : (∫⁻ s in S k, G s ∂ν).toReal ≤ (g + ε / 2) * n.toReal`. Use `ENNReal.toReal_mono hfinU hup` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]`. Then use the resulting hypothesis. Establish `hlo' : (g - ε / 2) * n.toReal ≤ (∫⁻ s in S k, G s ∂ν).toReal`.

Use `ENNReal.toReal_mono (ne_top_of_le_ne_top hfinU hup) hlo` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_mul]`. Use `le_trans ?_ this` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_right ?_ hnr.le` and prove the remaining obligations. Rewrite using `[ENNReal.toReal_ofReal']`.

Conclude with `le_max_left _ _`. Rewrite using `[Real.dist_eq, abs_lt]`. Prove the components needed by the constructor for the conclusion. Establish `: g - ε / 2 ≤ (∫⁻ s in S k, G s ∂ν).toReal / n.toReal` using `(le_div_iff₀ hnr).2 hlo'`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: (∫⁻ s in S k, G s ∂ν).toReal / n.toReal ≤ g + ε / 2` using `(div_le_iff₀ hnr).2 hup'`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tendsto_mean {R : Type} [TopologicalSpace R] [MeasurableSpace R] (ν : Measure R) (G : R → ℝ≥0∞) (c : R)
    (hG : ContinuousAt (fun s => (G s).toReal) c) (hfin : ∀ᶠ s in nhds c, G s ≠ ⊤) (S : ℕ → Set R)
    (hS : ∀ k, MeasurableSet (S k)) (hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets)
    (hpos : ∀ k, ν (S k) ≠ 0) (htop : ∀ k, ν (S k) ≠ ⊤) :
    Filter.Tendsto (fun k => (∫⁻ s in S k, G s ∂ν).toReal / (ν (S k)).toReal) Filter.atTop
      (nhds (G c).toReal) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hN : {s | G s ≠ ⊤ ∧ dist (G s).toReal (G c).toReal < ε / 2} ∈ nhds c :=
    Filter.inter_mem hfin (hG.eventually (Metric.ball_mem_nhds _ (half_pos hε)))
  have hev := hl.eventually (Filter.eventually_smallSets_subset.2 hN)
  filter_upwards [hev] with k hk
  set g := (G c).toReal with hg
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  set n := ν (S k) with hn
  have hnr : 0 < n.toReal := ENNReal.toReal_pos (hpos k) (htop k)
  have hup : ∫⁻ s in S k, G s ∂ν ≤ ENNReal.ofReal (g + ε / 2) * n := by
    rw [hn, ← setLIntegral_const]
    refine setLIntegral_mono' (hS k) fun s hs => ?_
    obtain ⟨h1, h2⟩ := hk hs
    rw [← ENNReal.ofReal_toReal h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_lt.1 (Real.dist_eq _ _ ▸ h2)).2
    linarith
  have hlo : ENNReal.ofReal (g - ε / 2) * n ≤ ∫⁻ s in S k, G s ∂ν := by
    rw [hn, ← setLIntegral_const]
    refine setLIntegral_mono' (hS k) fun s hs => ?_
    obtain ⟨h1, h2⟩ := hk hs
    rw [← ENNReal.ofReal_toReal h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_lt.1 (Real.dist_eq _ _ ▸ h2)).1
    linarith
  have hfinU : ENNReal.ofReal (g + ε / 2) * n ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htop k)
  have hup' : (∫⁻ s in S k, G s ∂ν).toReal ≤ (g + ε / 2) * n.toReal := by
    have := ENNReal.toReal_mono hfinU hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hlo' : (g - ε / 2) * n.toReal ≤ (∫⁻ s in S k, G s ∂ν).toReal := by
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hfinU hup) hlo
    rw [ENNReal.toReal_mul] at this
    refine le_trans ?_ this
    refine mul_le_mul_of_nonneg_right ?_ hnr.le
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : g - ε / 2 ≤ (∫⁻ s in S k, G s ∂ν).toReal / n.toReal := (le_div_iff₀ hnr).2 hlo'
    linarith
  · have : (∫⁻ s in S k, G s ∂ν).toReal / n.toReal ≤ g + ε / 2 := (div_le_iff₀ hnr).2 hup'
    linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ hM d b v lv hlv mv hmv c hc A hAc hAo U hU hUt`. Take `⟨r1, r2, r3, r4, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI := r1`. Use `haveI := r2`. Use `haveI := r3`.

Use `haveI := r4`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Take `⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)`. Use `haveI := a1`. Use `haveI := a2`.

Use `haveI := a3`. Use `haveI := a4`. Use `haveI := a8 1 M`. Use `haveI := hlv.1`. Take `⟨-, hW, -⟩` from `GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1`.

Use `haveI := hW 1 M`. Take `⟨n1, n2⟩` from `GlobalTheory.CompanionTheory.SW.NullV.null_nonunits F E σ hσ M J hJ (by omega) v (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M) lv (hW 1 M) hlv.1`. Establish `hmv' : GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J 1 (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M) (lv.map (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ)) mv`. Rewrite using `[(GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hσ (Fv F v) d b).2.2 lv hlv.1]`. Conclude with `hmv`.

Establish `FF` using `GlobalTheory.CompanionTheory.SW.isFibreFamily_length F E σ hσ M J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) _ lv (hW 1 M) hlv.1 n1 n2 mv hmv'`. Establish `hqc : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => qR (Fv F v) σ J (X 0)` using `GlobalTheory.CompanionTheory.SW.LenFib.continuous_qR (Fv F v) hσ J`. Establish `hAm : MeasurableSet A` using `hAo.measurableSet`. Establish `hAcl : IsClosed A` using `hAc.isClosed`. Set `S : ℕ → Set (Fv F v)` to `fun k => {s | c - s ∈ U k}`.

Establish `hSo : ∀ k, IsOpen (S k)` using `fun k => (hU k).2.1.preimage (continuous_const.sub continuous_id)`. Establish `hSm : ∀ k, MeasurableSet (S k)` using `fun k => (hSo k).measurableSet`. Establish `hSc : ∀ k, c ∈ S k` using `fun k => by show c - c ∈ U k`. Rewrite using `[sub_self]`. Conclude with `(hU k).2.2`.

Use `haveI : lv.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular lv`. Establish `hSU : ∀ k, lv (S k) = lv (U k)` using `fun k => (Measure.measurePreserving_sub_left lv c).measure_preimage (hU k).2.1.measurableSet.nullMeasurableSet`. Establish `hpos : ∀ k, lv (S k) ≠ 0` using `fun k => (hSo k).measure_ne_zero lv ⟨c, hSc k⟩`. Establish `htop : ∀ k, lv (S k) ≠ ⊤` using `fun k => by`. Rewrite using `[hSU]`.

Conclude with `(hU k).1.measure_lt_top.ne`. Establish `hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets`. Rewrite using `[Filter.tendsto_smallSets_iff]`. Introduce `t ht`. Establish `hcont : Filter.Tendsto (fun u : Fv F v => c - u) (nhds 0) (nhds c)`.

Establish `: Continuous fun u : Fv F v => c - u` using `continuous_const.sub continuous_id`. Simplify using `using this.tendsto 0`. Establish `h0` using `(Filter.tendsto_smallSets_iff.1 hUt) _ (hcont ht)`. Use `filter_upwards [h0] with k hk s hs`. Use `hk hs` as an intermediate fact.

Simplify using `using this`. Set `φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ` to `A.indicator fun _ => 1`. Establish `hφc : Continuous φ`. Use `continuous_indicator ?_ continuous_const.continuousOn` and prove the remaining obligations. Simplify using `[hAo.frontier_eq, hAcl.closure_eq]`.

Establish `hφs : HasCompactSupport φ`. Use `HasCompactSupport.intro hAc fun x hx => ?_` and prove the remaining obligations. Conclude with `Set.indicator_of_notMem hx _`. Take `⟨hI, hC⟩` from `FF.2.2 φ hφc hφs (Set.subset_univ _)`. Establish `hint : ∀ s, ∫ X, φ X ∂(mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s)) = (mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A).toReal` using `fun s => by`.

Simplify using `[φ, integral_indicator hAm, Measure.real]`. Establish `hUn : {s : Fv F v | IsUnit s} ∈ nhds c`. Establish `: {s : Fv F v | IsUnit s} = {0}ᶜ`. Use extensionality with `s`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `isOpen_compl_singleton.mem_nhds hc`. Establish `hG : ContinuousAt (fun s => (mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A).toReal) c`. Establish `h` using `hC.continuousAt (x := c) hUn`. Simplify `h` using `only [hint]`.

Establish `hfin : ∀ᶠ s in nhds c, mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A ≠ ⊤` using `by filter_upwards [hUn] with s hs`. Establish `h` using `hI s hs`. Rewrite `h` using `[integrable_indicator_iff hAm]`. Break down `(integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h` into its components or cases. Simplify using `at h`.

Conclude with `h.ne`. Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Establish `hO : IsOpen (A ∩ {X | c - qR (Fv F v) σ J (X 0) ∈ U k})` using `hAo.inter ((hU k).2.1.preimage (continuous_const.sub hqc))`. Conclude with `⟨hO.measurableSet, ne_top_of_le_ne_top hAc.measure_lt_top.ne (measure_mono Set.inter_subset_left)⟩`. Establish `key` using `tendsto_mean lv (fun s => mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A) c hG hfin S hSm hl hpos htop`.

Use `key.congr fun k => ?_` and prove the remaining obligations. Rewrite using `[hSU k, ← fibre_mass_eq _ lv _ hqc.measurable _ _ FF hAm (hSm k)]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.CompanionTheory.Hypotheses₂.OneV.avgV_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 2 < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J 1 (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv 1) mv → ∀ c : Fv F v, c ≠ 0 → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ U : ℕ → Set (Fv F v), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : Fv F v) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : Fv F v)).smallSets → (∀ k, MeasurableSet (A ∩ {X | c - qR (Fv F v) σ J (X 0) ∈ U k}) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M (A ∩ {X | c - qR (Fv F v) σ J (X 0) ∈ U k}) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M (A ∩ {X | c - qR (Fv F v) σ J (X 0) ∈ U k})).toReal / (lv (U k)).toReal) Filter.atTop (nhds (mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ c) A).toReal) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b v lv hlv mv hmv c hc A hAc hAo U hU hUt
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  haveI := hlv.1
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW 1 M
  obtain ⟨n1, n2⟩ := GlobalTheory.CompanionTheory.SW.NullV.null_nonunits F E σ hσ M J hJ (by omega) v
    (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M) lv (hW 1 M) hlv.1
  have hmv' : GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J 1 (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M)
      (lv.map (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ)) mv := by
    rw [(GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hσ (Fv F v) d b).2.2 lv hlv.1]
    exact hmv
  have FF := GlobalTheory.CompanionTheory.SW.isFibreFamily_length F E σ hσ M J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) _ lv
    (hW 1 M) hlv.1 n1 n2 mv hmv'
  have hqc : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => qR (Fv F v) σ J (X 0) :=
    GlobalTheory.CompanionTheory.SW.LenFib.continuous_qR (Fv F v) hσ J
  have hAm : MeasurableSet A := hAo.measurableSet
  have hAcl : IsClosed A := hAc.isClosed

  let S : ℕ → Set (Fv F v) := fun k => {s | c - s ∈ U k}
  have hSo : ∀ k, IsOpen (S k) := fun k => (hU k).2.1.preimage (continuous_const.sub continuous_id)
  have hSm : ∀ k, MeasurableSet (S k) := fun k => (hSo k).measurableSet
  have hSc : ∀ k, c ∈ S k := fun k => by
    show c - c ∈ U k
    rw [sub_self]
    exact (hU k).2.2
  haveI : lv.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular lv
  have hSU : ∀ k, lv (S k) = lv (U k) := fun k =>
    (Measure.measurePreserving_sub_left lv c).measure_preimage (hU k).2.1.measurableSet.nullMeasurableSet
  have hpos : ∀ k, lv (S k) ≠ 0 := fun k => (hSo k).measure_ne_zero lv ⟨c, hSc k⟩
  have htop : ∀ k, lv (S k) ≠ ⊤ := fun k => by
    rw [hSU]
    exact (hU k).1.measure_lt_top.ne
  have hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have hcont : Filter.Tendsto (fun u : Fv F v => c - u) (nhds 0) (nhds c) := by
      have : Continuous fun u : Fv F v => c - u := continuous_const.sub continuous_id
      simpa using this.tendsto 0
    have h0 := (Filter.tendsto_smallSets_iff.1 hUt) _ (hcont ht)
    filter_upwards [h0] with k hk s hs
    have := hk hs
    simpa using this

  let φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ := A.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hAo.frontier_eq, hAcl.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hAc fun x hx => ?_
    exact Set.indicator_of_notMem hx _
  obtain ⟨hI, hC⟩ := FF.2.2 φ hφc hφs (Set.subset_univ _)
  have hint : ∀ s, ∫ X, φ X ∂(mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s)) =
      (mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A).toReal := fun s => by
    simp [φ, integral_indicator hAm, Measure.real]
  have hUn : {s : Fv F v | IsUnit s} ∈ nhds c := by
    have : {s : Fv F v | IsUnit s} = {0}ᶜ := by
      ext s
      simp
    rw [this]
    exact isOpen_compl_singleton.mem_nhds hc
  have hG : ContinuousAt (fun s => (mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A).toReal) c := by
    have h := hC.continuousAt (x := c) hUn
    simpa only [hint] using h
  have hfin : ∀ᶠ s in nhds c, mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A ≠ ⊤ := by
    filter_upwards [hUn] with s hs
    have h := hI s hs
    rw [integrable_indicator_iff hAm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  refine ⟨fun k => ?_, ?_⟩
  · have hO : IsOpen (A ∩ {X | c - qR (Fv F v) σ J (X 0) ∈ U k}) :=
      hAo.inter ((hU k).2.1.preimage (continuous_const.sub hqc))
    exact ⟨hO.measurableSet, ne_top_of_le_ne_top hAc.measure_lt_top.ne (measure_mono Set.inter_subset_left)⟩
  · have key := tendsto_mean lv (fun s => mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A) c hG hfin S hSm hl hpos htop
    refine key.congr fun k => ?_
    rw [hSU k, ← fibre_mass_eq _ lv _ hqc.measurable _ _ FF hAm (hSm k)]
    rfl
