import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualMeasurePi
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx

/- English proof (translation)
Introduce `hreal F _ _ hF ψ hψ laminf hH`. Use `haveI := hF`. Take `⟨h1, h2, h3, h4, -⟩` from `GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Establish `he : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F)` using `(GlobalTheory.CompanionTheory.SW.RealCoord.isHomeomorph_coord F).continuous`.

Establish `he' : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F).symm` using `(GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F).symm.continuous`. Establish `hpc : Continuous (psiInf F ψ)` using `hψ.1.comp (continuous_id.prodMk continuous_const)`. Take `⟨a, ha, hχ⟩` from `GlobalTheory.CompanionTheory.SW.SdPi.exists_form (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) he' (psiInf F ψ) hpc (fun _ => hψ.2.1 _) (fun u v => by`. Simplify using `only [psiInf, map_add, ← AddChar.map_add_eq_mul]`. Use `congr 1`.

Conclude with `Prod.ext rfl (add_zero _).symm)`. Use the proof step `(GlobalTheory.T.localComponents_nontrivial_adelic_character F ψ hψ).2.2`. Take `⟨g, hg1, hg2, hg3⟩` from `hreal (InfinitePlace F) a ha`. Use `set e := GlobalTheory.CompanionTheory.SW.RealCoord.coord F with hedef`. Use `set E := GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F with hEdef`.

Establish `hEe : ∀ y, E y = e y` using `fun _ => rfl`. Use `haveI : (laminf.map e).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map laminf e.toAddEquiv he he'`. Take `⟨c, hc⟩ : ∃ c : ℝ≥0, laminf.map e = c • (volume : Measure (InfinitePlace F → ℝ))` from `⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`.

Establish `h0 : laminf.map e = 0` using `by simpa using hc`. Conclude with `(Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := laminf.map e)).open_pos Set.univ isOpen_univ Set.univ_nonempty (by simp [h0])`. Establish `hme : MeasurableEmbedding e` using `E.measurableEmbedding`. Establish `hint : ∀ f : (InfinitePlace F → ℝ) → ℂ, ∫ y, f (e y) ∂laminf = (c : ℝ) • ∫ u, f u`. Introduce `f`.

Rewrite using `[← hme.integral_map (μ := laminf) f, hc, integral_smul_nnreal_measure]`. Both sides reduce to the same expression. Establish `hintR : ∀ f : (InfinitePlace F → ℝ) → ℝ, ∫ y, f (e y) ∂laminf = (c : ℝ) * ∫ u, f u`. Introduce `f`. Rewrite using `[← hme.integral_map (μ := laminf) f, hc, integral_smul_nnreal_measure]`.

Both sides reduce to the same expression. Use `⟨fun k y => g k (e y), fun k => ⟨(hg1 k).1.comp he, (hg1 k).2.1.comp_homeomorph E, fun y => (hg1 k).2.2.1 _, ?_⟩, ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[hintR]`. Establish `: (0 : ℝ) < c` using `by exact_mod_cast pos_iff_ne_zero.2 hc0`. Conclude with `mul_pos this (hg1 k).2.2.2`.

Rewrite using `[Filter.tendsto_smallSets_iff]`. Introduce `U hU`. Establish `hV : E.symm ⁻¹' U ∈ nhds (0 : InfinitePlace F → ℝ)`. Apply `E.symm.continuous.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Establish `: E.symm 0 = 0` using `e.symm.map_zero`.

Rewrite using `[this]` and apply the resulting hypothesis. Take `⟨ε, hε, hεV⟩` from `Metric.nhds_basis_closedBall.mem_iff.1 hV`. Establish `hlim : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0)` using `tendsto_one_div_add_atTop_nhds_zero_nat`. Use `filter_upwards [hlim.eventually (ge_mem_nhds hε)] with k hk y hy`. Establish `h1 : e y ∈ tsupport (g k)` using `tsupport_comp_subset_preimage (g k) he hy`.

Establish `h3 : e y ∈ E.symm ⁻¹' U` using `hεV (Metric.closedBall_subset_closedBall hk (hg2 k h1))`. Establish `h5 : E.symm (e y) = y` using `E.symm_apply_apply y`. Rewrite `h3` using `[Set.mem_preimage, h5]`. Conclude with `h3`. Establish `hfou : ∀ t, fouInf ψ laminf (fun y => g k (e y)) t = (c : ℝ) • ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * e t w) : ℝ) : ℂ))`.

Introduce `t`. Establish `h6` using `hint (fun u => (g k u : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (u w * e t w) : ℝ) : ℂ)))`. Rewrite using `[← h6, fouInf]`. Simplify using `only [hχ, map_mul, Pi.mul_apply]`. Establish `hG : Integrable (fun t => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * e t w) : ℝ) : ℂ))) laminf`.

Establish `h7 : Integrable (fun t : InfinitePlace F → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ))) (laminf.map e)`. Rewrite using `[hc]`. Conclude with `(hg3 k).smul_measure_nnreal`. Conclude with `hme.integrable_map_iff.1 h7`. Rewrite using `[funext hfou]`.

Conclude with `hG.smul (c : ℝ)`.
-/
theorem exists_bumps_inf : (∀ (P : Type) [Fintype P] (a : P → ℝ), (∀ w, a w ≠ 0) → ∃ g : ℕ → (P → ℝ) → ℝ, (∀ k, Continuous (g k) ∧ HasCompactSupport (g k) ∧ (∀ x, 0 ≤ g k x) ∧ 0 < ∫ x, g k x) ∧ (∀ k, tsupport (g k) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))) ∧ ∀ k, Integrable (fun t : P → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ)))) → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∃ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧ ∀ k, Integrable (fouInf ψ laminf (ρ k)) laminf := by
  intro hreal F _ _ hF ψ hψ laminf hH
  haveI := hF
  classical
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have he : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) := (GlobalTheory.CompanionTheory.SW.RealCoord.isHomeomorph_coord F).continuous
  have he' : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F).symm := (GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F).symm.continuous
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨a, ha, hχ⟩ := GlobalTheory.CompanionTheory.SW.SdPi.exists_form (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) he' (psiInf F ψ) hpc (fun _ => hψ.2.1 _)
    (fun u v => by
      simp only [psiInf, map_add, ← AddChar.map_add_eq_mul]
      congr 1
      exact Prod.ext rfl (add_zero _).symm)
    (GlobalTheory.T.localComponents_nontrivial_adelic_character F ψ hψ).2.2
  obtain ⟨g, hg1, hg2, hg3⟩ := hreal (InfinitePlace F) a ha
  set e := GlobalTheory.CompanionTheory.SW.RealCoord.coord F with hedef
  set E := GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F with hEdef
  have hEe : ∀ y, E y = e y := fun _ => rfl
  haveI : (laminf.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map laminf e.toAddEquiv he he'
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, laminf.map e = c • (volume : Measure (InfinitePlace F → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : laminf.map e = 0 := by simpa using hc
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := laminf.map e)).open_pos Set.univ isOpen_univ
      Set.univ_nonempty (by simp [h0])
  have hme : MeasurableEmbedding e := E.measurableEmbedding
  have hint : ∀ f : (InfinitePlace F → ℝ) → ℂ, ∫ y, f (e y) ∂laminf = (c : ℝ) • ∫ u, f u := by
    intro f
    rw [← hme.integral_map (μ := laminf) f, hc, integral_smul_nnreal_measure]
    rfl
  have hintR : ∀ f : (InfinitePlace F → ℝ) → ℝ, ∫ y, f (e y) ∂laminf = (c : ℝ) * ∫ u, f u := by
    intro f
    rw [← hme.integral_map (μ := laminf) f, hc, integral_smul_nnreal_measure]
    rfl
  refine ⟨fun k y => g k (e y), fun k => ⟨(hg1 k).1.comp he, (hg1 k).2.1.comp_homeomorph E, fun y => (hg1 k).2.2.1 _, ?_⟩, ?_, fun k => ?_⟩
  · rw [hintR]
    have : (0 : ℝ) < c := by exact_mod_cast pos_iff_ne_zero.2 hc0
    exact mul_pos this (hg1 k).2.2.2
  · rw [Filter.tendsto_smallSets_iff]
    intro U hU
    have hV : E.symm ⁻¹' U ∈ nhds (0 : InfinitePlace F → ℝ) := by
      apply E.symm.continuous.continuousAt.preimage_mem_nhds
      have : E.symm 0 = 0 := e.symm.map_zero
      rwa [this]
    obtain ⟨ε, hε, hεV⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
    have hlim : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hlim.eventually (ge_mem_nhds hε)] with k hk y hy
    have h1 : e y ∈ tsupport (g k) := tsupport_comp_subset_preimage (g k) he hy
    have h3 : e y ∈ E.symm ⁻¹' U := hεV (Metric.closedBall_subset_closedBall hk (hg2 k h1))
    have h5 : E.symm (e y) = y := E.symm_apply_apply y
    rw [Set.mem_preimage, h5] at h3
    exact h3
  · have hfou : ∀ t, fouInf ψ laminf (fun y => g k (e y)) t = (c : ℝ) • ∫ x, (g k x : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * e t w) : ℝ) : ℂ)) := by
      intro t
      have h6 := hint (fun u => (g k u : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (u w * e t w) : ℝ) : ℂ)))
      rw [← h6, fouInf]
      simp only [hχ, map_mul, Pi.mul_apply]
    have hG : Integrable (fun t => ∫ x, (g k x : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * e t w) : ℝ) : ℂ))) laminf := by
      have h7 : Integrable (fun t : InfinitePlace F → ℝ => ∫ x, (g k x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ))) (laminf.map e) := by
        rw [hc]
        exact (hg3 k).smul_measure_nnreal
      exact hme.integrable_map_iff.1 h7
    rw [funext hfou]
    exact hG.smul (c : ℝ)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx
