import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

open Formalism.FourierDecayAlt.ThreeDimData

/- English proof (translation)
Introduce `hSch hNI hGS hGG hDD hBC hInp _ k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS W hWc hWeq hRe hpos hfin`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩` from `hS`. Establish `hS' : Side k r ε lam h σ w0 z c u π μW μN μG νq` using `⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩`.

Use `hWh.1` as an intermediate fact. Use `hNh.1` as an intermediate fact. Use `hGh.1` as an intermediate fact. Establish `hsm` using `DDSmoothness.DD_smooth hInp.2.2.1 hlam hσ hw0`. Establish `memDD : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ DDsp σ w0` using `fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩`.

Establish `hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r))` using `continuous_id`. Establish `hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `ae_iff.mpr hGh.2.2.1`. Establish `hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z` using `ae_iff.mpr hWh.2.2.1`. Establish `hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r` using `ae_iff.mpr hNh.2.2.1`. Establish `hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r` using `(Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)`.

Take `⟨hS0, hSc⟩` from `DDSmoothness.muSof_facts hWh hNh`. Establish `hνae` using `DDSmoothness.ae_UH_of_quot hGh.2.2.1 hS0 hSc hq`. Establish `hBC'` using `hBC hInp k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS'`. Establish `hcs` using `Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w0`. Establish `hW0 : ∀ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x0 = 0`.

Introduce `x0 hx0`. Take `⟨hI, hR⟩` from `hRe x0 hx0`. Rewrite using `[← hR]`. Unfold `PI.BesselPeriodGGP.rconv`. Apply `ext_inner_left ℂ` to reduce the goal to its premises.

Introduce `η`. Rewrite using `[inner_zero_right, ← integral_inner hI η]`. Take `⟨hxi, hxx, hxx'⟩` from `uh_inv hx0`. Use `set U : Set (Formalism.QuantumDeterminants.Mt k r) := {g | Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU`. Establish `hUm : MeasurableSet U` using `(isClosed_UH.preimage hof).measurableSet`.

Set `Φ : Formalism.QuantumDeterminants.Mt k r → ℂ` to `fun g => ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g) • W (Matrix.of g)⟫_ℂ`. Set `Φ' : Formalism.QuantumDeterminants.Mt k r → ℂ` to `U.piecewise Φ (fun _ => 0)`. Establish `hΦc : ContinuousOn Φ U`. Establish `hm : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U` using `(continuous_const.matrix_mul hof).continuousOn`. Establish `hmaps : Set.MapsTo (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))` using `fun g hg => DDSmoothness.uh_mul hxi hg`.

Establish `he : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g)) U`. Unfold `PI.BesselPeriodGGP.eFun`. Conclude with `continuousOn_const.mul (continuous_star.comp_continuousOn (continuousOn_const.inner (hcs.comp hm hmaps)))`. Establish `hWc' : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of g)) U` using `hWc.comp hof.continuousOn (fun g hg => hg)`. Conclude with `continuousOn_const.inner (he.smul hWc')`.

Establish `hΦm : Measurable Φ'` using `hΦc.measurable_piecewise continuousOn_const hUm`. Establish `hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k` using `k) (r := r) x0) := by`. Establish `: Continuous (Formalism.QuantumDeterminants.lmulM (k` using `k) (r := r) x0) := continuous_const.matrix_mul hof`. Conclude with `this.measurable`. Establish `htrans : (fun g : Formalism.QuantumDeterminants.Mt k r => ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) =ᵐ[μG] Φ' ∘ Formalism.QuantumDeterminants.lmulM x0` using `by filter_upwards [hGae] with g hg`.

Establish `hxg : x0 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `DDSmoothness.uh_mul hx0 hg`. Establish `hmem : Formalism.QuantumDeterminants.lmulM x0 g ∈ U` using `hxg`. Simplify using `only [Function.comp, Φ', Set.piecewise, hmem, if_true, Φ]`. Use `show _ = ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (x0 * Matrix.of g)) • W (x0 * Matrix.of g)⟫_ℂ`. Rewrite using `[← Matrix.mul_assoc, hxx', Matrix.one_mul]`.

Establish `hmapEq : μG.map (Formalism.QuantumDeterminants.lmulM x0) = μG` using `hGh.2.2.2 x0 hx0`. Establish `hΦint : Integrable Φ' μG`. Establish `h1 : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) μG` using `(innerSL ℂ η).integrable_comp hI`. Establish `h2 : Integrable (Φ' ∘ Formalism.QuantumDeterminants.lmulM x0) μG` using `h1.congr htrans`. Rewrite `h2` using `[← integrable_map_measure hΦm.aestronglyMeasurable hlm.aemeasurable, hmapEq]`.

Conclude with `h2`. Rewrite using `[integral_congr_ae htrans]`. Use `show ∫ a, Φ' (Formalism.QuantumDeterminants.lmulM x0 a) ∂μG = 0`. Rewrite using `[← integral_map hlm.aemeasurable hΦm.aestronglyMeasurable, hmapEq]`. Establish `: SFinite (muSof μW μN)` using `by unfold muSof; infer_instance`.

Use `quot_zero hq Φ' hΦm hΦint ?_` and prove the remaining obligations. Use `filter_upwards [hνae] with x hx`. Establish `hpm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))`. Establish `h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r))` using `continuous_fst`. Establish `h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r))` using `continuous_snd`.

Establish `h3 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))` using `h1.matrix_mul h2`. Conclude with `h3.measurable`. Establish `hFm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => Φ' (mulMt s x))` using `hΦm.comp (measurable_mulMt.comp (measurable_id.prodMk measurable_const))`. Unfold `muSof`. Rewrite using `[integral_map hpm.aemeasurable hFm.aestronglyMeasurable]`.

Use `set u' := σ (Matrix.of x) w0 with hu'`. Use `set v' := σ x0 w0 with hv'`. Establish `hu'DD : u' ∈ DDsp σ w0` using `memDD _ hx`. Establish `hv'DD : v' ∈ DDsp σ w0` using `memDD _ hx0`. Establish `hI2 : Integrable (beInt z c π σ u' v') (μW.prod μN)` using `hBC'.1 u' (hsm _ hu'DD) v' (Or.inl hv'DD)`.

Establish `hval : ∀ᵐ p ∂(μW.prod μN), Φ' (mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) = ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℝ) : ℂ) * ⟪beInt z c π σ u' v' p η, W (Matrix.of x)⟫_ℂ` using `by filter_upwards [hPae] with p hp`. Establish `hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `DDSmoothness.uh_mul hp.1.1 hp.2.1`. Establish `hsx : Matrix.of p.1 * Matrix.of p.2 * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `DDSmoothness.uh_mul hs hx`. Establish `hmem : mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x ∈ U` using `hsx`. Simplify using `only [Φ', Set.piecewise, hmem, if_true, Φ]`.

Use `show ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) • W (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)⟫_ℂ = _`. Rewrite using `[hWeq _ hp.1 _ hp.2 _ hx]`. Establish `hdet : IsUnit x0.det` using `Matrix.isUnit_det_of_right_inverse hxx`. Establish `eσ : σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0 = σ x0⁻¹ (σ (Matrix.of p.1 * Matrix.of p.2) u')`. Rewrite using `[Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hxi hsx, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hs hx]`.

Both sides reduce to the same expression. Establish `eA : ⟪w0, σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0⟫_ℂ = ⟪v', σ (Matrix.of p.1 * Matrix.of p.2) u'⟫_ℂ`. Rewrite using `[eσ, sigma_inner hσ hxi, Matrix.nonsing_inv_nonsing_inv x0 hdet]`. Unfold `PI.BesselPeriodGGP.eFun beInt`. Rewrite using `[eA, inner_smul_right, inner_smul_right, piW_inner hT hπ hp.1, ContinuousLinearMap.smul_apply, inner_smul_left]`.

Simplify using `only [map_mul, Complex.star_def, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[integral_congr_ae hval, integral_const_mul]`. Establish `hf : Integrable (fun p => beInt z c π σ u' v' p η) (μW.prod μN)` using `(ContinuousLinearMap.apply ℂ Wp η).integrable_comp hI2`. Establish `hinner : ∫ p, ⟪beInt z c π σ u' v' p η, W (Matrix.of x)⟫_ℂ ∂(μW.prod μN) = ⟪be z c π σ μW μN u' v' η, W (Matrix.of x)⟫_ℂ`.

Establish `e2 : be z c π σ μW μN u' v' η = ∫ p, beInt z c π σ u' v' p η ∂(μW.prod μN)` using `ContinuousLinearMap.integral_apply hI2 η`. Rewrite using `[e2, ← inner_conj_symm, ← integral_inner hf (W (Matrix.of x)), ← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Rewrite using `[inner_conj_symm]`.

Rewrite using `[hinner, hcon u' hu'DD v' hv'DD]`. Simplify using the standard rewrite rules. Establish `hl0 : PI.BesselPeriodGGP.l2SG νq W = 0`. Unfold `PI.BesselPeriodGGP.l2SG`. Rewrite using `[lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]`.

Use `filter_upwards [hνae] with x hx`. Rewrite using `[hW0 _ hx]`. Simplify using the standard rewrite rules. Rewrite `hpos` using `[hl0]`. Conclude with `lt_irrefl _ hpos`.
-/
theorem bessel_nonvanishing_from_L2 : Formalism.FourierDecayAlt.ThreeDimData.More.BesselNonvanishingReduction := by
  classical
  intro hSch hNI hGS hGG hDD hBC hInp _ k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS W hWc hWeq
    hRe hpos hfin
  by_contra hcon
  push_neg at hcon
  obtain ⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩ := hS
  have hS' : Side k r ε lam h σ w0 z c u π μW μN μG νq :=
    ⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩
  have := hWh.1; have := hNh.1; have := hGh.1
  have hsm := DDSmoothness.DD_smooth hInp.2.2.1 hlam hσ hw0
  have memDD : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ DDsp σ w0 :=
    fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  obtain ⟨hS0, hSc⟩ := DDSmoothness.muSof_facts hWh hNh
  have hνae := DDSmoothness.ae_UH_of_quot hGh.2.2.1 hS0 hSc hq
  have hBC' := hBC hInp k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS'
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w0

  have hW0 : ∀ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x0 = 0 := by
    intro x0 hx0
    obtain ⟨hI, hR⟩ := hRe x0 hx0
    rw [← hR]
    unfold PI.BesselPeriodGGP.rconv
    apply ext_inner_left ℂ
    intro η
    rw [inner_zero_right, ← integral_inner hI η]
    obtain ⟨hxi, hxx, hxx'⟩ := uh_inv hx0
    set U : Set (Formalism.QuantumDeterminants.Mt k r) := {g | Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU
    have hUm : MeasurableSet U := (isClosed_UH.preimage hof).measurableSet
    let Φ : Formalism.QuantumDeterminants.Mt k r → ℂ := fun g =>
      ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g) • W (Matrix.of g)⟫_ℂ
    let Φ' : Formalism.QuantumDeterminants.Mt k r → ℂ := U.piecewise Φ (fun _ => 0)
    have hΦc : ContinuousOn Φ U := by
      have hm : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U :=
        (continuous_const.matrix_mul hof).continuousOn
      have hmaps : Set.MapsTo (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U
          (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := fun g hg => DDSmoothness.uh_mul hxi hg
      have he : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r =>
          PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g)) U := by
        unfold PI.BesselPeriodGGP.eFun
        exact continuousOn_const.mul (continuous_star.comp_continuousOn
          (continuousOn_const.inner (hcs.comp hm hmaps)))
      have hWc' : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of g)) U :=
        hWc.comp hof.continuousOn (fun g hg => hg)
      exact continuousOn_const.inner (he.smul hWc')
    have hΦm : Measurable Φ' := hΦc.measurable_piecewise continuousOn_const hUm
    have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x0) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x0) := continuous_const.matrix_mul hof
      exact this.measurable
    have htrans : (fun g : Formalism.QuantumDeterminants.Mt k r =>
        ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) =ᵐ[μG]
        Φ' ∘ Formalism.QuantumDeterminants.lmulM x0 := by
      filter_upwards [hGae] with g hg
      have hxg : x0 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hx0 hg
      have hmem : Formalism.QuantumDeterminants.lmulM x0 g ∈ U := hxg
      simp only [Function.comp, Φ', Set.piecewise, hmem, if_true, Φ]
      show _ = ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (x0 * Matrix.of g)) • W (x0 * Matrix.of g)⟫_ℂ
      rw [← Matrix.mul_assoc, hxx', Matrix.one_mul]
    have hmapEq : μG.map (Formalism.QuantumDeterminants.lmulM x0) = μG := hGh.2.2.2 x0 hx0
    have hΦint : Integrable Φ' μG := by
      have h1 : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
          ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) μG :=
        (innerSL ℂ η).integrable_comp hI
      have h2 : Integrable (Φ' ∘ Formalism.QuantumDeterminants.lmulM x0) μG := h1.congr htrans
      rw [← integrable_map_measure hΦm.aestronglyMeasurable hlm.aemeasurable, hmapEq] at h2
      exact h2
    rw [integral_congr_ae htrans]
    show ∫ a, Φ' (Formalism.QuantumDeterminants.lmulM x0 a) ∂μG = 0
    rw [← integral_map hlm.aemeasurable hΦm.aestronglyMeasurable, hmapEq]
    have : SFinite (muSof μW μN) := by unfold muSof; infer_instance
    refine quot_zero hq Φ' hΦm hΦint ?_
    filter_upwards [hνae] with x hx
    have hpm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
      have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
      have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
      have h3 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
          (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := h1.matrix_mul h2
      exact h3.measurable
    have hFm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => Φ' (mulMt s x)) :=
      hΦm.comp (measurable_mulMt.comp (measurable_id.prodMk measurable_const))
    unfold muSof
    rw [integral_map hpm.aemeasurable hFm.aestronglyMeasurable]
    set u' := σ (Matrix.of x) w0 with hu'
    set v' := σ x0 w0 with hv'
    have hu'DD : u' ∈ DDsp σ w0 := memDD _ hx
    have hv'DD : v' ∈ DDsp σ w0 := memDD _ hx0
    have hI2 : Integrable (beInt z c π σ u' v') (μW.prod μN) := hBC'.1 u' (hsm _ hu'DD) v' (Or.inl hv'DD)
    have hval : ∀ᵐ p ∂(μW.prod μN), Φ' (mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) =
        ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℝ) : ℂ) * ⟪beInt z c π σ u' v' p η, W (Matrix.of x)⟫_ℂ := by
      filter_upwards [hPae] with p hp
      have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
      have hsx : Matrix.of p.1 * Matrix.of p.2 * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
        DDSmoothness.uh_mul hs hx
      have hmem : mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x ∈ U := hsx
      simp only [Φ', Set.piecewise, hmem, if_true, Φ]
      show ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) •
          W (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)⟫_ℂ = _
      rw [hWeq _ hp.1 _ hp.2 _ hx]
      have hdet : IsUnit x0.det := Matrix.isUnit_det_of_right_inverse hxx
      have eσ : σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0 =
          σ x0⁻¹ (σ (Matrix.of p.1 * Matrix.of p.2) u') := by
        rw [Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hxi hsx, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hs hx]; rfl
      have eA : ⟪w0, σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0⟫_ℂ =
          ⟪v', σ (Matrix.of p.1 * Matrix.of p.2) u'⟫_ℂ := by
        rw [eσ, sigma_inner hσ hxi, Matrix.nonsing_inv_nonsing_inv x0 hdet]
      unfold PI.BesselPeriodGGP.eFun beInt
      rw [eA, inner_smul_right, inner_smul_right, piW_inner hT hπ hp.1, ContinuousLinearMap.smul_apply,
        inner_smul_left]
      simp only [map_mul, Complex.star_def, Complex.conj_conj]
      ring
    rw [integral_congr_ae hval, integral_const_mul]
    have hf : Integrable (fun p => beInt z c π σ u' v' p η) (μW.prod μN) :=
      (ContinuousLinearMap.apply ℂ Wp η).integrable_comp hI2
    have hinner : ∫ p, ⟪beInt z c π σ u' v' p η, W (Matrix.of x)⟫_ℂ ∂(μW.prod μN) =
        ⟪be z c π σ μW μN u' v' η, W (Matrix.of x)⟫_ℂ := by
      have e2 : be z c π σ μW μN u' v' η = ∫ p, beInt z c π σ u' v' p η ∂(μW.prod μN) :=
        ContinuousLinearMap.integral_apply hI2 η
      rw [e2, ← inner_conj_symm, ← integral_inner hf (W (Matrix.of x)), ← integral_conj]
      congr 1
      funext p
      rw [inner_conj_symm]
    rw [hinner, hcon u' hu'DD v' hv'DD]
    simp

  have hl0 : PI.BesselPeriodGGP.l2SG νq W = 0 := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hνae] with x hx
    rw [hW0 _ hx]; simp
  rw [hl0] at hpos
  exact lt_irrefl _ hpos

/- English proof (translation)
The claim follows from `bessel_nonvanishing_from_L2`.
-/
theorem bessel_nonzero_l2_reduction : Formalism.FourierDecayAlt.ThreeDimData.More.BesselNonvanishingReduction := bessel_nonvanishing_from_L2

end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
