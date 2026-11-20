import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.LeviCoordinates in

/- English proof (translation)
Introduce `D X u hK Dt Fs hD hin hFs T hPI f φ hf hφf`. Use `X.B.sf` as an intermediate fact. Use `X.B.haar` as an intermediate fact. Use `Formalism.L2.SG.Pf.gf_secondCountable X.B.I` as an intermediate fact. Use `Formalism.L2.SG.Pf.muf_right X` as an intermediate fact.

Use `rr_muA_sigmaFinite X.B.I X.B.μf` as an intermediate fact. Use `rr_muA_left X.B.I X.B.μf` as an intermediate fact. Use `rr_muA_right X.B.I X.B.μf` as an intermediate fact. Establish `hPP` using `Formalism.L2.SG.PoincareInHH.Cut.phProps_closed X u hK (Formalism.L2.SG.Pf.ksetSplit_holds X u) (Formalism.L2.SG.Pf.unipotent_in_level X u) (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u)`. Establish `hFD` using `rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec`.

Establish `hS : Srat X u ≤ rr_GF X.B.I` using `inf_le_left`. Establish `hDc : Dt.Countable` using `(Set.countable_coe_iff.1 (inferInstance : Countable (rr_GF X.B.I))).mono hD.1`. Use `hDc.to_subtype` as an intermediate fact. Establish `hSc : Countable (Srat X u)` using `Function.Injective.countable (Subgroup.inclusion_injective hS)`. Establish `hSinv : SMulInvariantMeasure (Srat X u) X.B.I.GA (X.B.I.muA X.B.μf)` using `⟨fun s A _ => by show (X.B.I.muA X.B.μf) ((fun y => (s : X.B.I.GA) * y) ⁻¹' A) = (X.B.I.muA X.B.μf) A`.

Conclude with `measure_preimage_mul _ (s : X.B.I.GA) A⟩`. Establish `hPm : Measurable (Ph X u hK T)` using `(hPP T).1`. Establish `hPinv : ∀ s ∈ Srat X u, ∀ y, Ph X u hK T (s * y) = Ph X u hK T y` using `(hPP T).2.1`. Establish `hfm : Measurable f` using `hf.cont.measurable`. Take `⟨C, hC⟩` from `hf.bdd`.

Establish `hfinv : ∀ γ ∈ rr_GF X.B.I, ∀ y, f (γ * y) = f y` using `fun γ hγ y => hf.left γ hγ y`. Establish `hginv : ∀ (s : Srat X u) (x : X.B.I.GA), (fun x => f x * Ph X u hK T x) ((s : X.B.I.GA) * x) = (fun x => f x * Ph X u hK T x) x`. Introduce `s x`. Use `show f (s * x) * Ph X u hK T (s * x) = f x * Ph X u hK T x`. Rewrite using `[hfinv s (hS s.2) x, hPinv s s.2 x]`.

Establish `hF' : IsFundamentalDomain (Srat X u) (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund) (X.B.I.muA X.B.μf)` using `rr_isFD (Formalism.L2.SG.Pf.InHHLeaf.rr_FD_union hFD (Srat X u) hS Dt hD hDc)`. Establish `hgFs : IntegrableOn (fun x => f x * Ph X u hK T x) Fs (X.B.I.muA X.B.μf)` using `Integrable.bdd_mul (c := C) hPI hfm.aestronglyMeasurable (Filter.Eventually.of_forall hC)`. Establish `hgFs'` using `(hFs.integrableOn_iff hF' hginv).1 hgFs`. Establish `e1 : ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) = ∫ x in (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund), f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf)` using `hFs.setIntegral_eq hF' (f := fun x => f x * Ph X u hK T x) hginv`. Establish `hU : (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund) = ⋃ δ : Dt, (fun y => (δ : X.B.I.GA) * y) '' X.B.fund`.

Rewrite using `[Set.biUnion_eq_iUnion]`. Establish `hmeas : ∀ δ : Dt, MeasurableSet ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund)`. Introduce `δ`. Rewrite using `[Formalism.L2.SG.Pf.InHHLeaf.img_mul]`. Conclude with `hFD.meas.preimage (measurable_const_mul _)`.

Establish `hdisj : Pairwise (Function.onFun (AEDisjoint (X.B.I.muA X.B.μf)) fun δ : Dt => (fun y => (δ : X.B.I.GA) * y) '' X.B.fund)`. Introduce `δ δ' hne`. Use `show X.B.I.muA X.B.μf (((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) ∩ ((fun y => (δ' : X.B.I.GA) * y) '' X.B.fund)) = 0`. Establish `hsub : ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) ∩ ((fun y => (δ' : X.B.I.GA) * y) '' X.B.fund) ⊆ (fun y => (δ' : X.B.I.GA) * y) '' ((fun y => ((δ' : X.B.I.GA)⁻¹ * δ) * y) '' X.B.fund ∩ X.B.fund)`. Introduce and unpack `_ ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx⟩⟩`.

Simplify using `only at hxx`. Use `⟨x', ⟨⟨x, hx, ?_⟩, hx'⟩, hxx⟩` and prove the remaining obligations. Use `show (δ' : X.B.I.GA)⁻¹ * δ * x = x'`. Rewrite using `[show x' = (δ' : X.B.I.GA)⁻¹ * ((δ' : X.B.I.GA) * x') by group, hxx]; group`. Use `measure_mono_null hsub ?_` and prove the remaining obligations.

Establish `hγ : (δ' : X.B.I.GA)⁻¹ * δ ∈ rr_GF X.B.I` using `(rr_GF X.B.I).mul_mem ((rr_GF X.B.I).inv_mem (hD.1 δ'.2)) (hD.1 δ.2)`. Establish `hne' : (δ' : X.B.I.GA)⁻¹ * δ ≠ 1`. Introduce `h1`. Apply `hne` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← mul_one (δ' : X.B.I.GA), ← h1]`. Use `group`. Rewrite using `[Formalism.L2.SG.Pf.InHHLeaf.img_mul, measure_preimage_mul]`. Conclude with `hFD.disj _ hγ hne'`. Establish `e2 : ∫ x in (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund), f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) = ∑' δ : Dt, ∫ x in (fun y => (δ : X.B.I.GA) * y) '' X.B.fund, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf)`.

Rewrite `hgFs'`, the goal using `[hU]`. Conclude with `integral_iUnion_ae (fun δ => (hmeas δ).nullMeasurableSet) hdisj hgFs'`. Establish `e3 : ∀ δ : Dt, ∫ x in (fun y => (δ : X.B.I.GA) * y) '' X.B.fund, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) = ∫ y in X.B.fund, f y * Ph X u hK T ((δ : X.B.I.GA) * y) ∂(X.B.I.muA X.B.μf)`. Introduce `δ`. Establish `hpre : (fun y => (δ : X.B.I.GA) * y) ⁻¹' ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) = X.B.fund` using `Set.preimage_image_eq _ (mul_right_injective (δ : X.B.I.GA))`.

Establish `h2` using `(measurePreserving_mul_left (X.B.I.muA X.B.μf) (δ : X.B.I.GA)).setIntegral_preimage_emb (measurableEmbedding_mulLeft (δ : X.B.I.GA)) (fun x => f x * Ph X u hK T x) ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund)`. Rewrite `h2` using `[hpre]`. Rewrite using `[← h2]`. Use `setIntegral_congr_fun hFD.meas fun y _ => ?_` and prove the remaining obligations. Use `show f ((δ : X.B.I.GA) * y) * Ph X u hK T ((δ : X.B.I.GA) * y) = f y * Ph X u hK T ((δ : X.B.I.GA) * y)`.

Rewrite using `[hfinv _ (hD.1 δ.2) y]`. Establish `hbound : ∑' δ : Dt, ∫⁻ y in X.B.fund, ‖f y * Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) ≠ ⊤`. Establish `hle : ∀ δ : Dt, ∫⁻ y in X.B.fund, ‖f y * Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) ≤ ENNReal.ofReal C * ∫⁻ y in X.B.fund, ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf)`. Introduce `δ`. Rewrite using `[← lintegral_const_mul (f := fun y => ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ) _ (hPm.comp (measurable_const_mul _)).enorm]`.

Use `lintegral_mono fun y => ?_` and prove the remaining obligations. Rewrite using `[enorm_mul]`. Use `mul_le_mul' ?_ le_rfl` and prove the remaining obligations. Rewrite using `[← ofReal_norm_eq_enorm]`. Conclude with `ENNReal.ofReal_le_ofReal (hC y)`.

Use `ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_mul_left, ← lintegral_tsum (f := fun (δ : Dt) y => ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ) (fun δ => (hPm.comp (measurable_const_mul _)).enorm.aemeasurable), Formalism.L2.SG.Pf.InHHLeaf.unfold_lint hFD (Srat X u) hS Dt hD Fs hFs (fun w => ‖Ph X u hK T w‖ₑ) hPm.enorm (f …`. Conclude with `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPI.2.ne`. Establish `e4 : ∫ y in X.B.fund, f y * Pser X u hK Dt T y ∂(X.B.I.muA X.B.μf) = ∑' δ : Dt, ∫ y in X.B.fund, f y * Ph X u hK T ((δ : X.B.I.GA) * y) ∂(X.B.I.muA X.B.μf)`. Establish `hfun : (fun y => f y * Pser X u hK Dt T y) = fun y => ∑' δ : Dt, f y * Ph X u hK T ((δ : X.B.I.GA) * y)`.

Use function extensionality and compare the values at `y`. Use `show f y * ∑' δ : Dt, Ph X u hK T ((δ : X.B.I.GA) * y) = _`. Rewrite using `[tsum_mul_left]`. Rewrite using `[hfun]`. Conclude with `integral_tsum (fun δ => (hfm.mul (hPm.comp (measurable_const_mul _))).aestronglyMeasurable) hbound`.

Establish `hm` using `(hin T Dt hD).2.2.1`. Establish `eL : ⟪star φ, PuFun X u hK Dt T⟫_ℂ = ∫ y in X.B.fund, f y * Pser X u hK Dt T y ∂(X.B.I.muA X.B.μf)`. Establish `e0 : PuFun X u hK Dt T = hm.toLp (Pser X u hK Dt T)` using `dif_pos hm`. Rewrite using `[e0, MeasureTheory.L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [Lp.coeFn_star φ, hm.coeFn_toLp, hφf] with a h1 h2 h3`. Rewrite using `[h1, h2, Pi.star_apply, h3, RCLike.inner_apply]`. Rewrite using `[mul_comm]`. Use `congr 1`. Use `first`.

Consider the case `exact Complex.conj_conj (f a)`. Consider the case `simp [Complex.star_def]`. Rewrite using `[eL, e4, e1, e2]`. Conclude with `tsum_congr fun δ => (e3 δ).symm`.
-/
theorem GlobalTheory.Core.Mi.inner_pser_eq_setIntegral : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (Dt Fs : Set X.B.I.GA), IsReps X u Dt → InHH X u hK → IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∀ T : Cu X u hK, IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) → ∀ (f : X.B.I.GA → ℂ) (φ : L2X X), RowFun X f → (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f → ⟪star φ, PuFun X u hK Dt T⟫_ℂ = ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) := by
  intro D X u hK Dt Fs hD hin hFs T hPI f φ hf hφf
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  have := Formalism.L2.SG.Pf.muf_right X
  have := rr_muA_sigmaFinite X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have := rr_muA_right X.B.I X.B.μf
  have hPP := Formalism.L2.SG.PoincareInHH.Cut.phProps_closed X u hK (Formalism.L2.SG.Pf.ksetSplit_holds X u)
    (Formalism.L2.SG.Pf.unipotent_in_level X u) (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u)
  have hFD := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have hS : Srat X u ≤ rr_GF X.B.I := inf_le_left
  have hDc : Dt.Countable :=
    (Set.countable_coe_iff.1 (inferInstance : Countable (rr_GF X.B.I))).mono hD.1
  have := hDc.to_subtype
  have hSc : Countable (Srat X u) := Function.Injective.countable (Subgroup.inclusion_injective hS)
  have hSinv : SMulInvariantMeasure (Srat X u) X.B.I.GA (X.B.I.muA X.B.μf) := ⟨fun s A _ => by
      show (X.B.I.muA X.B.μf) ((fun y => (s : X.B.I.GA) * y) ⁻¹' A) = (X.B.I.muA X.B.μf) A
      exact measure_preimage_mul _ (s : X.B.I.GA) A⟩
  have hPm : Measurable (Ph X u hK T) := (hPP T).1
  have hPinv : ∀ s ∈ Srat X u, ∀ y, Ph X u hK T (s * y) = Ph X u hK T y := (hPP T).2.1
  have hfm : Measurable f := hf.cont.measurable
  obtain ⟨C, hC⟩ := hf.bdd
  have hfinv : ∀ γ ∈ rr_GF X.B.I, ∀ y, f (γ * y) = f y := fun γ hγ y => hf.left γ hγ y
  have hginv : ∀ (s : Srat X u) (x : X.B.I.GA),
      (fun x => f x * Ph X u hK T x) ((s : X.B.I.GA) * x) = (fun x => f x * Ph X u hK T x) x := by
    intro s x
    show f (s * x) * Ph X u hK T (s * x) = f x * Ph X u hK T x
    rw [hfinv s (hS s.2) x, hPinv s s.2 x]
  have hF' : IsFundamentalDomain (Srat X u) (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund) (X.B.I.muA X.B.μf) :=
    rr_isFD (Formalism.L2.SG.Pf.InHHLeaf.rr_FD_union hFD (Srat X u) hS Dt hD hDc)
  have hgFs : IntegrableOn (fun x => f x * Ph X u hK T x) Fs (X.B.I.muA X.B.μf) :=
    Integrable.bdd_mul (c := C) hPI hfm.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hgFs' := (hFs.integrableOn_iff hF' hginv).1 hgFs
  have e1 : ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∫ x in (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund), f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) :=
    hFs.setIntegral_eq hF' (f := fun x => f x * Ph X u hK T x) hginv
  have hU : (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund) = ⋃ δ : Dt, (fun y => (δ : X.B.I.GA) * y) '' X.B.fund := by
    rw [Set.biUnion_eq_iUnion]
  have hmeas : ∀ δ : Dt, MeasurableSet ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) := by
    intro δ; rw [Formalism.L2.SG.Pf.InHHLeaf.img_mul]; exact hFD.meas.preimage (measurable_const_mul _)
  have hdisj : Pairwise (Function.onFun (AEDisjoint (X.B.I.muA X.B.μf))
      fun δ : Dt => (fun y => (δ : X.B.I.GA) * y) '' X.B.fund) := by
    intro δ δ' hne
    show X.B.I.muA X.B.μf (((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) ∩ ((fun y => (δ' : X.B.I.GA) * y) '' X.B.fund)) = 0
    have hsub : ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) ∩ ((fun y => (δ' : X.B.I.GA) * y) '' X.B.fund) ⊆
        (fun y => (δ' : X.B.I.GA) * y) '' ((fun y => ((δ' : X.B.I.GA)⁻¹ * δ) * y) '' X.B.fund ∩ X.B.fund) := by
      rintro _ ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx⟩⟩
      simp only at hxx
      refine ⟨x', ⟨⟨x, hx, ?_⟩, hx'⟩, hxx⟩
      show (δ' : X.B.I.GA)⁻¹ * δ * x = x'
      rw [show x' = (δ' : X.B.I.GA)⁻¹ * ((δ' : X.B.I.GA) * x') by group, hxx]; group
    refine measure_mono_null hsub ?_
    have hγ : (δ' : X.B.I.GA)⁻¹ * δ ∈ rr_GF X.B.I := (rr_GF X.B.I).mul_mem ((rr_GF X.B.I).inv_mem (hD.1 δ'.2)) (hD.1 δ.2)
    have hne' : (δ' : X.B.I.GA)⁻¹ * δ ≠ 1 := by
      intro h1
      apply hne
      apply Subtype.ext
      rw [← mul_one (δ' : X.B.I.GA), ← h1]; group
    rw [Formalism.L2.SG.Pf.InHHLeaf.img_mul, measure_preimage_mul]
    exact hFD.disj _ hγ hne'
  have e2 : ∫ x in (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund), f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∑' δ : Dt, ∫ x in (fun y => (δ : X.B.I.GA) * y) '' X.B.fund, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) := by
    rw [hU] at hgFs' ⊢
    exact integral_iUnion_ae (fun δ => (hmeas δ).nullMeasurableSet) hdisj hgFs'
  have e3 : ∀ δ : Dt, ∫ x in (fun y => (δ : X.B.I.GA) * y) '' X.B.fund, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∫ y in X.B.fund, f y * Ph X u hK T ((δ : X.B.I.GA) * y) ∂(X.B.I.muA X.B.μf) := by
    intro δ
    have hpre : (fun y => (δ : X.B.I.GA) * y) ⁻¹' ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) = X.B.fund :=
      Set.preimage_image_eq _ (mul_right_injective (δ : X.B.I.GA))
    have h2 := (measurePreserving_mul_left (X.B.I.muA X.B.μf) (δ : X.B.I.GA)).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft (δ : X.B.I.GA)) (fun x => f x * Ph X u hK T x)
      ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund)
    rw [hpre] at h2
    rw [← h2]
    refine setIntegral_congr_fun hFD.meas fun y _ => ?_
    show f ((δ : X.B.I.GA) * y) * Ph X u hK T ((δ : X.B.I.GA) * y) = f y * Ph X u hK T ((δ : X.B.I.GA) * y)
    rw [hfinv _ (hD.1 δ.2) y]
  have hbound : ∑' δ : Dt, ∫⁻ y in X.B.fund, ‖f y * Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) ≠ ⊤ := by
    have hle : ∀ δ : Dt, ∫⁻ y in X.B.fund, ‖f y * Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) ≤
        ENNReal.ofReal C * ∫⁻ y in X.B.fund, ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) := by
      intro δ
      rw [← lintegral_const_mul (f := fun y => ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ) _ (hPm.comp (measurable_const_mul _)).enorm]
      refine lintegral_mono fun y => ?_
      rw [enorm_mul]
      refine mul_le_mul' ?_ le_rfl
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC y)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_mul_left, ← lintegral_tsum (f := fun (δ : Dt) y => ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ) (fun δ => (hPm.comp (measurable_const_mul _)).enorm.aemeasurable),
      Formalism.L2.SG.Pf.InHHLeaf.unfold_lint hFD (Srat X u) hS Dt hD Fs hFs (fun w => ‖Ph X u hK T w‖ₑ) hPm.enorm
        (fun s hs y => by simp only [hPinv s hs y])]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPI.2.ne
  have e4 : ∫ y in X.B.fund, f y * Pser X u hK Dt T y ∂(X.B.I.muA X.B.μf) =
      ∑' δ : Dt, ∫ y in X.B.fund, f y * Ph X u hK T ((δ : X.B.I.GA) * y) ∂(X.B.I.muA X.B.μf) := by
    have hfun : (fun y => f y * Pser X u hK Dt T y) = fun y => ∑' δ : Dt, f y * Ph X u hK T ((δ : X.B.I.GA) * y) := by
      funext y
      show f y * ∑' δ : Dt, Ph X u hK T ((δ : X.B.I.GA) * y) = _
      rw [tsum_mul_left]
    rw [hfun]
    exact integral_tsum (fun δ => (hfm.mul (hPm.comp (measurable_const_mul _))).aestronglyMeasurable) hbound
  have hm := (hin T Dt hD).2.2.1
  have eL : ⟪star φ, PuFun X u hK Dt T⟫_ℂ = ∫ y in X.B.fund, f y * Pser X u hK Dt T y ∂(X.B.I.muA X.B.μf) := by
    have e0 : PuFun X u hK Dt T = hm.toLp (Pser X u hK Dt T) := dif_pos hm
    rw [e0, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_star φ, hm.coeFn_toLp, hφf] with a h1 h2 h3
    rw [h1, h2, Pi.star_apply, h3, RCLike.inner_apply]
    rw [mul_comm]
    congr 1
    first
      | exact Complex.conj_conj (f a)
      | simp [Complex.star_def]
  rw [eL, e4, e1, e2]
  exact tsum_congr fun δ => (e3 δ).symm
