import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UMeasEx
import Development.AutomorphicArithmetic.AdelicSL2.IsOpenEmbeddingProjection
import Development.AutomorphicArithmetic.AdelicSL2.ExistsHaarRestrictRangeSl2IdeleMapEqSmulProd
import Development.AutomorphicArithmetic.AdelicSL2.IsFundamentalDomainImageSl2DomainProdIdeles

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical
open scoped ENNReal NNReal

/- English proof (translation)
Introduce `M μ _ Φ hΦ h0`. Take `⟨U⟩` from `UpperTheory.ConvolutionTheory.RankTwoDescent.uMeasEx_of`. Use `haveI := M.haar`. Establish `hemb : MeasurableEmbedding pm` using `UpperTheory.isOpenEmbedding_projection.measurableEmbedding`. Use `set F : Set GG := pm '' (M.D ×ˢ Set.univ) with hFdef`.

Establish `hF : IsFundamentalDomain Ga F μ` using `UpperTheory.isFundamentalDomain_image_sl2Domain_prod_ideles M U μ`. Establish `hFm : MeasurableSet F` using `hemb.measurableSet_image.2 (M.meas.prod MeasurableSet.univ)`. Establish `hinv : ∀ (γ : Ga) (x : GG), Φ ((γ • x : GG) : GL (Fin 2) (A ℚ)) = Φ (x : GL (Fin 2) (A ℚ))`. Introduce `γ x`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r : GL (Fin 2) ℚ, ratGL ℚ 2 r = ((γ : GG) : GL (Fin 2) (A ℚ)) := by`.

Take `⟨r, hr⟩` from `γ.2`. Conclude with `⟨r, hr⟩`. Use `hΦ.left r (x : GL (Fin 2) (A ℚ))` as an intermediate fact. Rewrite `this` using `[hr]`. Conclude with `this`.

Set `Φq : GroundTheory.Automorphic.RightCosetSpace Ga → ℂ` to `fun y => Φ ((Quotient.out y : GG) : GL (Fin 2) (A ℚ))`. Establish `hq : ∀ x : GG, Φq (GroundTheory.Automorphic.RightCosetSpace.mk Ga x) = Φ (x : GL (Fin 2) (A ℚ))`. Introduce `x`. Establish `h : GroundTheory.Automorphic.RightCosetSpace.mk Ga (Quotient.out (GroundTheory.Automorphic.RightCosetSpace.mk Ga x)) = GroundTheory.Automorphic.RightCosetSpace.mk Ga x` using `Quotient.out_eq _`. Take `⟨γ, hγ⟩` from `GroundTheory.Automorphic.RightCosetSpace.mk_eq_mk_iff.1 h`.

Express the relevant statement in the definitionally equal form `Φ ((Quotient.out (GroundTheory.Automorphic.RightCosetSpace.mk Ga x) : GG) : GL (Fin 2) (A ℚ)) = _`. Rewrite using `[← hγ, hinv]`. Establish `hqc : Continuous Φq`. Use `(GroundTheory.Automorphic.RightCosetSpace.isOpenQuotientMap_mk (Γ := Ga)).isQuotientMap.continuous_iff.2 ?_` and prove the remaining obligations. Establish `: Φq ∘ GroundTheory.Automorphic.RightCosetSpace.mk Ga = fun x : GG => Φ (x : GL (Fin 2) (A ℚ))` using `funext hq`.

Rewrite using `[this]`. Conclude with `hΦ.cont.comp continuous_subtype_val`. Express the relevant statement in the definitionally equal form `∫ y, Φq y ∂(GroundTheory.Automorphic.RightCosetSpace.quotientMeasure Ga μ) = 0`. Rewrite using `[← GroundTheory.Automorphic.RightCosetSpace.map_restrict_eq_quotientMeasure μ hF, integral_map (GroundTheory.Automorphic.RightCosetSpace.measurable_mk Ga).aemeasurable hqc.aestronglyMeasurable]`. Simplify using `only [hq]`.

Take `⟨c, hc⟩` from `UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod M U μ`. Establish `hFR : F ⊆ Set.range pm` using `Set.image_subset_range _ _`. Establish `hres : μ.restrict F = (c • (M.μ.prod (us U)).map pm).restrict F`. Rewrite using `[← hc, Measure.restrict_restrict hFm, Set.inter_eq_self_of_subset_left hFR]`. Rewrite using `[hres, Measure.restrict_smul, integral_smul_nnreal_measure, hemb.setIntegral_map]`.

Establish `hpre : pm ⁻¹' F = M.D ×ˢ Set.univ` using `hemb.injective.preimage_image _`. Establish `hr : (M.μ.prod (us U)).restrict (M.D ×ˢ Set.univ) = (M.μ.restrict M.D).prod (us U)`. Rewrite using `[← Measure.prod_restrict, Measure.restrict_univ]`. Rewrite using `[hpre, hr]`. Distinguish the cases in `hi : Integrable (fun x : G1 ℚ × US => Φ (pm x : GL (Fin 2) (A ℚ))) ((M.μ.restrict M.D).prod (us U))`.

Rewrite using `[integral_prod_symm _ hi]`. Establish `: ∀ t : US, ∫ g in M.D, Φ (pm (g, t) : GL (Fin 2) (A ℚ)) ∂M.μ = 0` using `fun t => h0 t t.2`. Simplify using `[this]`. Rewrite using `[integral_undef hi, smul_zero]`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.fibre :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fibre := by
  intro M μ _ Φ hΦ h0
  obtain ⟨U⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.uMeasEx_of
  haveI := M.haar
  have hemb : MeasurableEmbedding pm := UpperTheory.isOpenEmbedding_projection.measurableEmbedding
  set F : Set GG := pm '' (M.D ×ˢ Set.univ) with hFdef
  have hF : IsFundamentalDomain Ga F μ := UpperTheory.isFundamentalDomain_image_sl2Domain_prod_ideles M U μ
  have hFm : MeasurableSet F := hemb.measurableSet_image.2 (M.meas.prod MeasurableSet.univ)
  have hinv : ∀ (γ : Ga) (x : GG), Φ ((γ • x : GG) : GL (Fin 2) (A ℚ)) = Φ (x : GL (Fin 2) (A ℚ)) := by
    intro γ x
    obtain ⟨r, hr⟩ : ∃ r : GL (Fin 2) ℚ, ratGL ℚ 2 r = ((γ : GG) : GL (Fin 2) (A ℚ)) := by
      obtain ⟨r, hr⟩ := γ.2
      exact ⟨r, hr⟩
    have := hΦ.left r (x : GL (Fin 2) (A ℚ))
    rw [hr] at this
    exact this
  let Φq : GroundTheory.Automorphic.RightCosetSpace Ga → ℂ := fun y => Φ ((Quotient.out y : GG) : GL (Fin 2) (A ℚ))
  have hq : ∀ x : GG, Φq (GroundTheory.Automorphic.RightCosetSpace.mk Ga x) = Φ (x : GL (Fin 2) (A ℚ)) := by
    intro x
    have h : GroundTheory.Automorphic.RightCosetSpace.mk Ga (Quotient.out (GroundTheory.Automorphic.RightCosetSpace.mk Ga x)) =
        GroundTheory.Automorphic.RightCosetSpace.mk Ga x := Quotient.out_eq _
    obtain ⟨γ, hγ⟩ := GroundTheory.Automorphic.RightCosetSpace.mk_eq_mk_iff.1 h
    change Φ ((Quotient.out (GroundTheory.Automorphic.RightCosetSpace.mk Ga x) : GG) : GL (Fin 2) (A ℚ)) = _
    rw [← hγ, hinv]
  have hqc : Continuous Φq := by
    refine (GroundTheory.Automorphic.RightCosetSpace.isOpenQuotientMap_mk (Γ := Ga)).isQuotientMap.continuous_iff.2 ?_
    have : Φq ∘ GroundTheory.Automorphic.RightCosetSpace.mk Ga = fun x : GG => Φ (x : GL (Fin 2) (A ℚ)) := funext hq
    rw [this]
    exact hΦ.cont.comp continuous_subtype_val
  change ∫ y, Φq y ∂(GroundTheory.Automorphic.RightCosetSpace.quotientMeasure Ga μ) = 0
  rw [← GroundTheory.Automorphic.RightCosetSpace.map_restrict_eq_quotientMeasure μ hF,
    integral_map (GroundTheory.Automorphic.RightCosetSpace.measurable_mk Ga).aemeasurable hqc.aestronglyMeasurable]
  simp only [hq]
  obtain ⟨c, hc⟩ := UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod M U μ
  have hFR : F ⊆ Set.range pm := Set.image_subset_range _ _
  have hres : μ.restrict F = (c • (M.μ.prod (us U)).map pm).restrict F := by
    rw [← hc, Measure.restrict_restrict hFm, Set.inter_eq_self_of_subset_left hFR]
  rw [hres, Measure.restrict_smul, integral_smul_nnreal_measure, hemb.setIntegral_map]
  have hpre : pm ⁻¹' F = M.D ×ˢ Set.univ := hemb.injective.preimage_image _
  have hr : (M.μ.prod (us U)).restrict (M.D ×ˢ Set.univ) = (M.μ.restrict M.D).prod (us U) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hpre, hr]
  by_cases hi : Integrable (fun x : G1 ℚ × US => Φ (pm x : GL (Fin 2) (A ℚ))) ((M.μ.restrict M.D).prod (us U))
  · rw [integral_prod_symm _ hi]
    have : ∀ t : US, ∫ g in M.D, Φ (pm (g, t) : GL (Fin 2) (A ℚ)) ∂M.μ = 0 := fun t => h0 t t.2
    simp [this]
  · rw [integral_undef hi, smul_zero]
